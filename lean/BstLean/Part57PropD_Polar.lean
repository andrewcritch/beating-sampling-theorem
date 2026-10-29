import BstLean.Part57Defs
import BstLean.Part56PropD_Bingham
import BstLean.Part57Key

/-! Rank-r Gaussian coordinates for the Bingham polar decomposition. -/
namespace BstLean.Part57.PropD57
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part56 (basisCoordinates basisCoordinates_preserving basisReconstruct
  basisReconstruct_eq_symm basisReconstruct_sumsq basisReconstruct_add basisReconstruct_smul)
variable {n r k : ℕ}

/-- An orthonormal frame extends to an orthonormal basis whose first `r` vectors are the frame. -/
theorem frame_basis_exists (hrn : r ≤ n) (V : Fin r → Fin n → ℝ) (hV : OrthoF V) :
    ∃ b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      ∀ a : Fin r, b (Fin.castLE hrn a) = WithLp.toLp 2 (V a) := by
  classical
  let u : Fin n → EuclideanSpace ℝ (Fin n) := fun i =>
    if h : i.val < r then WithLp.toLp 2 (V ⟨i, h⟩) else 0
  let s : Set (Fin n) := {i | i.val < r}
  have ho : Orthonormal ℝ (s.restrict u) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : ((i : Fin n) : ℕ) < r := i.2
    have hj : ((j : Fin n) : ℕ) < r := j.2
    change inner ℝ (u i) (u j) = _
    have e1 : u i = WithLp.toLp 2 (V ⟨(i : Fin n), hi⟩) := dif_pos hi
    have e2 : u j = WithLp.toLp 2 (V ⟨(j : Fin n), hj⟩) := dif_pos hj
    rw [e1, e2]
    simp only [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct]
    have h := hV ⟨(i : Fin n), hi⟩ ⟨(j : Fin n), hj⟩
    rw [show (∑ x, V ⟨(j : Fin n), hj⟩ x * V ⟨(i : Fin n), hi⟩ x) =
      ∑ x, V ⟨(i : Fin n), hi⟩ x * V ⟨(j : Fin n), hj⟩ x from
        Finset.sum_congr rfl fun x _ => mul_comm _ _, h]
    by_cases hij : i = j
    · subst hij; simp
    · have : (⟨(i : Fin n), hi⟩ : Fin r) ≠ ⟨(j : Fin n), hj⟩ := by
        intro h'; apply hij; apply Subtype.ext; apply Fin.ext
        simpa using congrArg Fin.val h'
      simp [this, hij]
  obtain ⟨b, hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨b, fun a => ?_⟩
  have hmem : Fin.castLE hrn a ∈ s := by simp [s]
  rw [hb _ hmem]
  simp [u]

theorem coord_reconstruct (hrn : r ≤ n) (V : Fin r → Fin n → ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (hb : ∀ a : Fin r, b (Fin.castLE hrn a) = WithLp.toLp 2 (V a)) (z : Fin n → ℝ) (a : Fin r) :
    coordY V (basisReconstruct b z) a = z (Fin.castLE hrn a) := by
  have h := b.repr_apply_apply (b.repr.symm (WithLp.toLp 2 z)) (Fin.castLE hrn a)
  simp only [LinearIsometryEquiv.apply_symm_apply, hb] at h
  unfold coordY
  symm
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
    basisReconstruct, mul_comm] using h

theorem sum_castLE (hrn : r ≤ n) (f : Fin n → ℝ) :
    ∑ a : Fin r, f (Fin.castLE hrn a) = ∑ i, if i.val < r then f i else 0 := by
  classical
  rw [← Finset.sum_filter]
  have he : (Finset.univ.filter fun i : Fin n => i.val < r) =
      Finset.univ.map (Fin.castLEEmb hrn) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro h; exact ⟨⟨i, h⟩, Fin.ext (by simp)⟩
    · rintro ⟨a, rfl⟩; simp
  rw [he, Finset.sum_map]
  rfl



noncomputable def gaussianJoin (r k : ℕ) :
    ((Fin r → ℝ) × (Fin k → ℝ)) ≃ᵐ (Fin (r+k) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin r ⊕ Fin k => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (r+k) => ℝ) finSumFinEquiv)

theorem gaussianJoin_preserving (r k : ℕ) :
    MeasurePreserving (gaussianJoin r k)
      ((stdGauss (Fin r)).prod (stdGauss (Fin k))) (stdGauss (Fin (r+k))) :=
  (measurePreserving_piCongrLeft
    (fun _ : Fin (r+k) => gaussianReal 0 1) finSumFinEquiv).comp
      (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin r ⊕ Fin k => gaussianReal 0 1))

theorem gaussianJoin_left (a : Fin r → ℝ) (z : Fin k → ℝ) (i : Fin r) :
    gaussianJoin r k (a,z) (Fin.castAdd k i) = a i := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Fin (r+k) => ℝ) finSumFinEquiv
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin r ⊕ Fin k => ℝ)).symm (a,z))
    (Sum.inl i)
  exact h

theorem gaussianJoin_right (a : Fin r → ℝ) (z : Fin k → ℝ) (i : Fin k) :
    gaussianJoin r k (a,z) (Fin.natAdd r i) = z i := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Fin (r+k) => ℝ) finSumFinEquiv
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin r ⊕ Fin k => ℝ)).symm (a,z))
    (Sum.inr i)
  exact h

theorem stdGauss_join_lintegral (r k : ℕ)
    (F : (Fin (r+k) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ g, F g ∂stdGauss (Fin (r+k))) =
      ∫⁻ a, ∫⁻ z, F (gaussianJoin r k (a,z)) ∂stdGauss (Fin k) ∂stdGauss (Fin r) := by
  rw [← (gaussianJoin_preserving r k).lintegral_comp_emb
    (gaussianJoin r k).measurableEmbedding F]
  exact lintegral_prod _ (hF.comp (gaussianJoin r k).measurable).aemeasurable

theorem gaussianJoin_add (a a' : Fin r → ℝ) (z z' : Fin k → ℝ) :
    gaussianJoin r k (a+a', z+z') = gaussianJoin r k (a,z) + gaussianJoin r k (a',z') := by
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp [gaussianJoin_left]
  · intro j; simp [gaussianJoin_right]

theorem gaussianJoin_smul (c : ℝ) (a : Fin r → ℝ) (z : Fin k → ℝ) :
    gaussianJoin r k (c • a,c • z) = c • gaussianJoin r k (a,z) := by
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp [gaussianJoin_left]
  · intro j; simp [gaussianJoin_right]

theorem gaussianJoin_sumsq (a : Fin r → ℝ) (z : Fin k → ℝ) :
    (∑ i, gaussianJoin r k (a,z) i ^ 2) = (∑ i, a i ^ 2) + ∑ i, z i ^ 2 := by
  rw [Fin.sum_univ_add]
  simp_rw [gaussianJoin_left, gaussianJoin_right]

noncomputable def tailR
    (b : OrthonormalBasis (Fin (r+k)) ℝ (EuclideanSpace ℝ (Fin (r+k))))
    (z : Fin k → ℝ) : Fin (r+k) → ℝ :=
  basisReconstruct b (gaussianJoin r k (0,z))

theorem tailR_sumsq
    (b : OrthonormalBasis (Fin (r+k)) ℝ (EuclideanSpace ℝ (Fin (r+k)))) (z : Fin k → ℝ) :
    (∑ i, tailR b z i ^ 2) = ∑ i, z i ^ 2 := by
  rw [tailR, basisReconstruct_sumsq, gaussianJoin_sumsq]
  simp

theorem tailR_smul
    (b : OrthonormalBasis (Fin (r+k)) ℝ (EuclideanSpace ℝ (Fin (r+k))))
    (c : ℝ) (z : Fin k → ℝ) : tailR b (c • z) = c • tailR b z := by
  unfold tailR
  have he : gaussianJoin r k (0,c • z) = c • gaussianJoin r k (0,z) := by
    simpa only [smul_zero] using gaussianJoin_smul c (0 : Fin r → ℝ) z
  rw [he, basisReconstruct_smul]

theorem headR_eq_span
    (b : OrthonormalBasis (Fin (r+k)) ℝ (EuclideanSpace ℝ (Fin (r+k))))
    (V : Fin r → Fin (r+k) → ℝ)
    (hb : ∀ a : Fin r, b (Fin.castAdd k a) = WithLp.toLp 2 (V a)) (a : Fin r → ℝ) :
    basisReconstruct b (gaussianJoin r k (a,0)) = spanV V a := by
  have h := b.sum_repr_symm (WithLp.toLp 2 (gaussianJoin r k (a,0)))
  change (∑ i, gaussianJoin r k (a,0) i • b i) = _ at h
  rw [Fin.sum_univ_add] at h
  simp only [gaussianJoin_left, gaussianJoin_right,
    Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero, hb] at h
  have h' := congrArg WithLp.ofLp h.symm
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_toLp] at h'
  ext i
  simpa only [basisReconstruct, spanV, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun h' i

theorem reconstruct_join
    (b : OrthonormalBasis (Fin (r+k)) ℝ (EuclideanSpace ℝ (Fin (r+k))))
    (V : Fin r → Fin (r+k) → ℝ)
    (hb : ∀ a : Fin r, b (Fin.castAdd k a) = WithLp.toLp 2 (V a))
    (a : Fin r → ℝ) (z : Fin k → ℝ) :
    basisReconstruct b (gaussianJoin r k (a,z)) = spanV V a + tailR b z := by
  have he : gaussianJoin r k (a,z) =
      gaussianJoin r k (a,0) + gaussianJoin r k (0,z) := by
    rw [← gaussianJoin_add]; simp
  rw [he, basisReconstruct_add, headR_eq_span b V hb]
  rfl

theorem coord_reconstruct_join
    (b : OrthonormalBasis (Fin (r+k)) ℝ (EuclideanSpace ℝ (Fin (r+k))))
    (V : Fin r → Fin (r+k) → ℝ)
    (hb : ∀ a : Fin r, b (Fin.castAdd k a) = WithLp.toLp 2 (V a))
    (a : Fin r → ℝ) (z : Fin k → ℝ) (i : Fin r) :
    coordY V (basisReconstruct b (gaussianJoin r k (a,z))) i = a i := by
  rw [coord_reconstruct (Nat.le_add_right r k) V b hb]
  change gaussianJoin r k (a,z) (Fin.castAdd k i) = a i
  exact gaussianJoin_left a z i

theorem perpDirR_reconstruct_join
    (b : OrthonormalBasis (Fin (r+k)) ℝ (EuclideanSpace ℝ (Fin (r+k))))
    (V : Fin r → Fin (r+k) → ℝ)
    (hb : ∀ a : Fin r, b (Fin.castAdd k a) = WithLp.toLp 2 (V a))
    (a : Fin r → ℝ) (z : Fin k → ℝ) :
    perpDirR V (basisReconstruct b (gaussianJoin r k (a,z))) = tailR b (unitF53 z) := by
  have he : (fun i => basisReconstruct b (gaussianJoin r k (a,z)) i -
      ∑ c, a c * V c i) = tailR b z := by
    rw [reconstruct_join b V hb]
    ext i
    simp [spanV]
  unfold perpDirR
  simp_rw [coord_reconstruct_join b V hb]
  simp_rw [show ∀ i, basisReconstruct b (gaussianJoin r k (a,z)) i -
    ∑ c, a c * V c i = tailR b z i from congrFun he]
  rw [tailR_sumsq]
  exact (tailR_smul b _ z).symm

theorem basis_join_lintegral
    (b : OrthonormalBasis (Fin (r+k)) ℝ (EuclideanSpace ℝ (Fin (r+k))))
    (F : (Fin (r+k) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ g, F g ∂stdGauss (Fin (r+k))) =
      ∫⁻ a, ∫⁻ z, F (basisReconstruct b (gaussianJoin r k (a,z)))
        ∂stdGauss (Fin k) ∂stdGauss (Fin r) := by
  rw [← (basisCoordinates_preserving b).symm.lintegral_comp_emb
    (basisCoordinates b).symm.measurableEmbedding F]
  exact stdGauss_join_lintegral r k _ (hF.comp (basisCoordinates b).symm.measurable)

theorem perpDirR_lintegral_tail
    (b : OrthonormalBasis (Fin (r+k)) ℝ (EuclideanSpace ℝ (Fin (r+k))))
    (V : Fin r → Fin (r+k) → ℝ)
    (hb : ∀ a : Fin r, b (Fin.castAdd k a) = WithLp.toLp 2 (V a))
    (F : (Fin (r+k) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ g, F (perpDirR V g) ∂stdGauss (Fin (r+k))) =
      ∫⁻ z, F (tailR b (unitF53 z)) ∂stdGauss (Fin k) := by
  rw [basis_join_lintegral b (fun g => F (perpDirR V g)) (hF.comp (KeyProof.measurable_dir V))]
  simp_rw [perpDirR_reconstruct_join b V hb]
  rw [lintegral_const]
  simp

theorem spanV_smul (V : Fin r → Fin n → ℝ) (c : ℝ) (a : Fin r → ℝ) :
    spanV V (c • a) = c • spanV V a := by
  ext i
  simp only [spanV, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

noncomputable def axialY (a : Fin r → ℝ) (R : ℝ) : Fin r → ℝ :=
  (1 / Real.sqrt ((∑ i, a i ^ 2) + R ^ 2)) • a

noncomputable def axialRad (a : Fin r → ℝ) (R : ℝ) : ℝ :=
  R / Real.sqrt ((∑ i, a i ^ 2) + R ^ 2)

noncomputable def polarPointR (V : Fin r → Fin n → ℝ) (w : Fin n → ℝ)
    (a : Fin r → ℝ) (R : ℝ) : Fin n → ℝ :=
  spanV V (axialY a R) + axialRad a R • w

theorem normalized_reconstruct_join
    (b : OrthonormalBasis (Fin (r+k)) ℝ (EuclideanSpace ℝ (Fin (r+k))))
    (V : Fin r → Fin (r+k) → ℝ)
    (hb : ∀ a : Fin r, b (Fin.castAdd k a) = WithLp.toLp 2 (V a))
    (a : Fin r → ℝ) (z : Fin k → ℝ) :
    unitF53 (basisReconstruct b (gaussianJoin r k (a,z))) =
      polarPointR V (tailR b (unitF53 z)) a (radF53 z) := by
  have hS : radF53 z ^ 2 = ∑ i, z i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have ht : tailR b z = radF53 z • tailR b (unitF53 z) := by
    rw [← tailR_smul, BstLean.Part56.rad_smul_unit]
  unfold unitF53
  rw [basisReconstruct_sumsq, gaussianJoin_sumsq, reconstruct_join b V hb, ht]
  unfold polarPointR axialY axialRad
  rw [spanV_smul, smul_add, smul_smul, hS]
  congr 1
  congr 1
  ring

theorem normalized_coord_join
    (b : OrthonormalBasis (Fin (r+k)) ℝ (EuclideanSpace ℝ (Fin (r+k))))
    (V : Fin r → Fin (r+k) → ℝ)
    (hb : ∀ a : Fin r, b (Fin.castAdd k a) = WithLp.toLp 2 (V a))
    (a : Fin r → ℝ) (z : Fin k → ℝ) (i : Fin r) :
    coordY V (unitF53 (basisReconstruct b (gaussianJoin r k (a,z)))) i =
      axialY a (radF53 z) i := by
  have he : coordY V (unitF53 (basisReconstruct b (gaussianJoin r k (a,z)))) i =
      (1 / radF53 (basisReconstruct b (gaussianJoin r k (a,z)))) *
        coordY V (basisReconstruct b (gaussianJoin r k (a,z))) i := by
    unfold coordY
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    simp only [unitF53, radF53, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, coord_reconstruct_join b V hb]
  simp only [radF53, basisReconstruct_sumsq, gaussianJoin_sumsq,
    axialY, Pi.smul_apply, smul_eq_mul,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

theorem axialY_sumsq_le_one (a : Fin r → ℝ) (R : ℝ) : ∑ i, axialY a R i ^ 2 ≤ 1 := by
  let S := (∑ i, a i ^ 2) + R ^ 2
  have hS : 0 ≤ S := by dsimp [S]; positivity
  by_cases hz : Real.sqrt S = 0
  · simp [axialY, S, hz]
  · have hp : 0 < S := lt_of_le_of_ne hS (by intro h; apply hz; rw [← h, Real.sqrt_zero])
    simp only [axialY, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum,
      one_div, inv_pow]
    change (Real.sqrt S ^ 2)⁻¹ * (∑ i, a i ^ 2) ≤ 1
    rw [Real.sq_sqrt hS]
    rw [← div_eq_inv_mul, div_le_one hp]
    dsimp [S]
    linarith [sq_nonneg R]

theorem axialRad_nonneg (a : Fin r → ℝ) (R : ℝ) (hR : 0 ≤ R) : 0 ≤ axialRad a R :=
  div_nonneg hR (Real.sqrt_nonneg _)

theorem axialRad_le_one (a : Fin r → ℝ) (R : ℝ) (hR : 0 ≤ R) : axialRad a R ≤ 1 := by
  have hA : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have he : axialRad a R = BstLean.Part56.axialR (Real.sqrt (∑ i, a i ^ 2)) R := by
    simp only [axialRad, BstLean.Part56.axialR, Real.sq_sqrt hA]
  rw [he]
  exact BstLean.Part56.axialR_le_one _ _ hR

theorem qA_rkR (t : Fin r → ℝ) (V : Fin r → Fin n → ℝ) (x : Fin n → ℝ) :
    BstLean.Part50.qA (rkR t V) x = ∑ a, t a * coordY V x a ^ 2 := by
  unfold BstLean.Part50.qA rkR coordY
  have e1 : ∀ a : Fin r, t a * (∑ i, V a i * x i) ^ 2 =
      ∑ i, ∑ j, t a * V a i * V a j * x i * x j := by
    intro a
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [e1, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem lawRR_lintegral_gauss (n : ℕ) (hn : 1 ≤ n) (t : Fin r → ℝ)
    (V : Fin r → Fin n → ℝ) (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂lawRR n t V) = ∫⁻ g, F (unitF53 g) * ENNReal.ofReal
      (Real.exp (∑ a, t a * coordY V (unitF53 g) a ^ 2) / BstLean.Part50.ZA n (rkR t V))
      ∂stdGauss (Fin n) := by
  have hw : Measurable (fun x : Fin n → ℝ => ENNReal.ofReal
      (Real.exp (BstLean.Part50.qA (rkR t V) x) / BstLean.Part50.ZA n (rkR t V))) := by
    unfold BstLean.Part50.qA
    fun_prop
  unfold lawRR BstLean.Part50.binghamA
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hF,
    BstLean.Part56.uniformSphere_lintegral_gauss n hn _ (hw.mul hF)]
  simp only [Pi.mul_apply, qA_rkR, mul_comm]

@[fun_prop] theorem continuous_spanV (V : Fin r → Fin n → ℝ) : Continuous (spanV V) := by
  apply continuous_pi
  intro i
  exact continuous_finsetSum _ (fun a _ => (continuous_apply a).mul continuous_const)

@[fun_prop] theorem measurable_tailR
    (b : OrthonormalBasis (Fin (r+k)) ℝ (EuclideanSpace ℝ (Fin (r+k)))) : Measurable (tailR b) := by
  change Measurable ((basisCoordinates b).symm ∘ (fun z : Fin k → ℝ => gaussianJoin r k (0,z)))
  exact (basisCoordinates b).symm.measurable.comp
    ((gaussianJoin r k).measurable.comp (measurable_const.prodMk measurable_id))

@[fun_prop] theorem measurable_axialY (a : Fin r → ℝ) : Measurable (axialY a) := by
  unfold axialY
  fun_prop

@[fun_prop] theorem measurable_axialRad (a : Fin r → ℝ) : Measurable (axialRad a) := by
  unfold axialRad
  fun_prop

end BstLean.Part57.PropD57
