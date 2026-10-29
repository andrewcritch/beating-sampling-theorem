import BstLean.Part105Defs

/-!
# Part 105, laws: Gaussian linear images, the correlation profile, sphere moments, the pair law
-/

namespace BstLean.Part105

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)

/-! ## Item 1: centred Gaussian vectors with the same covariance -/

section GaussLin

variable {ι κ : Type} [Fintype ι] [Fintype κ]

lemma sum_sq_transpose_mulVec (A : Matrix κ ι ℝ) (t : κ → ℝ) :
    ∑ j, (A.transpose.mulVec t) j ^ 2 = t ⬝ᵥ (A * A.transpose).mulVec t := by
  classical
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp [dotProduct, sq]

lemma charFun_gaussLin (A : Matrix κ ι ℝ) (t : EuclideanSpace ℝ κ) :
    charFun (((stdGauss ι).map (fun ξ => A.mulVec ξ)).map (WithLp.toLp 2)) t =
      Complex.exp (-((WithLp.ofLp t ⬝ᵥ (A * A.transpose).mulVec (WithLp.ofLp t) : ℝ) : ℂ) / 2) := by
  classical
  have h1 : charFun (((stdGauss ι).map (fun ξ => A.mulVec ξ)).map (WithLp.toLp 2)) t =
      charFun ((stdGauss ι).map (WithLp.toLp 2))
        (WithLp.toLp 2 (A.transpose.mulVec (WithLp.ofLp t))) := by
    rw [charFun_apply, charFun_apply, Measure.map_map (by fun_prop) (by fun_prop),
      integral_map (Measurable.aemeasurable (by fun_prop))
        (Measurable.aestronglyMeasurable (by fun_prop)),
      integral_map (Measurable.aemeasurable (by fun_prop))
        (Measurable.aestronglyMeasurable (by fun_prop))]
    congr 1
    funext ξ
    congr 2
    simp only [Function.comp_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    norm_cast
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h1]
  unfold stdGauss
  rw [map_pi_eq_stdGaussian, charFun_stdGaussian, ← Complex.ofReal_pow,
    EuclideanSpace.real_norm_sq_eq]
  simp only [sum_sq_transpose_mulVec]

/-- Item 1. -/
theorem gaussLin105 : GaussLin105 := by
  intro ι ι' κ _ _ _ A B hAB
  have hinj : Function.Injective
      (Measure.map (WithLp.toLp 2 : (κ → ℝ) → EuclideanSpace ℝ κ)) :=
    (MeasurableEquiv.toLp 2 (κ → ℝ)).map_measurableEquiv_injective
  apply hinj
  have : IsProbabilityMeasure ((stdGauss ι).map (fun ξ => A.mulVec ξ)) :=
    (Measure.isProbabilityMeasure_map_iff (Measurable.aemeasurable (by fun_prop))).2 inferInstance
  have : IsProbabilityMeasure ((stdGauss ι').map (fun ξ => B.mulVec ξ)) :=
    (Measure.isProbabilityMeasure_map_iff (Measurable.aemeasurable (by fun_prop))).2 inferInstance
  have : IsProbabilityMeasure (((stdGauss ι).map (fun ξ => A.mulVec ξ)).map
      (WithLp.toLp 2 : (κ → ℝ) → EuclideanSpace ℝ κ)) :=
    (Measure.isProbabilityMeasure_map_iff (Measurable.aemeasurable (by fun_prop))).2 inferInstance
  have : IsProbabilityMeasure (((stdGauss ι').map (fun ξ => B.mulVec ξ)).map
      (WithLp.toLp 2 : (κ → ℝ) → EuclideanSpace ℝ κ)) :=
    (Measure.isProbabilityMeasure_map_iff (Measurable.aemeasurable (by fun_prop))).2 inferInstance
  apply Measure.ext_of_charFun (E := EuclideanSpace ℝ κ)
  ext t
  rw [charFun_gaussLin, charFun_gaussLin, hAB]

end GaussLin

/-! ## Item 2: the correlation profile -/

lemma sum_Icc_pow_nonneg (d : ℕ) (t : ℝ) (ht : |t| ≤ 1) : 0 ≤ ∑ j ∈ Finset.Icc 2 d, t ^ j := by
  have h1 : ∑ j ∈ Finset.Icc 2 d, t ^ j = t ^ 2 * ∑ i ∈ Finset.range (d - 1), t ^ i := by
    rw [show Finset.Icc 2 d = Finset.Ico 2 (d + 1) from rfl, Finset.sum_Ico_eq_sum_range,
      Finset.mul_sum]
    refine Finset.sum_congr (by congr 1) fun i _ => by ring
  rw [h1]
  apply mul_nonneg (sq_nonneg t)
  obtain ⟨hl, hu⟩ := abs_le.mp ht
  rcases eq_or_lt_of_le hu with h | h
  · subst h; simp
  · have h2 := mul_neg_geom_sum t (d - 1)
    have h3 : t ^ (d - 1) ≤ 1 := by
      calc t ^ (d - 1) ≤ |t| ^ (d - 1) := by rw [← abs_pow]; exact le_abs_self _
        _ ≤ 1 := pow_le_one₀ (abs_nonneg t) ht
    have h4 : 0 ≤ (1 - t) * ∑ i ∈ Finset.range (d - 1), t ^ i := by rw [h2]; linarith
    exact nonneg_of_mul_nonneg_right h4 (by linarith)

lemma sum_Icc_pow_le (d : ℕ) (t : ℝ) (hd : 2 ≤ d) (ht : |t| ≤ 1) :
    ∑ j ∈ Finset.Icc 2 d, t ^ j ≤ (d : ℝ) - 1 := by
  have h : ∑ j ∈ Finset.Icc 2 d, t ^ j ≤ ∑ _j ∈ Finset.Icc 2 d, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    calc t ^ j ≤ |t| ^ j := by rw [← abs_pow]; exact le_abs_self _
      _ ≤ 1 := pow_le_one₀ (abs_nonneg t) ht
  refine h.trans (le_of_eq ?_)
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  rw [show d + 1 - 2 = d - 1 by omega, Nat.cast_sub (by omega)]
  simp

/-- Item 2. -/
theorem rhoBounds105 : RhoBounds105 := by
  intro d t hd ht
  have hd' : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold rho
  exact ⟨div_nonneg (sum_Icc_pow_nonneg d t ht) hd'.le,
    (div_le_one hd').2 (sum_Icc_pow_le d t hd ht)⟩

/-! ## Item 3: moments of `u · u'` on the sphere -/

/-- The `j`-th moment of a coordinate of a uniform point of the unit sphere of `ℝ^N`. -/
noncomputable def sphMom (N j : ℕ) : ℝ :=
  if Even j then BstLean.Part29.gaussMom j / BstLean.Part36.rhoD N (j / 2) else 0

lemma sphere_cont_integrable {n : ℕ} (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f (uniformSphere n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

lemma continuous_dot {N : ℕ} (u : Fin N → ℝ) : Continuous (fun u' : Fin N → ℝ => dot u u') := by
  unfold dot
  fun_prop

lemma dot_self_eq {N : ℕ} (u : Fin N → ℝ) : dot u u = ∑ i, u i ^ 2 := by
  unfold dot
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sphere_dot_pow (N : ℕ) (hN : 1 ≤ N) (u : Fin N → ℝ) (hu : dot u u = 1) (j : ℕ) :
    ∫ u', dot u u' ^ j ∂uniformSphere N = sphMom N j := by
  have hu' : ∑ i, u i ^ 2 = 1 := by rw [← dot_self_eq, hu]
  unfold sphMom dot
  rcases Nat.even_or_odd' j with ⟨m, rfl | rfl⟩
  · rw [BstLean.Part58.Kappa.sphere_linear_even hN u m, hu']
    simp
  · rw [BstLean.Part58.Kappa.sphere_linear_odd u m]
    simp

lemma integrable_dot_pow (N : ℕ) (hN : 1 ≤ N) (u : Fin N → ℝ) (j : ℕ) :
    Integrable (fun u' => dot u u' ^ j) (uniformSphere N) :=
  sphere_cont_integrable hN ((continuous_dot u).pow j)

theorem integral_rho_dot (N d : ℕ) (hN : 1 ≤ N) (u : Fin N → ℝ) (hu : dot u u = 1) :
    ∫ u', rho d (dot u u') ∂uniformSphere N =
      (∑ j ∈ Finset.Icc 2 d, sphMom N j) / ((d : ℝ) - 1) := by
  unfold rho
  rw [integral_div, integral_finsetSum _ fun j _ => integrable_dot_pow N hN u j]
  congr 1
  exact Finset.sum_congr rfl fun j _ => sphere_dot_pow N hN u hu j

theorem lam0_eq (N d : ℕ) (hN : 1 ≤ N) :
    lam0 N d = (∑ j ∈ Finset.Icc 2 d, sphMom N j) / ((d : ℝ) - 1) := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  unfold lam0
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have : ∀ᵐ u ∂uniformSphere N, ∫ u', dot u u' ^ j ∂uniformSphere N = sphMom N j := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere N] with u hu
    exact sphere_dot_pow N hN u (by rw [dot_self_eq, hu]) j
  rw [integral_congr_ae this]
  simp

/-- Item 3a. -/
theorem lamRow105 : LamRow105 := by
  intro N d u hN hu
  rw [integral_rho_dot N d hN u hu, lam0_eq N d hN]

/-- Item 3b. -/
theorem lamValue105 : LamValue105 := by
  intro N hN
  rw [lam0_eq N 6 hN]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hI : Finset.Icc 2 6 = {2, 3, 4, 5, 6} := by decide
  rw [hI]
  simp only [sphMom, BstLean.Part29.gaussMom, BstLean.Part36.rhoD]
  norm_num [Finset.prod_range_succ, Nat.doubleFactorial, Nat.even_iff]
  ring

/-! ## Item 4: the pair distribution -/

section PairLaw

variable {N n d : ℕ}

/-- The matrix of `ξ ↦ R(u)`, `R` the terms of degree `2` to `d` with Gaussian coordinates
`σ ξ`. -/
noncomputable def rowMat (σ : ℝ) (u : Fin N → ℝ) : Matrix (Fin n) (CoefIdx N n d) ℝ :=
  fun a i => if a = i.1 then
    (if 2 ≤ i.2.deg then σ * monoVal u i.2 / Real.sqrt (bwWeight i.2) else 0) else 0

lemma bwWeight_nonneg (m : MonoIdx N d) : 0 ≤ bwWeight m := by
  unfold bwWeight
  positivity

lemma bwEval_eq_rowMat (σ : ℝ) (u : Fin N → ℝ) (ξ : CoefIdx N n d → ℝ) :
    bwEval (mixW 0 (bwOfCoord (σ • ξ))) u = (rowMat σ u).mulVec ξ := by
  funext a
  simp only [bwEval, mixW, bwOfCoord, Matrix.mulVec, dotProduct, rowMat, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h2 : 2 ≤ m.deg
  · simp only [h2, ite_true, Pi.smul_apply, smul_eq_mul]
    ring
  · simp [h2]

lemma rowMat_mul_transpose (hM : Multinomial105) (σ : ℝ) (u u' : Fin N → ℝ) :
    (rowMat (N := N) (n := n) (d := d) σ u) * (rowMat (N := N) (n := n) (d := d) σ u').transpose =
      (σ ^ 2 * ∑ j ∈ Finset.Icc 2 d, dot u u' ^ j) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  ext a a'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowMat, Fintype.sum_prod_type,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  by_cases h : a = a'
  · subst h
    simp only [ite_true, mul_one]
    have key : ∀ m : MonoIdx N d,
        (if 2 ≤ m.deg then σ * monoVal u m / Real.sqrt (bwWeight m) else 0) *
          (if 2 ≤ m.deg then σ * monoVal u' m / Real.sqrt (bwWeight m) else 0) =
        ∑ j ∈ Finset.Icc 2 d,
          if m.deg = j then σ ^ 2 * (monoVal u m * monoVal u' m / bwWeight m) else 0 := by
      intro m
      rw [Finset.sum_ite_eq]
      have hmd : m.deg ≤ d := Nat.lt_succ_iff.mp m.1.isLt
      by_cases h2 : 2 ≤ m.deg
      · have hmem : m.deg ∈ Finset.Icc 2 d := Finset.mem_Icc.2 ⟨h2, hmd⟩
        simp only [h2, hmem, ite_true]
        have hw := Real.mul_self_sqrt (bwWeight_nonneg m)
        rw [div_mul_div_comm, hw]
        ring
      · have hmem : m.deg ∉ Finset.Icc 2 d := fun hc => h2 (Finset.mem_Icc.1 hc).1
        simp only [h2, hmem, ite_false, mul_zero]
    simp_rw [key]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← hM N d u u' j (Finset.mem_Icc.1 hj).2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  · have h' : ¬ a' = a := fun hc => h hc.symm
    simp [h, h']

lemma measurable_bwEval_mixW (u : Fin N → ℝ) :
    Measurable (fun c : CoefIdx N n d → ℝ => bwEval (mixW 0 c) u) := by
  refine measurable_pi_iff.2 fun a => ?_
  unfold bwEval
  refine Finset.measurable_sum _ fun m _ => ?_
  simp only [mixW]
  split_ifs
  · fun_prop
  · fun_prop

lemma measurable_bwOfCoord_smul (σ : ℝ) :
    Measurable (fun ξ : CoefIdx N n d → ℝ => bwOfCoord (σ • ξ)) := by
  unfold bwOfCoord
  refine measurable_pi_iff.2 fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  fun_prop

lemma dot_comm' (u u' : Fin N → ℝ) : dot u u' = dot u' u := by
  unfold dot
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma abs_dot_le_one (u u' : Fin N → ℝ) (hu : dot u u = 1) (hu' : dot u' u' = 1) :
    |dot u u'| ≤ 1 := by
  rw [← sq_le_one_iff_abs_le_one]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u u'
  rw [← dot_self_eq, ← dot_self_eq, hu, hu'] at h
  unfold dot
  linarith

/-- Item 4. -/
theorem pairLaw105_of (hM : Multinomial105) : PairLaw105 := by
  classical
  intro N n d σ u u' hd hu hu'
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨hρ0, hρ1⟩ := rhoBounds105 d (dot u u') hd (abs_dot_le_one u u' hu hu')
  generalize hρ : rho d (dot u u') = ρ at hρ0 hρ1 ⊢
  generalize hτ : Real.sqrt ((d : ℝ) - 1) * σ = τ
  generalize hs : Real.sqrt (1 - ρ ^ 2) = s
  have hss : s * s = 1 - ρ ^ 2 := by
    rw [← hs]
    exact Real.mul_self_sqrt (by nlinarith)
  have hττ : τ * τ = σ ^ 2 * ((d : ℝ) - 1) := by
    rw [← hτ]
    have := Real.mul_self_sqrt hd1.le
    nlinarith
  have hsum1 : ∑ j ∈ Finset.Icc 2 d, (1 : ℝ) ^ j = (d : ℝ) - 1 := by
    simp only [one_pow, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    rw [show d + 1 - 2 = d - 1 by omega, Nat.cast_sub (by omega)]
    simp
  have hsumρ : ∑ j ∈ Finset.Icc 2 d, dot u u' ^ j = ((d : ℝ) - 1) * ρ := by
    rw [← hρ]
    unfold rho
    field_simp
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ)
  let A : Matrix (Fin n ⊕ Fin n) (CoefIdx N n d) ℝ := Matrix.fromRows (rowMat σ u) (rowMat σ u')
  let B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
    Matrix.fromBlocks (τ • 1) 0 ((τ * ρ) • 1) ((τ * s) • 1)
  have hAB : A * A.transpose = B * B.transpose := by
    simp only [A, B, Matrix.transpose_fromRows, Matrix.fromRows_mul_fromCols,
      rowMat_mul_transpose hM, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      hu, hu', dot_comm' u' u, hsum1, hsumρ]
    simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_zero,
      Matrix.mul_smul, Matrix.mul_one, Matrix.mul_zero, smul_zero,
      add_zero, smul_smul, ← add_smul]
    congr 2
    · rw [hττ]
    · rw [show τ * ρ * τ = τ * τ * ρ by ring, hττ]; ring
    · rw [show τ * (τ * ρ) = τ * τ * ρ by ring, hττ]; ring
    · rw [show τ * ρ * (τ * ρ) + τ * s * (τ * s) = τ * τ * (ρ ^ 2 + s * s) by ring, hττ, hss]
      ring
  have hL : (fun c : CoefIdx N n d → ℝ => (bwEval (mixW 0 c) u, bwEval (mixW 0 c) u')) ∘
      (fun ξ : CoefIdx N n d → ℝ => bwOfCoord (σ • ξ)) = e ∘ (fun ξ => A.mulVec ξ) := by
    funext ξ
    simp only [Function.comp_apply, bwEval_eq_rowMat, A, Matrix.fromRows_mulVec]
    rfl
  have hR : (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (τ • p.1, τ • (ρ • p.1 + s • p.2))) ∘ e =
      e ∘ (fun ξ => B.mulVec ξ) := by
    funext ξ
    simp only [Function.comp_apply, B, Matrix.fromBlocks_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
    refine Prod.ext ?_ ?_
    · rfl
    · funext a
      simp [e, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, mul_add, mul_assoc]
  have hprod : (stdGauss (Fin n)).prod (stdGauss (Fin n)) = (stdGauss (Fin n ⊕ Fin n)).map e :=
    ((measurePreserving_sumPiEquivProdPi
      (fun _ : Fin n ⊕ Fin n => gaussianReal 0 1)).map_eq).symm
  have hmF : Measurable (fun c : CoefIdx N n d → ℝ =>
      (bwEval (mixW 0 c) u, bwEval (mixW 0 c) u')) :=
    (measurable_bwEval_mixW u).prodMk (measurable_bwEval_mixW u')
  unfold bwGauss
  rw [Measure.map_map hmF (measurable_bwOfCoord_smul σ), hL, hprod,
    Measure.map_map (by fun_prop) e.measurable, hR,
    ← Measure.map_map e.measurable (by fun_prop), ← Measure.map_map e.measurable (by fun_prop),
    gaussLin105 _ _ _ A B hAB]

end PairLaw

#print axioms gaussLin105
#print axioms rhoBounds105
#print axioms sphere_dot_pow
#print axioms lamRow105
#print axioms lamValue105
#print axioms pairLaw105_of

end BstLean.Part105
