import BstLean.Part105Defs
import BstLean.Part35Wick
import BstLean.Part48Var
import BstLean.Part56PropD_Polar

/-!
# Part 105: the Bombieri–Weyl inner product, the Gaussian version and the sphere version

Role: `delegations/statements/p105-spec.md`. Definitions: `BstLean/Part105Defs.lean`.
-/

namespace BstLean.Part105

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)

variable {k q d : ℕ}

/-! ## The weight and the multinomial identity -/

theorem bwWeight_pos (m : MonoIdx k d) : 0 < bwWeight m := by
  unfold bwWeight
  apply div_pos
  · exact Finset.prod_pos fun l _ => by exact_mod_cast Nat.factorial_pos _
  · exact_mod_cast Nat.factorial_pos _

private lemma countPerms_mul (j : ℕ) (s : Sym (Fin k) j) :
    ((s.1.countPerms : ℕ) : ℝ) * ∏ l : Fin k, ((s.1.count l).factorial : ℝ) = (j.factorial : ℝ) := by
  have h := Nat.multinomial_spec (Finset.univ : Finset (Fin k)) (fun l => s.1.count l)
  have h2 : Nat.multinomial (Finset.univ : Finset (Fin k)) (fun l => s.1.count l) =
      s.1.countPerms := by
    have := Finsupp.multinomial_of_support_subset (d := Multiset.toFinsupp s.1)
      (s := (Finset.univ : Finset (Fin k))) (Finset.subset_univ _)
    exact this
  have h3 : ∑ l : Fin k, s.1.count l = j := by
    have hcard : Multiset.card s.1 = j := s.2
    refine Eq.trans ?_ ((Multiset.toFinset_sum_count_eq s.1).trans hcard)
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro l _ hl
    exact Multiset.count_eq_zero.mpr (by simpa using hl)
  rw [h2, h3] at h
  rw [mul_comm]
  exact_mod_cast h

private lemma multinomial_aux (x y : Fin k → ℝ) (j : Fin (d + 1)) :
    ∑ s : Sym (Fin k) j, monoVal x (⟨j, s⟩ : MonoIdx k d) * monoVal y (⟨j, s⟩ : MonoIdx k d) /
      bwWeight (⟨j, s⟩ : MonoIdx k d) = dot x y ^ (j : ℕ) := by
  unfold dot
  rw [Finset.sum_pow, Finset.sym_univ]
  apply Finset.sum_congr rfl
  intro s _
  have hc := countPerms_mul (j : ℕ) s
  have hp : (0 : ℝ) < ∏ l : Fin k, ((s.1.count l).factorial : ℝ) :=
    Finset.prod_pos fun l _ => by exact_mod_cast Nat.factorial_pos _
  have hj : (0 : ℝ) < ((j : ℕ).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  simp only [monoVal, bwWeight, MonoIdx.deg, Multiset.prod_map_mul]
  rw [← hc]
  field_simp

theorem multinomial105 : Multinomial105 := by
  intro k d x y j hj
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single (⟨j, by omega⟩ : Fin (d + 1))]
  · simp only [MonoIdx.deg, ↓reduceIte]
    exact multinomial_aux x y ⟨j, by omega⟩
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro s _
    exact ite_eq_right_iff.mpr fun h => absurd (Fin.ext h) hb
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## The orthonormal coordinates -/

theorem bwInner_ofCoord (ξ η : CoefIdx k q d → ℝ) :
    bwInner (bwOfCoord ξ) (bwOfCoord η) = ∑ i, ξ i * η i := by
  unfold bwInner bwOfCoord
  apply Finset.sum_congr rfl
  intro i _
  have hw := bwWeight_pos i.2
  have hs : Real.sqrt (bwWeight i.2) * Real.sqrt (bwWeight i.2) = bwWeight i.2 :=
    Real.mul_self_sqrt hw.le
  have hs0 : Real.sqrt (bwWeight i.2) ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
  rw [div_mul_div_comm, hs]
  field_simp

theorem measurable_bwOfCoord : Measurable (bwOfCoord (k := k) (q := q) (d := d)) := by
  unfold bwOfCoord
  exact measurable_pi_iff.mpr fun i => (measurable_pi_apply i).div_const _

theorem measurable_bwGaussMap (σ : ℝ) :
    Measurable (fun ξ : CoefIdx k q d → ℝ => bwOfCoord (σ • ξ)) :=
  measurable_bwOfCoord.comp (measurable_const_smul σ)

theorem measurable_bwSphereMap :
    Measurable (fun ξ : CoefIdx k q d → ℝ =>
      bwOfCoord ((1 / Real.sqrt (∑ i, ξ i ^ 2)) • ξ)) :=
  measurable_bwOfCoord.comp BstLean.Part53.measurable_unitF

instance : IsProbabilityMeasure (bwGauss k q d σ) := by
  unfold bwGauss
  infer_instance

instance : IsProbabilityMeasure (bwSphere k q d) := by
  unfold bwSphere
  infer_instance

theorem bwGauss_integral (σ : ℝ) (F : (CoefIdx k q d → ℝ) → ℝ) (hF : Measurable F) :
    ∫ c, F c ∂bwGauss k q d σ = ∫ ξ, F (bwOfCoord (σ • ξ)) ∂stdGauss (CoefIdx k q d) := by
  unfold bwGauss
  exact integral_map (measurable_bwGaussMap σ).aemeasurable hF.aestronglyMeasurable

/-! ## Mean and covariance of the evaluation under the Gaussian version -/

private lemma gauss_pair105 {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    ∫ z, z i * z j ∂stdGauss ι = if i = j then 1 else 0 := by
  have hw := BstLean.Part35.stdGauss_wick_step i 1 (fun _ : Fin 1 => j)
  simpa [eq_comm] using hw

private lemma gauss_coord_mean105 {ι : Type*} [Fintype ι] (i : ι) :
    ∫ z, z i ∂stdGauss ι = 0 := by
  classical
  have hw := BstLean.Part35.stdGauss_wick_step i 0 (Fin.elim0 : Fin 0 → ι)
  simpa using hw

private lemma sumsq_pos105 {ι : Type*} [Fintype ι] (z : ι → ℝ) (hz : z ≠ 0) :
    0 < ∑ i, z i ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hi)
    (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i))

private lemma gauss_coord_integrable {ι : Type*} [Fintype ι] (i : ι) :
    Integrable (fun z : ι → ℝ => z i) (stdGauss ι) := by
  simpa using BstLean.Part48.gauss_poly_integrable (MvPolynomial.X i : MvPolynomial ι ℝ)

private lemma gauss_pair_integrable {ι : Type*} [Fintype ι] (i j : ι) :
    Integrable (fun z : ι → ℝ => z i * z j) (stdGauss ι) := by
  have h := BstLean.Part48.gauss_poly_integrable
    (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial ι ℝ)
  simp only [map_mul, MvPolynomial.eval_X] at h
  exact h

/-- The coefficient of `ξ (a, m)` in `bwEval (bwOfCoord (σ • ξ)) x a`. -/
private noncomputable def evC (σ : ℝ) (x : Fin k → ℝ) (m : MonoIdx k d) : ℝ :=
  σ * monoVal x m / Real.sqrt (bwWeight m)

private lemma bwEval_ofCoord (σ : ℝ) (ξ : CoefIdx k q d → ℝ) (x : Fin k → ℝ) (a : Fin q) :
    bwEval (bwOfCoord (σ • ξ)) x a = ∑ m : MonoIdx k d, evC σ x m * ξ (a, m) := by
  unfold bwEval bwOfCoord evC
  apply Finset.sum_congr rfl
  intro m _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma evC_mul (σ : ℝ) (x y : Fin k → ℝ) (m : MonoIdx k d) :
    evC σ x m * evC σ y m = σ ^ 2 * (monoVal x m * monoVal y m / bwWeight m) := by
  unfold evC
  have hw := bwWeight_pos m
  have hs : Real.sqrt (bwWeight m) * Real.sqrt (bwWeight m) = bwWeight m :=
    Real.mul_self_sqrt hw.le
  rw [div_mul_div_comm, hs]
  ring

private lemma sum_by_deg (f : MonoIdx k d → ℝ) :
    ∑ m, f m = ∑ j ∈ Finset.range (d + 1), ∑ m : MonoIdx k d, if m.deg = j then f m else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_ite_eq]
  simp [MonoIdx.deg, m.1.2]

theorem measurable_bwEval (x : Fin k → ℝ) (a : Fin q) :
    Measurable (fun c : CoefIdx k q d → ℝ => bwEval c x a) := by
  unfold bwEval
  fun_prop

theorem bwGauss_eval_integrable (σ : ℝ) (x : Fin k → ℝ) (a : Fin q) :
    Integrable (fun c => bwEval c x a) (bwGauss k q d σ) := by
  unfold bwGauss
  rw [integrable_map_measure (measurable_bwEval x a).aestronglyMeasurable
    (measurable_bwGaussMap σ).aemeasurable]
  simp only [Function.comp_def, bwEval_ofCoord]
  exact integrable_finsetSum _ fun m _ => (gauss_coord_integrable (a, m)).const_mul _

private lemma pair_expand (σ : ℝ) (ξ : CoefIdx k q d → ℝ) (x y : Fin k → ℝ) (a b : Fin q) :
    bwEval (bwOfCoord (σ • ξ)) x a * bwEval (bwOfCoord (σ • ξ)) y b =
      ∑ m : MonoIdx k d, ∑ m' : MonoIdx k d,
        (evC σ x m * evC σ y m') * (ξ (a, m) * ξ (b, m')) := by
  rw [bwEval_ofCoord, bwEval_ofCoord, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro m' _
  ring

theorem bwGauss_eval_mul_integrable (σ : ℝ) (x y : Fin k → ℝ) (a b : Fin q) :
    Integrable (fun c => bwEval c x a * bwEval c y b) (bwGauss k q d σ) := by
  unfold bwGauss
  have hm : Measurable (fun c : CoefIdx k q d → ℝ => bwEval c x a * bwEval c y b) :=
    (measurable_bwEval x a).mul (measurable_bwEval y b)
  rw [integrable_map_measure hm.aestronglyMeasurable (measurable_bwGaussMap σ).aemeasurable]
  simp only [Function.comp_def, pair_expand]
  exact integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun m' _ =>
    (gauss_pair_integrable (a, m) (b, m')).const_mul _

theorem bwGauss_mean (σ : ℝ) (x : Fin k → ℝ) (a : Fin q) :
    ∫ c, bwEval c x a ∂bwGauss k q d σ = 0 := by
  rw [bwGauss_integral σ _ (measurable_bwEval x a)]
  simp only [bwEval_ofCoord]
  rw [integral_finsetSum _ fun m _ => (gauss_coord_integrable (a, m)).const_mul _]
  apply Finset.sum_eq_zero
  intro m _
  rw [integral_const_mul, gauss_coord_mean105, mul_zero]

theorem bwGauss_cov (σ : ℝ) (x y : Fin k → ℝ) (a b : Fin q) :
    ∫ c, bwEval c x a * bwEval c y b ∂bwGauss k q d σ =
      if a = b then σ ^ 2 * ∑ j ∈ Finset.range (d + 1), dot x y ^ j else 0 := by
  classical
  have hm : Measurable (fun c : CoefIdx k q d → ℝ => bwEval c x a * bwEval c y b) :=
    (measurable_bwEval x a).mul (measurable_bwEval y b)
  rw [bwGauss_integral σ _ hm]
  simp only [pair_expand]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun m' _ =>
    (gauss_pair_integrable (a, m) (b, m')).const_mul _]
  have h1 (m : MonoIdx k d) :
      ∫ ξ : CoefIdx k q d → ℝ, ∑ m' : MonoIdx k d,
        (evC σ x m * evC σ y m') * (ξ (a, m) * ξ (b, m')) ∂stdGauss (CoefIdx k q d) =
      if a = b then evC σ x m * evC σ y m else 0 := by
    rw [integral_finsetSum _ fun m' _ => (gauss_pair_integrable (a, m) (b, m')).const_mul _]
    simp only [integral_const_mul, gauss_pair105, Prod.mk.injEq]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab]
  simp only [h1]
  by_cases hab : a = b
  · simp only [hab, ite_true, evC_mul]
    rw [← Finset.mul_sum, sum_by_deg]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact multinomial105 k d x y j (by simpa [Nat.lt_succ_iff] using hj)
  · simp [hab]

/-! ## The sphere version -/

private lemma gauss_ne_zero_ae105 {ι : Type*} [Fintype ι] [Nonempty ι] :
    ∀ᵐ z ∂stdGauss ι, z ≠ 0 := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hz : stdGauss ι {(0 : ι → ℝ)} = 0 := by
    change (Measure.pi (fun _ : ι => gaussianReal 0 1)) {0} = 0
    exact measure_singleton _
  rw [ae_iff]
  simpa only [not_not, Set.ofPred_eq_eq_singleton] using hz

theorem bwSphere_normSq (hq : 1 ≤ q) : ∀ᵐ b ∂bwSphere k q d, bwNormSq b = 1 := by
  have : Nonempty (CoefIdx k q d) := ⟨(⟨0, hq⟩, ⟨0, Sym.nil⟩)⟩
  unfold bwSphere
  have hm : MeasurableSet {b : CoefIdx k q d → ℝ | bwNormSq b = 1} := by
    apply measurableSet_eq_fun _ measurable_const
    unfold bwNormSq bwInner
    fun_prop
  rw [ae_map_iff measurable_bwSphereMap.aemeasurable hm]
  filter_upwards [gauss_ne_zero_ae105 (ι := CoefIdx k q d)] with ξ hξ
  have hpos := sumsq_pos105 ξ hξ
  unfold bwNormSq
  rw [bwInner_ofCoord]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hs : Real.sqrt (∑ i, ξ i ^ 2) * Real.sqrt (∑ i, ξ i ^ 2) = ∑ i, ξ i ^ 2 :=
    Real.mul_self_sqrt hpos.le
  have hs0 : Real.sqrt (∑ i, ξ i ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have : ∀ i, 1 / Real.sqrt (∑ i, ξ i ^ 2) * ξ i * (1 / Real.sqrt (∑ i, ξ i ^ 2) * ξ i) =
      ξ i ^ 2 / (∑ i, ξ i ^ 2) := by
    intro i
    have : 1 / Real.sqrt (∑ i, ξ i ^ 2) * ξ i * (1 / Real.sqrt (∑ i, ξ i ^ 2) * ξ i) =
        ξ i ^ 2 / (Real.sqrt (∑ i, ξ i ^ 2) * Real.sqrt (∑ i, ξ i ^ 2)) := by
      field_simp
    rw [this, hs]
  simp only [this]
  rw [← Finset.sum_div, div_self hpos.ne']

/-! ## Independence of the low-degree and the high-degree coefficients -/

/-- Mixing two independent standard Gaussians coordinatewise gives a standard Gaussian. -/
theorem stdGauss_mix {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] :
    ((stdGauss ι).prod (stdGauss ι)).map
      (fun p : (ι → ℝ) × (ι → ℝ) => fun i => if P i then p.2 i else p.1 i) = stdGauss ι := by
  have hmeas : Measurable
      (fun p : (ι → ℝ) × (ι → ℝ) => fun i => if P i then p.2 i else p.1 i) := by
    refine measurable_pi_iff.mpr fun i => ?_
    by_cases hi : P i
    · simp only [hi, ite_true]; fun_prop
    · simp only [hi, ite_false]; fun_prop
  symm
  unfold stdGauss
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → ℝ) × (ι → ℝ) => fun i => if P i then p.2 i else p.1 i) ⁻¹'
      (Set.univ.pi s) =
      (Set.univ.pi fun i => if P i then Set.univ else s i) ×ˢ
        (Set.univ.pi fun i => if P i then s i else Set.univ) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      constructor <;> intro i <;> have := h i <;> by_cases hi : P i <;> simp_all
    · rintro ⟨h1, h2⟩ i
      have a1 := h1 i
      have a2 := h2 i
      by_cases hi : P i <;> simp_all
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : P i <;> simp [hi]

theorem bwGauss_mix (σ : ℝ) :
    ((bwGauss k q d σ).prod (bwGauss k q d σ)).map (fun p => mixW p.1 p.2) =
      bwGauss k q d σ := by
  have hT := measurable_bwGaussMap (k := k) (q := q) (d := d) σ
  have hmix : Measurable (fun p : (CoefIdx k q d → ℝ) × (CoefIdx k q d → ℝ) => mixW p.1 p.2) := by
    unfold mixW
    refine measurable_pi_iff.mpr fun i => ?_
    by_cases hi : 2 ≤ i.2.deg
    · simp only [hi, ite_true]; fun_prop
    · simp only [hi, ite_false]; fun_prop
  have hmix' : Measurable (fun p : (CoefIdx k q d → ℝ) × (CoefIdx k q d → ℝ) =>
      fun i => if 2 ≤ i.2.deg then p.2 i else p.1 i) := hmix
  conv_rhs => rw [bwGauss, ← stdGauss_mix (fun i : CoefIdx k q d => 2 ≤ i.2.deg)]
  unfold bwGauss
  rw [Measure.map_prod_map _ _ hT hT, Measure.map_map hmix (hT.prodMap hT),
    Measure.map_map hT hmix']
  congr 1
  funext p
  funext i
  simp only [Function.comp_def, mixW, Prod.map, bwOfCoord, Pi.smul_apply]
  split_ifs <;> rfl

/-! ## The sphere version as an image of the uniform measure on the sphere -/

private lemma uniformSphere_eq_map (M : ℕ) (hM : 1 ≤ M) :
    uniformSphere M = (stdGauss (Fin M)).map BstLean.Part53.unitF53 := by
  ext s hs
  rw [Measure.map_apply BstLean.Part53.measurable_unitF hs,
    ← lintegral_indicator_one hs,
    BstLean.Part56.uniformSphere_lintegral_gauss M hM _ (measurable_one.indicator hs),
    ← lintegral_indicator_one (BstLean.Part53.measurable_unitF hs)]
  rfl

theorem bwSphere_eq_map_uniformSphere {M : ℕ} (e : CoefIdx k q d ≃ Fin M) (hM : 1 ≤ M) :
    bwSphere k q d = (uniformSphere M).map (fun v => bwOfCoord (fun i => v (e i))) := by
  have hR : Measurable (fun (ξ : CoefIdx k q d → ℝ) (j : Fin M) => ξ (e.symm j)) :=
    measurable_pi_iff.mpr fun j => measurable_pi_apply _
  have hB : stdGauss (Fin M) =
      (stdGauss (CoefIdx k q d)).map (fun ξ j => ξ (e.symm j)) := by
    have h := (measurePreserving_piCongrLeft (fun _ : Fin M => gaussianReal 0 1) e).map_eq
    have hf : (MeasurableEquiv.piCongrLeft (fun _ : Fin M => ℝ) e : (CoefIdx k q d → ℝ) → _) =
        fun ξ j => ξ (e.symm j) := by
      funext ξ j
      simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    rw [hf] at h
    exact h.symm
  have hV : Measurable (fun v : Fin M → ℝ => bwOfCoord (k := k) (q := q) (d := d)
      (fun i => v (e i))) :=
    measurable_bwOfCoord.comp (measurable_pi_iff.mpr fun i => measurable_pi_apply _)
  rw [uniformSphere_eq_map M hM, hB, Measure.map_map BstLean.Part53.measurable_unitF hR,
    Measure.map_map hV (BstLean.Part53.measurable_unitF.comp hR)]
  unfold bwSphere
  congr 1
  funext ξ
  simp only [Function.comp_def, BstLean.Part53.unitF53]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Equiv.symm_apply_apply]
  rw [e.symm.sum_comp (fun i => ξ i ^ 2)]

#print axioms bwWeight_pos
#print axioms multinomial105
#print axioms bwInner_ofCoord
#print axioms bwGauss_integral
#print axioms bwGauss_eval_integrable
#print axioms bwGauss_eval_mul_integrable
#print axioms bwGauss_mean
#print axioms bwGauss_cov
#print axioms bwSphere_normSq
#print axioms stdGauss_mix
#print axioms bwGauss_mix
#print axioms bwSphere_eq_map_uniformSphere

end BstLean.Part105
