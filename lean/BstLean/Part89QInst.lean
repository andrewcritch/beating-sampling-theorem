import BstLean.Part89QDefs
import BstLean.Part86Inst
import BstLean.Part86Ident
import BstLean.Part86SliceOp
import BstLean.Part86RotA
import BstLean.Part86ArithS
import BstLean.Part80Bridge
import BstLean.Part80PLow4

/-!
# Part 89, `d_f = 2`: the facts of the instance `modRK` used by the variance bound

* `instSph`: the points of the model are on the unit sphere, almost surely.
* `instSliceOpF`: `SliceOpF` with the level `τ_p = R_p²`.
* `instKmax`: `κ(x, x) ≤ d` on the unit sphere.
* `instBbd`: `|b_j(x)| ≤ 1` on the unit sphere.
* `instTmin`, `instTauLe`: `49/100 ≤ E_p R_p²`, `R_p² ≤ 1`.
* `instQuadRep`: `PU 2 f0 T U r sc` is a quadratic in the sense of `QuadRep`.
-/

namespace BstLean.Part89

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part41 (Mono phiM frob Tens TSymm fval)
open BstLean.Part53 (radF53)
open BstLean.Part56 (UnitV lawRK phiB kJ KR tauR axialMeasure polarState polarPoint perpDir
  axialR axialS tailReconstruct)
open BstLean.Part56.Orth (residualFeature block_norm_pos)
open BstLean.Part78 (nsq frobH qfun zv)
open BstLean.Part86

/-! ## Kernel bounds on the unit sphere -/

section kernel

variable {n d : ℕ}

private lemma enum_exists89 {ι : Type*} {i : ℕ} (β : Sym ι i) :
    ∃ w : Fin i → ι, Finset.univ.val.map w = β.val := by
  have enum (b : Multiset ι) : ∃ (r : ℕ) (w : Fin r → ι),
      r = b.card ∧ Finset.univ.val.map w = b := by
    induction b using Quot.inductionOn with
    | h a => exact ⟨a.length, a.get, rfl, by simp [Fin.univ_val_map]⟩
  obtain ⟨r, w, hr, hw⟩ := enum β.val
  have hri : r = i := hr.trans β.property
  clear hr
  subst r
  exact ⟨w, hw⟩

/-- One degree level of the monomial vector has squared norm `≤ 1` on the unit sphere. -/
lemma level_le_one (x : Fin n → ℝ) (hx : ∑ a, x a ^ 2 = 1) (i : ℕ) :
    (∑ β : Sym (Fin n) i, BstLean.Part36.monoVal x β.val ^ 2) ≤ 1 := by
  classical
  choose e he using fun β : Sym (Fin n) i => enum_exists89 β
  have hinj : Function.Injective e := by
    intro β γ h
    apply Subtype.ext
    rw [← he β, ← he γ, h]
  have hm : ∀ β : Sym (Fin n) i, BstLean.Part36.monoVal x β.val = ∏ t, x (e β t) := by
    intro β
    rw [BstLean.Part36.monoVal, ← he β, Multiset.map_map]
    rfl
  calc
    _ = ∑ β : Sym (Fin n) i, ∏ t, x (e β t) ^ 2 := by
      apply Finset.sum_congr rfl
      intro β _
      rw [hm, Finset.prod_pow]
    _ ≤ ∑ w : Fin i → Fin n, ∏ t, x (w t) ^ 2 := by
      calc
        _ = ∑ w ∈ Finset.univ.image e, ∏ t, x (w t) ^ 2 := by
          rw [Finset.sum_image (fun β _ γ _ h => hinj h)]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun w _ _ => Finset.prod_nonneg (fun t _ => sq_nonneg _))
    _ = ∏ _t : Fin i, ∑ a : Fin n, x a ^ 2 :=
      (Fintype.prod_sum (fun (_ : Fin i) (a : Fin n) => x a ^ 2)).symm
    _ = 1 := by simp [hx]

/-- `k_j(x, x) ≤ 1` on the unit sphere. -/
lemma kJ_self_le_one (d j : ℕ) (x : Fin n → ℝ) (hx : ∑ a, x a ^ 2 = 1) : kJ d j x x ≤ 1 := by
  classical
  unfold kJ
  rw [Fintype.sum_sigma]
  have hb : ∀ i : Fin (d + 1), (∑ β : Sym (Fin n) i,
      phiB d j x ⟨i, β⟩ * phiB d j x ⟨i, β⟩) ≤ if (i : ℕ) = j then 1 else 0 := by
    intro i
    by_cases h : (i : ℕ) = j
    · simp only [h, ite_true]
      refine le_trans (le_of_eq ?_) (level_le_one x hx i)
      apply Finset.sum_congr rfl
      intro β _
      simp only [phiB, h, ite_true, phiM]
      ring
    · simp only [h, ite_false]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro β _
      simp [phiB, h]
  refine (Finset.sum_le_sum fun i _ => hb i).trans ?_
  rw [Finset.sum_boole]
  have hc : (Finset.univ.filter fun i : Fin (d + 1) => (i : ℕ) = j).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb'
    exact Fin.ext (ha.trans hb'.symm)
  exact_mod_cast hc

lemma kJ_self_nonneg (d j : ℕ) (x : Fin n → ℝ) : 0 ≤ kJ d j x x := by
  unfold kJ
  exact Finset.sum_nonneg fun p _ => mul_self_nonneg _

lemma kJ_cs (d j : ℕ) (x v : Fin n → ℝ) : kJ d j x v ^ 2 ≤ kJ d j x x * kJ d j v v := by
  classical
  simpa only [kJ, pow_two] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (phiB d j x) (phiB d j v)

/-- `K_R(x, x) ≤ d` on the unit sphere. -/
lemma KR_self_le (d : ℕ) (v x : Fin n → ℝ) (hx : ∑ a, x a ^ 2 = 1) : KR d v x x ≤ (d : ℝ) := by
  unfold KR
  have h : ∀ j ∈ Finset.Icc 1 d, kJ d j x x - kJ d j x v * kJ d j x v / kJ d j v v ≤ 1 := by
    intro j _
    have h1 := kJ_self_le_one d j x hx
    have h2 : 0 ≤ kJ d j x v * kJ d j x v / kJ d j v v :=
      div_nonneg (mul_self_nonneg _) (kJ_self_nonneg d j v)
    linarith
  refine (Finset.sum_le_sum h).trans ?_
  simp

end kernel

/-! ## Axial facts -/

lemma axial_sq_eq (a r : ℝ) (ha : a ≠ 0) : axialS a r ^ 2 + axialR a r ^ 2 = 1 := by
  unfold axialS axialR
  have hp : 0 < a ^ 2 + r ^ 2 := by positivity
  rw [div_pow, div_pow, Real.sq_sqrt hp.le, ← add_div, div_self hp.ne']

lemma measurable_tauF (m : ℕ) :
    Measurable (fun p : ℝ × (Fin m → ℝ) => axialR p.1 (radF53 p.2) ^ 2) := by
  unfold axialR radF53
  fun_prop

lemma measurable_sF (m : ℕ) :
    Measurable (fun p : ℝ × (Fin m → ℝ) => axialS p.1 (radF53 p.2) ^ 2) := by
  unfold axialS radF53
  fun_prop

/-- The axial coordinate is nonzero for almost every slice. -/
lemma axial_ne_zero {m : ℕ} (t : ℝ) (v : Fin (m + 1) → ℝ) :
    ∀ᵐ p ∂axialMeasure t v, p.1 ≠ 0 := by
  have hbase : ∀ᵐ p ∂((ProbabilityTheory.gaussianReal 0 1).prod (stdGauss (Fin m))),
      p.1 ≠ 0 := by
    rw [ae_iff]
    have e : {p : ℝ × (Fin m → ℝ) | ¬ p.1 ≠ 0} = ({0} : Set ℝ) ×ˢ (Set.univ : Set (Fin m → ℝ)) := by
      ext p
      simp
    rw [e, Measure.prod_prod]
    have : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
      ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num)
    rw [measure_singleton, zero_mul]
  unfold axialMeasure
  exact (withDensity_absolutelyContinuous _ _).ae_le hbase

/-- The perpendicular direction is a unit vector, for almost every `g`. -/
lemma perp_unit {m : ℕ} (hm : 1 ≤ m) (v : Fin (m + 1) → ℝ) (hv : UnitV v) :
    ∀ᵐ g ∂stdGauss (Fin (m + 1)), ∑ i, perpDir v g i ^ 2 = 1 := by
  obtain ⟨b, hb⟩ := BstLean.Part56.unit_basis_exists (m + 1) (by omega) v hv
  have hb0 : b 0 = WithLp.toLp 2 v := hb
  have hset : MeasurableSet {w : Fin (m + 1) → ℝ | ∑ i, w i ^ 2 = 1} := by
    apply IsClosed.measurableSet
    exact isClosed_eq (by fun_prop) continuous_const
  have hae : ∀ᵐ w ∂((stdGauss (Fin (m + 1))).map (perpDir v)), ∑ i, w i ^ 2 = 1 := by
    rw [XSliceOp.perp_map b hm v hb0]
    rw [ae_map_iff (XSliceOp.continuous_tail b).measurable.aemeasurable hset]
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere m] with ω hω
    rw [BstLean.Part56.tailReconstruct_sumsq, hω]
  exact ae_of_ae_map (BstLean.Part56.measurable_perpDir56 v).aemeasurable hae

/-! ## The facts of the instance -/

section inst

variable (m d : ℕ) (t : ℝ) (v : Fin (m + 1) → ℝ) (E : JR (m + 1) d → Mono (m + 1) d → ℝ)

/-- (i) The points of the model are on the unit sphere, almost surely. -/
theorem instSph (hm : 1 ≤ m) (hv : UnitV v) :
    ∀ᵐ p ∂(modRK m d t v E).pi, ∀ᵐ g ∂(modRK m d t v E).ga,
      ∑ i, (modRK m d t v E).X (p, g) i ^ 2 = 1 := by
  change ∀ᵐ p ∂axialMeasure t v, ∀ᵐ g ∂stdGauss (Fin (m + 1)),
    ∑ i, polarState v (p, g) i ^ 2 = 1
  filter_upwards [axial_ne_zero t v] with p hp
  filter_upwards [perp_unit hm v hv] with g hg
  have e : polarState v (p, g) = axialS p.1 (radF53 p.2) • v +
      axialR p.1 (radF53 p.2) • perpDir v g := rfl
  rw [e, XInst.comb_sq, BstLean.Part56.perpDir_orth56 v g hv, hg]
  have h1 : ∑ i, v i ^ 2 = 1 := hv
  rw [h1]
  have := axial_sq_eq p.1 (radF53 p.2) hp
  linarith

/-- (ii) The slice feature operator bound with the level `τ_p = R_p²`. -/
theorem instSliceOpF (hd : 1 ≤ d) (hm : 5000 ≤ m) (hv : UnitV v) (hE : RotE v E) :
    SliceOpF (modRK m d t v E) (CLs d / (m : ℝ)) (fun p => axialR p.1 (radF53 p.2) ^ 2) := by
  have hK := rot_KR v hv E hE
  have hres := rot_resid v E hE
  have hOp : SliceOpRK m d (CLs d) := XSliceOp.sliceOpRK_fact m d hd hm
  refine ⟨measurable_tauF m, fun p => ?_⟩
  obtain ⟨hτ, hop⟩ := hOp v hv p.1 (radF53 p.2) (Real.sqrt_nonneg _)
  refine ⟨sq_nonneg _, ?_, ?_⟩
  · change ∀ᵐ g ∂stdGauss (Fin (m + 1)), _
    filter_upwards [hτ] with g hg
    have e : kapm (modRK m d t v E) (polarPoint v (perpDir v g) p.1 (radF53 p.2))
        (polarPoint v (perpDir v g) p.1 (radF53 p.2)) =
        tauR d v (polarPoint v (perpDir v g) p.1 (radF53 p.2)) := hK _ _
    change _ ≤ kapm (modRK m d t v E) (polarPoint v (perpDir v g) p.1 (radF53 p.2))
        (polarPoint v (perpDir v g) p.1 (radF53 p.2))
    rw [e]; exact hg
  · intro c
    obtain ⟨c', hc', hcx⟩ := hres c
    have h := hop c'
    rw [hc'] at h
    have e : ∀ g : Fin (m + 1) → ℝ,
        (∑ q, c q * (modRK m d t v E).ps ((modRK m d t v E).X (p, g)) q) =
          ∑ p', c' p' * residualFeature v (polarPoint v (perpDir v g) p.1 (radF53 p.2)) p' :=
      fun g => hcx _
    simp only [e]
    exact h

/-- (iii) `κ(x, x) ≤ d` on the unit sphere. -/
theorem instKmax (hv : UnitV v) (hE : RotE v E) :
    ∀ x : Fin (m + 1) → ℝ, ∑ i, x i ^ 2 = 1 → kapm (modRK m d t v E) x x ≤ (d : ℝ) := by
  intro x hx
  have e : kapm (modRK m d t v E) x x = KR d v x x := rot_KR v hv E hE x x
  rw [e]
  exact KR_self_le d v x hx

/-- (iv) `|b_j(x)| ≤ 1` on the unit sphere. -/
theorem instBbd :
    ∀ x : Fin (m + 1) → ℝ, ∑ i, x i ^ 2 = 1 → ∀ j, |(modRK m d t v E).b x j| ≤ 1 := by
  intro x hx j
  have e : (modRK m d t v E).b x j = kJ d j x v / Real.sqrt (kJ d j v v) :=
    XIdent.eval_bPE v x j
  rw [e]
  have hvv := kJ_self_nonneg d j v
  by_cases hz : kJ d j v v = 0
  · simp [hz]
  · have hp : 0 < kJ d j v v := lt_of_le_of_ne hvv (Ne.symm hz)
    have hs : 0 < Real.sqrt (kJ d j v v) := Real.sqrt_pos.mpr hp
    rw [abs_div, abs_of_pos hs, div_le_one hs]
    apply Real.abs_le_sqrt
    have h1 := kJ_cs d j x v
    have h2 := kJ_self_le_one d j x hx
    nlinarith

/-- (v) `R_p² ≤ 1`. -/
theorem instTauLe (m : ℕ) : ∀ p : ℝ × (Fin m → ℝ), axialR p.1 (radF53 p.2) ^ 2 ≤ 1 := by
  intro p
  have h := XInst.axial_sq_le p.1 (radF53 p.2)
  have := sq_nonneg (axialS p.1 (radF53 p.2))
  linarith

/-- (v) `49/100 ≤ E_p R_p²`. -/
theorem instTmin (hm : 100 ≤ m + 1) (hv : UnitV v) (ht0 : 0 ≤ t)
    (htn : t ≤ ((m + 1 : ℕ) : ℝ)) :
    49 / 100 ≤ ∫ p, axialR p.1 (radF53 p.2) ^ 2 ∂axialMeasure t v := by
  obtain ⟨b, hb⟩ := BstLean.Part56.unit_basis_exists (m + 1) (by omega) v hv
  have hb0 : b 0 = WithLp.toLp 2 v := hb
  have : IsProbabilityMeasure (axialMeasure t v) :=
    BstLean.Part56.axialMeasure_probability b v hb0 t
  have hlow := BstLean.Part80.pLowRK_sharp (m + 1) (by omega) v hv t ht0 htn
  have hsl := XIdent.lawRK_integral_slices t v hv (fun x => (∑ i, v i * x i) ^ 2) (by fun_prop)
  have hdot : ∀ (p : ℝ × (Fin m → ℝ)) (g : Fin (m + 1) → ℝ),
      (∑ i, v i * polarState v (p, g) i) ^ 2 = axialS p.1 (radF53 p.2) ^ 2 := by
    intro p g
    have e : polarState v (p, g) = axialS p.1 (radF53 p.2) • v +
        axialR p.1 (radF53 p.2) • perpDir v g := rfl
    have h1 : ∑ i, v i ^ 2 = 1 := hv
    have h2 := BstLean.Part56.perpDir_orth56 v g hv
    have h3 : ∑ i, v i * polarState v (p, g) i =
        axialS p.1 (radF53 p.2) * ∑ i, v i ^ 2 +
          axialR p.1 (radF53 p.2) * ∑ i, v i * perpDir v g i := by
      rw [e, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h3, h1, h2]
    ring
  simp only [hdot, integral_const, probReal_univ, one_smul] at hsl
  rw [hsl] at hlow
  have hSint : Integrable (fun p : ℝ × (Fin m → ℝ) => axialS p.1 (radF53 p.2) ^ 2)
      (axialMeasure t v) :=
    XInst.int_bdd _ _ (measurable_sF m) 1 fun p => by
      rw [abs_of_nonneg (sq_nonneg _)]
      have h := XInst.axial_sq_le p.1 (radF53 p.2)
      have := sq_nonneg (axialR p.1 (radF53 p.2))
      linarith
  have hcong : ∫ p, axialR p.1 (radF53 p.2) ^ 2 ∂axialMeasure t v =
      ∫ p, (1 - axialS p.1 (radF53 p.2) ^ 2) ∂axialMeasure t v := by
    apply integral_congr_ae
    filter_upwards [axial_ne_zero t v] with p hp
    have := axial_sq_eq p.1 (radF53 p.2) hp
    linarith
  rw [hcong, integral_sub (integrable_const _) hSint]
  simp only [integral_const, probReal_univ, one_smul]
  have hm' : (100 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hm
  have h100 : 1 / ((m + 1 : ℕ) : ℝ) ≤ 1 / 100 :=
    one_div_le_one_div_of_le (by norm_num) hm'
  norm_num at h100 hlow ⊢
  linarith

/-- (vi) `PU 2 f0 T U r sc` is the quadratic `qfun f0 ℓ H` at the anchors `U_j / r`. -/
theorem instQuadRep :
    ∀ (f0 : ℝ) (T : Tens (m + 1)), TSymm 2 T →
      ∃ (ℓ : Fin (m + 1) → ℝ) (H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ),
        H.IsSymm ∧ frobH H = frob (T 2) ∧
        ∀ (U : Fin (d + 1) × Fin (m + 1) → ℝ) (r sc : ℝ),
          QuadRep (modRK m d t v E) (PU 2 f0 T U r sc) f0 ℓ H (fun j i => U (j, i) / r) sc := by
  intro f0 T hT
  obtain ⟨ℓ, H, hsym, hq, hfrob, -⟩ := BstLean.Part80.tensBridge (m + 1) f0 T hT
  refine ⟨ℓ, H, hsym, hfrob, ?_⟩
  intro U r sc lam W x
  rw [XIdent.Fm_PU, hq]
  congr 1
  funext i
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · ring

end inst

end BstLean.Part89

#print axioms BstLean.Part89.instSph
#print axioms BstLean.Part89.instSliceOpF
#print axioms BstLean.Part89.instKmax
#print axioms BstLean.Part89.instBbd
#print axioms BstLean.Part89.instTauLe
#print axioms BstLean.Part89.instTmin
#print axioms BstLean.Part89.instQuadRep
