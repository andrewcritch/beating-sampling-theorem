import BstLean.Part222Mass
import BstLean.Part219Rotation

/-! The same order-24 gradient event supplies every even mass order through twenty-four. -/
namespace BstLean.Part222
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part188

theorem directional_moment_even {n p : ℕ} (hn : 50 ≤ n) (hp : 1 ≤ p) (hp12 : p ≤ 12)
    (D : Design n) (c : Ret n) (hτ : 0 < D.tau0 c)
    (hb : 0 < normSq (D.bA c.1 c.2.1.1)) {M : ℝ} (hM : DirectionMoment D c M) :
    Integrable (fun ξ => |centreCoordinate D c ξ-
      ∫ ζ, centreCoordinate D c ζ ∂stdGauss (Fin n)|^(2*p)) (stdGauss (Fin n)) ∧
    (∫ ξ, |centreCoordinate D c ξ-
      ∫ ζ, centreCoordinate D c ζ ∂stdGauss (Fin n)|^(2*p) ∂stdGauss (Fin n)) ≤
      BstLean.Part195.rotationConstant p^(2*p)*(M/n)^p := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  let f := centreCoordinate D c
  let g := fun ξ => √(BstLean.Part151.gradSq f ξ)
  have mg : Measurable g := (BstLean.Part151.measurable_gradSq f).sqrt
  have hg0 : ∀ ξ, 0 ≤ g ξ := fun ξ => sqrt_nonneg _
  have hmn : 0 ≤ M/(n : ℝ) := div_nonneg hM.1 (Nat.cast_nonneg _)
  have eg : (fun ξ => g ξ^24) = (fun ξ => BstLean.Part151.gradSq f ξ^12) := by
    funext ξ
    dsimp [g]
    rw [show (24 : ℕ) = 2*12 from rfl, pow_mul, sq_sqrt (BstLean.Part151.gradSq_nonneg _ _)]
  have egx (ξ : Fin n → ℝ) : g ξ^24 = BstLean.Part151.gradSq f ξ^12 := congrFun eg ξ
  have hgn : eLpNorm g (24 : ℕ) (stdGauss (Fin n)) ≤ ENNReal.ofReal (√(M/n)) := by
    apply BstLean.Part219.norm_le_of_moment (p := 24) (by norm_num)
      mg.aestronglyMeasurable hg0 (sqrt_nonneg _)
    simp_rw [egx]
    rw [← ofReal_integral_eq_lintegral_ofReal hM.2.1
      (Filter.Eventually.of_forall fun ξ => pow_nonneg (BstLean.Part151.gradSq_nonneg _ _) _)]
    have he : √(M/(n : ℝ))^24 = (M/n)^12 := by
      rw [show (24 : ℕ) = 2*12 from rfl, pow_mul, sq_sqrt hmn]
    rw [he]
    exact ENNReal.ofReal_le_ofReal hM.2.2
  have hgp : eLpNorm g (2*p : ℕ) (stdGauss (Fin n)) ≤ ENNReal.ofReal (√(M/n)) :=
    (eLpNorm_le_eLpNorm_of_exponent_le (by exact_mod_cast (show 2*p ≤ 24 by omega))).trans hgn
  obtain ⟨hgi,hgb⟩ := BstLean.Part219.moment_of_norm (p := 2*p) (by omega)
    mg.aestronglyMeasurable hg0 (sqrt_nonneg _) hgp
  have egp : (fun ξ => g ξ^(2*p)) = (fun ξ => BstLean.Part151.gradSq f ξ^p) := by
    funext ξ
    dsimp [g]
    rw [pow_mul, sq_sqrt (BstLean.Part151.gradSq_nonneg _ _)]
  rw [egp] at hgi hgb
  have hs : √(M/(n : ℝ))^(2*p) = (M/n)^p := by rw [pow_mul, sq_sqrt hmn]
  rw [hs] at hgb
  have hf24 := (centreCoordinate_moment24 hn D c hτ hb hM).1
  have mf : AEStronglyMeasurable (fun ξ => f ξ-∫ ζ, f ζ ∂stdGauss (Fin n))
      (stdGauss (Fin n)) := ((measurable_centreCoordinate D c).sub measurable_const).aestronglyMeasurable
  have hfmem : MemLp (fun ξ => f ξ-∫ ζ, f ζ ∂stdGauss (Fin n)) (24 : ℕ) (stdGauss (Fin n)) := by
    apply (integrable_norm_rpow_iff mf (by norm_num : ((24 : ℕ) : ℝ≥0∞) ≠ 0)
      (ENNReal.natCast_ne_top _)).1
    simpa only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs] using hf24
  have hfmemP := hfmem.mono_exponent (show ((2*p : ℕ) : ℝ≥0∞) ≤ (24 : ℕ) by
    exact_mod_cast (show 2*p ≤ 24 by omega))
  have hfi := hfmemP.integrable_norm_pow (by omega : 2*p ≠ 0)
  refine ⟨by simpa only [Real.norm_eq_abs] using hfi, ?_⟩
  have hr := BstLean.Part195.centreCoordinate_even hp (by omega) D c hτ hb hgi
  exact hr.trans (mul_le_mul_of_nonneg_left hgb
    (pow_nonneg (BstLean.Part195.rotationConstant_nonneg p) _))

noncomputable def massBoundOrder (n p : ℕ) (M H xi E u d : ℝ) : ℝ :=
  (n : ℝ)*((H/u)^32+
    (BstLean.Part195.rotationConstant p^(2*p)*(M/n)^p)/
      (√((1-u)^2-d)-(√E+√(xi/n)))^(2*p))

/-- The energy tail and the directional tail bound the actual residual cutoff set. -/
theorem sharp_residual_mass_order {n p : ℕ} (hn : 50 ≤ n) (hp : 1 ≤ p) (hp12 : p ≤ 12)
    (D : Design n) (c : Ret n) (hτ : 0 < D.tau0 c)
    (hb : 0 < normSq (D.bA c.1 c.2.1.1))
    (hb0 : ∀ j, 0 ≤ D.bA c.1 c.2.1.1 j) {M H xi E u d : ℝ}
    (hI : WFInterfaces D c M H xi) (hE : centreEnergy D c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : d < (1-u)^2)
    (hgap : 0 < √((1-u)^2-d)-(√E+√(xi/n))) :
    BstLean.Part160.MASS_at D c d (massBoundOrder n p M H xi E u d) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  let μ := stdGauss (Fin n)
  let q := √E+√(xi/(n : ℝ))
  let g := √((1-u)^2-d)-q
  have hsub : {ξ | ¬ goodInput ((1-u)^2) d (inputEnergy D c ξ) (centreCoordinate D c ξ)} ⊆
      {ξ | u ≤ |√(inputEnergy D c ξ)-1|} ∪
      {ξ | g ≤ |centreCoordinate D c ξ-∫ ζ, centreCoordinate D c ζ ∂μ|} := by
    intro ξ hξ
    by_cases he : u ≤ |√(inputEnergy D c ξ)-1|
    · exact Or.inl he
    · right
      have hclose := (abs_lt.mp (not_le.mp he)).1
      have he0 := inputEnergy_nonneg D c ξ
      have hs := sq_sqrt he0
      have hlow : (1-u)^2 ≤ inputEnergy D c ξ := by
        nlinarith [sqrt_nonneg (inputEnergy D c ξ)]
      have hbad : (1-u)^2-d < centreCoordinate D c ξ^2 := by
        by_contra h
        exact hξ ⟨hlow, not_lt.mp h⟩
      have hf0 := centreCoordinate_nonneg D c hb0 ξ
      have ht : √((1-u)^2-d) < centreCoordinate D c ξ := by
        nlinarith [sqrt_nonneg ((1-u)^2-d), sq_sqrt (by linarith : 0 ≤ (1-u)^2-d)]
      have hm : (∫ ζ, centreCoordinate D c ζ ∂μ) ≤ q := by
        have hp := (abs_le.mp hI.parallel.2).2
        have hs := sqrt_le_sqrt hE
        dsimp [q, μ]
        linarith
      exact (show g ≤ centreCoordinate D c ξ-∫ ζ, centreCoordinate D c ζ ∂μ by
        dsimp [g]; linarith).trans (le_abs_self _)
  have he : (fun ξ => |√(inputEnergy D c ξ)-1|^32) =
      (fun ξ => (√(inputEnergy D c ξ)-1)^32) := by
    funext ξ
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hiE := hI.energy.2.1
  have hmE := hI.energy.2.2
  rw [← he] at hiE hmE
  have hEt := moment_tail μ (fun ξ => √(inputEnergy D c ξ)-1) 32 hu hiE hmE
  have hf := directional_moment_even hn hp hp12 D c hτ hb hI.direction
  have hFt := moment_tail μ (fun ξ => centreCoordinate D c ξ-∫ ζ, centreCoordinate D c ζ ∂μ)
    (2*p) hgap hf.1 hf.2
  have hmass := (measureReal_mono hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add hEt hFt))
  rw [div_pow] at hmass
  apply MASS_at_of_good_complement (a := (1-u)^2) (by omega) D c (ne_of_gt hb)
  simpa only [massBoundOrder, div_pow] using
    mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

#print axioms directional_moment_even
#print axioms sharp_residual_mass_order
end BstLean.Part222
