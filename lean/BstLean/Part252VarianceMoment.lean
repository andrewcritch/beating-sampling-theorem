import BstLean.Part252Variance
import BstLean.Part212Fields

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_of_latitude {n : ℕ} (hn : 26 ≤ n) (c : Ret n)
    (he : 0 < eR c) {C : ℝ} (hC : 0 < C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) (K : Set (Ix n)) :
    ∫ a in K, ((n : ℝ) * VR c a) ^ 2 ∂muI n ≤ (C / ((n : ℝ) - 3)) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb : normSq (bR c) ≠ 0 := by
    intro h
    unfold eR at he
    rw [h, zero_div] at he
    exact (lt_irrefl 0 he)
  set Vl : Ix n → ℝ := fun a => ∫ v, (lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) -
    ∫ w, lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2 ∂stdGauss (Fin (n - 1)) with hVl
  have hVe : ∀ a, VR c a = eR c * Vl a := by
    intro a
    have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
    obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
    have hV := VR_eq hn1 c hb a
    rw [fbR_eq] at hV
    unfold fbarS at hV
    rw [← var_eq i1 i2] at hV
    rw [hV, hVl]
    simp only [fX_eq_lam c]
    have hin : ∫ w, √(eR c) * lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a)
        (unitF53 w)) ∂stdGauss (Fin (n - 1)) = √(eR c) * ∫ w, lamX (paperDesignP n) c
          (xLat c (latC (paperDesignP n) c a) (unitF53 w)) ∂stdGauss (Fin (n - 1)) :=
      integral_const_mul _ _
    rw [hin]
    have e2 : ∀ v, (√(eR c) * lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a)
        (unitF53 v)) - √(eR c) * ∫ w, lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a)
          (unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2 =
        eR c * (lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) -
          ∫ w, lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 w))
            ∂stdGauss (Fin (n - 1))) ^ 2 := by
      intro v; rw [← mul_sub, mul_pow, Real.sq_sqrt he.le]
    simp only [e2]
    exact integral_const_mul _ _
  have hcert := BstLean.Part212.fresh_LG_variance_lambda hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  change √(∫ a, Vl a ^ 2 ∂muI n) ≤ (C / eR c) / ((n : ℝ) * ((n : ℝ) - 3)) at hcert
  have hint : ∫ a, Vl a ^ 2 ∂muI n ≤ ((C / eR c) / ((n : ℝ) * ((n : ℝ) - 3))) ^ 2 :=
    (sqrt_le_iff.mp hcert).2
  obtain ⟨MV, bV⟩ := bdd_VR hn1 c
  have iV : Integrable (fun a => ((n : ℝ) * VR c a) ^ 2) (muI n) := by
    have hh := intOn_of_bdd (((measurable_VR c).const_mul (n : ℝ)).pow_const 2)
      (bdd_pow (bdd_nmul bV) 2) Set.univ
    simpa only [IntegrableOn, Measure.restrict_univ] using hh
  refine (setIntegral_le_integral iV
    (Filter.Eventually.of_forall fun a => sq_nonneg ((n : ℝ) * VR c a))).trans ?_
  have hid : (fun a => ((n : ℝ) * VR c a) ^ 2) =
      fun a => ((n : ℝ) * eR c) ^ 2 * Vl a ^ 2 := by
    funext a
    rw [hVe a]
    ring
  rw [hid, integral_const_mul]
  refine (mul_le_mul_of_nonneg_left hint (sq_nonneg _)).trans_eq ?_
  field_simp
  <;> ring

theorem variance_moment_row (c : Ret 12225) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12225) c ∈ BstLean.Part212.latitudeEvent 12225
      (ENNReal.ofReal (C / 12225))) (K : Set (Ix 12225)) :
    ∫ a in K, ((12225 : ℝ) * VR c a) ^ 2 ∂muI 12225 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part252
