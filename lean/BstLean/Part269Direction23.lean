import BstLean.Part182SNum
import BstLean.Part253DirectionConstants
import BstLean.Part264Direction
import BstLean.Part264DirectionError

/-! The actual Part219 direction error has a rational upper bound. -/
namespace BstLean.Part269.D23
open BstLean.Part253
open Real BstLean.Part152 BstLean.Part209

theorem sqrtN_upper : √(12925 : ℝ) ≤ 113.6881700091 := sqrt_le_iff.mpr (by norm_num)
theorem sqrt2_upper : √(2 : ℝ) ≤ 1.414213563 := sqrt_le_iff.mpr (by norm_num)
theorem sqrt2_lower : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
theorem sqrt32_upper : √(32 : ℝ) ≤ 5.65685425 := sqrt_le_iff.mpr (by norm_num)

theorem length_upper (P : ℕ) {b B : ℝ} (hb : twoGaussConst P ≤ b)
    (hnum : 2 / (12925 : ℝ) ^ 2 + 1.414213563 / 12925 * b ≤ B) :
    lengthAlpha 12925 P ≤ B := by
  unfold lengthAlpha
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hnum
  have h0 := twoGaussConst_nonneg P
  gcongr
  exact sqrt2_upper

theorem length16_upper : lengthAlpha 12925 16 ≤ 0.0004123715 :=
  length_upper 16 two16_upper (by norm_num)
theorem length32_upper : lengthAlpha 12925 32 ≤ 0.0005594388 :=
  length_upper 32 two32_upper (by norm_num)
theorem length64_upper : lengthAlpha 12925 64 ≤ 0.0007728202 :=
  length_upper 64 two64_upper (by norm_num)
theorem length128_upper : lengthAlpha 12925 128 ≤ 0.0010787321 :=
  length_upper 128 two128_upper (by norm_num)

theorem pairQ_upper : pairQ 12925 32 ≤ 0.0129999992 := by
  have h0 := gaussMomConst_nonneg 32
  have hs := sqrtN_upper
  have hs2 := sqrt2_lower
  have hg := gauss32_upper
  unfold pairQ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 / (12925 : ℝ) ^ 2 * (113.6881700091 + 5.05772465) *
        (12925 / 1.414213562 + 5.05772465) := by gcongr
    _ ≤ (0.0129999992 : ℝ) := by norm_num

theorem pairPlane_upper : pairPlane 12925 32 ≤ 618537.2327818977 := by
  have hs := sqrt32_upper
  have hl := log162_upper
  have h32 := factorial32_upper
  have h64 := factorial64_upper
  have hr : √(log (162 : ℝ) + factorialRoot 32) ≤ 4.22827381 := by
    apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · linarith
  unfold pairPlane
  simp only [Nat.cast_ofNat, Nat.reduceMul]
  calc
    _ ≤ 2 * 5.65685425 * (12925 : ℝ) * 4.22827381 +
        8 * (5.088 + 24.67407549) := by gcongr
    _ ≤ (618537.2327818977 : ℝ) := by norm_num

theorem pairV_upper : pairV 12925 32 ≤ 0.0204051642 := by
  unfold pairV
  have hq := pairQ_upper
  have hp := pairPlane_upper
  simp only [Nat.cast_ofNat]
  linarith

theorem overlap_upper : overlapC 12925 16 ≤ 0.0023332835 := by
  have hs := sqrt32_upper
  have h16 := overlap16_upper
  have h32 := overlap32_upper
  unfold overlapC
  simp only [Nat.cast_ofNat, Nat.reduceMul]
  rw [show (2 * (16 : ℝ)) = 32 by norm_num]
  calc
    _ ≤ 2 / (12925 : ℝ) ^ 2 *
        (5.65685425 * 12925 * 2.66487321 + 4 * 13.07036015) := by gcongr
    _ ≤ (0.0023332835 : ℝ) := by norm_num

theorem delta_upper : pairDelta 12925 16 (1 / 100) ≤ 0.0032224666 := by
  have ho := overlap_upper
  have h16 := length16_upper
  have h32 := length32_upper
  have h0 := lengthAlpha_nonneg 12925 32
  unfold pairDelta
  simp only [Nat.reduceMul]
  calc
    _ ≤ ((0.0023332835 : ℝ) + 2 * 0.0004123715 + 0.0005594388 ^ 2) / (1 - 1 / 100) ^ 2 := by
      gcongr
    _ ≤ (0.0032224666 : ℝ) := by norm_num

theorem tangent_upper (P : ℕ) {b g r B : ℝ}
    (hb : twoGaussConst P ≤ b) (hg : gaussMomConst (2 * P) ≤ g)
    (hr0 : 0 ≤ r) (hr : (12925 : ℝ) ^ 2 / 2 + 12925 / 2 * b ≤ r ^ 2)
    (hnum : 2 / (12925 : ℝ) ^ 2 * (r + 113.6881700091 + g) ^ 2 ≤ B) :
    tangentU 12925 P ≤ B := by
  have hs : √((12925 : ℝ) ^ 2 / 2 + activeB 12925 P) ≤ r := by
    apply sqrt_le_iff.mpr
    refine ⟨hr0, ?_⟩
    unfold activeB
    simp only [Nat.cast_ofNat]
    nlinarith
  have hn := sqrtN_upper
  have h0 := gaussMomConst_nonneg (2 * P)
  unfold tangentU
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hnum
  gcongr

theorem tangent32_upper : tangentU 12925 32 ≤ 1.0269913367 := by
  apply tangent_upper 32 two32_upper gauss64_upper (r := 9141.1626157619)
    <;> norm_num

theorem tangent64_upper : tangentU 12925 64 ≤ 1.0277669265 := by
  apply tangent_upper 64 two64_upper gauss128_upper (r := 9141.8519420720)
    <;> norm_num

theorem error_epsilon_upper : pairEpsilon 12925 16 (1 / 100) ≤ 0.0623535369 := by
  have hV := pairV_upper
  have hQ := pairQ_upper
  have hQ0 := pairQ_nonneg 12925 32
  have hV0 := pairV_nonneg 12925 32
  have hd : √(pairDelta 12925 16 (1 / 100)) ≤ 0.0567667738 :=
    sqrt_le_iff.mpr ⟨by norm_num, delta_upper.trans (by norm_num)⟩
  have ht32 : √(tangentU 12925 32) ≤ 1.0134058105 :=
    sqrt_le_iff.mpr ⟨by norm_num, tangent32_upper.trans (by norm_num)⟩
  have ht64 : √(tangentU 12925 64) ≤ 1.0137884033 :=
    sqrt_le_iff.mpr ⟨by norm_num, tangent64_upper.trans (by norm_num)⟩
  have hl64 := length64_upper
  have hl128 := length128_upper
  have hl0 := lengthAlpha_nonneg 12925 128
  have hrad : radialCoefficient (1 / 100) ≤ 0.324741 := by
    unfold radialCoefficient
    apply (div_le_iff₀ (by positivity : 0 < π * (1 - 1 / 100))).mpr
    linarith [pi_gt_d6]
  have hr0 := radialCoefficient_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100)
    (by norm_num : (1 / 100 : ℝ) < 1)
  have hlow : lowLengthProb 12925 (1 / 100) ^ (1 / 128 : ℝ) ≤ (1 / 1000000 : ℝ) :=
    (Real.rpow_le_rpow (by unfold lowLengthProb; positivity)
      (BstLean.Part264.lowLengthProb_le (by norm_num : 12225 ≤ 12925))
      (by norm_num : (0 : ℝ) ≤ 1 / 128)).trans BstLean.Part253.low_length_root
  have hlow0 : 0 ≤ lowLengthProb 12925 (1 / 100) ^ (1 / 128 : ℝ) :=
    rpow_nonneg (by unfold lowLengthProb; positivity) _
  have hcomp : complementB 12925 16 (1 / 100) ≤
      (1.0137884033 * (1 + 0.0010787321) + 1) * (1 / 1000000 : ℝ) := by
    unfold complementB complementRoot
    simp only [Nat.reduceMul, Nat.cast_ofNat]
    rw [show (8 * (16 : ℝ)) = 128 by norm_num]
    gcongr
  have hfluc : fluctuationRoot 12925 16 ≤
      (0.0204051642 : ℝ) * 1.0134058105 * (1 + 0.0007728202) := by
    have hl640 := lengthAlpha_nonneg 12925 64
    have hprod := mul_le_mul hV ht32 (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 0.0204051642)
    have hh := mul_le_mul hprod (add_le_add (le_refl (1 : ℝ)) hl64)
      (by linarith : (0 : ℝ) ≤ 1 + lengthAlpha 12925 64) (by norm_num)
    simpa only [fluctuationRoot, Nat.reduceMul] using hh
  have hmean : meanEpsilon 12925 16 (1 / 100) ≤
      0.0204051642 + (3 / 10 : ℝ) * 0.0567667738 + 0.324741 * 0.0129999992 +
        (1.0137884033 * (1 + 0.0010787321) + 1) * (1 / 1000000) := by
    have hh := add_le_add (add_le_add (add_le_add hV
      (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 3 / 10)))
      (mul_le_mul hrad hQ hQ0 (by norm_num : (0 : ℝ) ≤ 0.324741))) hcomp
    simpa only [meanEpsilon, Nat.reduceMul] using hh
  unfold pairEpsilon
  linarith

end BstLean.Part269.D23

/-! Rational bounds for the deterministic Part219 ideal term. -/
namespace BstLean.Part269.D23
open BstLean.Part253
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part219 BstLean.Part215

theorem rotation24_upper : BstLean.Part195.rotationConstant 24 ≤ 6.7 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (48 : ℕ) ≠ 0) (by norm_num)
  have he := BstLean.Part195.rotationConstant_pow (by norm_num : 1 ≤ 24) (by norm_num)
  rw [he, BstLean.Part162.gmom_even]
  have hp := pi_lt_d20.le
  calc
    _ ≤ (3.14159265358979323847 / 2 : ℝ) ^ 48 *
        ∏ j ∈ Finset.range 24, (2 * j + 1 : ℝ) := by gcongr
    _ ≤ (6.7 : ℝ) ^ 48 := by norm_num [Finset.prod_range_succ]

theorem slope_upper {q Q K s B : ℝ} (hq : 0 ≤ q) (hQ : q ≤ Q) (hQ1 : Q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : 1 - Q ^ 2 ≤ s ^ 2)
    (hK : (s + Q * (3141593 / 2000000 +
      (Q + Q ^ 3 / 6 + 3 * Q ^ 5 / 40 + Q ^ 7 / 10))) / (3141592 / 1000000) ≤ K)
    (hK0 : 0 ≤ K) (hK1 : K ≤ 3 / 4)
    (hB : (1 / 2 + (K + K ^ 3 / 6 + 3 * K ^ 5 / 40 + K ^ 7 / 10) /
        (3141592 / 1000000)) *
      (1 / 2 + (Q + Q ^ 3 / 6 + 3 * Q ^ 5 / 40 + Q ^ 7 / 10) /
        (3141592 / 1000000)) ≤ B) : kernelSlope q ≤ B := by
  have hq1 : q ≤ 1 := hQ.trans (hQ1.trans (by norm_num))
  have hQ0 : 0 ≤ Q := hq.trans hQ
  have hkap : kappa q ≤ K :=
    ((kappa_monotoneOn ⟨by linarith, hq1⟩ ⟨by linarith, by linarith⟩ hQ).trans
      (sn_kappa_le hQ0 hQ1 (sqrt_le_iff.mpr ⟨hs, hsq⟩))).trans hK
  have hk0 := (kappa_mem (by linarith : -1 ≤ q) hq1).1
  have hk1 := (kappa_mem (by linarith : -1 ≤ q) hq1).2
  have h1 := (kdot_monotoneOn ⟨by linarith, hk1⟩ ⟨by linarith, by linarith⟩ hkap).trans
    (sn_kdot_le hK0 hK1)
  have h2 := (kdot_monotoneOn ⟨by linarith, hq1⟩ ⟨by linarith, by linarith⟩ hQ).trans
    (sn_kdot_le hQ0 hQ1)
  have he : kernelSlope q = kdot (kappa q) * kdot q := by
    unfold kernelSlope BstLean.Part145.kg kdot
    field_simp
    <;> ring
  rw [he]
  exact (mul_le_mul h1 h2 (kdot_nonneg _) ((kdot_nonneg _).trans h1)).trans hB

theorem radius_upper {θ b R : ℝ} (j : ℕ) (hθ : 0 ≤ θ) (hb : θ ≤ b)
    (hd : 0 < 1 - (2 * j + 2 : ℝ) * b / 12925)
    (hR : b / (1 - (2 * j + 2 : ℝ) * b / 12925) ≤ R) :
    radiusCoefficient 12925 j θ ≤ R := by
  unfold radiusCoefficient
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hR
  apply div_le_div₀ (hθ.trans hb) hb hd
  have hj : (0 : ℝ) ≤ 2 * j + 2 := by positivity
  nlinarith

theorem amplitude_upper {θ a b A : ℝ} (ha : a ≤ θ) (hb : θ ≤ b) (hb1 : b ≤ 1)
    (hd : 0 < 1 - 4 * b / 12925) (hA0 : 0 ≤ A)
    (hA : (1 - a) / (1 - 4 * b / 12925) ≤ A ^ 2) :
    paperAmplitude 12925 θ ≤ A := by
  unfold paperAmplitude
  apply sqrt_le_iff.mpr
  refine ⟨hA0, ?_⟩
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hA
  apply div_le_div₀ (by linarith : 0 ≤ 1 - a) (by linarith) hd
  linarith

/-- The remaining premises are rational bounds on the radius and slope terms. -/
theorem ideal_from_bounds {θ e A K R1 R4 R24 R48 R96 T : ℝ}
    (hθ : 0 ≤ θ) (he : 0.665 ≤ e) (hT : θ ≤ T) (hT0 : 0 ≤ T) (hT1 : T ≤ 0.54)
    (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hA : paperAmplitude 12925 θ ≤ A) (hK : kernelSlope (1 - θ) ≤ K)
    (h1 : radiusCoefficient 12925 1 θ ≤ R1)
    (h4 : radiusCoefficient 12925 4 θ ≤ R4)
    (h24 : radiusCoefficient 12925 24 θ ≤ R24)
    (h48 : radiusCoefficient 12925 48 θ ≤ R48)
    (h96 : radiusCoefficient 12925 96 θ ≤ R96)
    (hR1 : 0 ≤ R1) (hR4 : 0 ≤ R4) (hR24 : 0 ≤ R24)
    (hR48 : 0 ≤ R48) (hR96 : 0 ≤ R96)
    (hscalar : K * A * R48 * 1.001921 / 0.815475 +
      (77 / 100 : ℝ) * √R24 / 0.815475 *
        (√(R1 / 12925) + A * 6.7 * R96 * 1.003879 / 113.6881700090 +
          2 * ((T + √T * R4 * 1.000123) / 12925)) ≤ 0.2282055781) :
    paperIdeal 12925 θ e ≤ 0.2282055781 := by
  have hsE : (0.815475 : ℝ) ≤ √e := le_sqrt_of_sq_le (by linarith)
  have hsN : (113.6881700090 : ℝ) ≤ √12925 := le_sqrt_of_sq_le (by norm_num)
  have h47 : √(1 + 47 / (12925 : ℝ)) ≤ 1.001921 := sqrt_le_iff.mpr (by norm_num)
  have h95 : √(1 + 95 / (12925 : ℝ)) ≤ 1.003879 := sqrt_le_iff.mpr (by norm_num)
  have h3 : √(1 + 3 / (12925 : ℝ)) ≤ 1.000123 := sqrt_le_iff.mpr (by norm_num)
  have hr := rotation24_upper
  have hrad (j : ℕ) (hj : j ≤ 96) : 0 ≤ radiusCoefficient 12925 j θ := by
    unfold radiusCoefficient
    have hjR : (j : ℝ) ≤ 96 := by exact_mod_cast hj
    have hjc : (2 * j + 2 : ℝ) ≤ 194 := by linarith
    have hp := mul_le_mul hjc (hT.trans hT1) hθ (by norm_num : (0 : ℝ) ≤ 194)
    apply div_nonneg hθ
    simp only [Nat.cast_ofNat]
    nlinarith
  have hr1 := hrad 1 (by norm_num)
  have hr4 := hrad 4 (by norm_num)
  have hr24 := hrad 24 (by norm_num)
  have hr48 := hrad 48 (by norm_num)
  have hr96 := hrad 96 (by norm_num)
  have hslope := kernelSlope_nonneg (1 - θ)
  have hAmp : 0 ≤ paperAmplitude 12925 θ := by unfold paperAmplitude; positivity
  have hrot := BstLean.Part195.rotationConstant_nonneg 24
  unfold paperIdeal paperBias
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hscalar
  gcongr

end BstLean.Part269.D23

/-! The interval certificates bound the deterministic ideal term. -/
namespace BstLean.Part269.D23
open Real Set BstLean.Part219 BstLean.Part215

theorem idealCell0 {θ e : ℝ} (hw : θ ∈ Icc (0.47199 : ℝ) 0.4744)
    (he : 0.665 ≤ e) : paperIdeal 12925 θ e ≤ 0.2282055781 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12925 θ ≤ 0.7266963134 :=
    amplitude_upper hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : kernelSlope (1 - θ) ≤ 0.4852690657 := by
    apply slope_upper (Q := (0.52801 : ℝ)) (K := (0.6279022677 : ℝ)) (s := (0.8492381527 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12925 1 θ ≤ 0.4744696599 :=
    radius_upper 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12925 4 θ ≤ 0.4745741881 :=
    radius_upper 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12925 24 θ ≤ 0.4752722211 :=
    radius_upper 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12925 48 θ ≤ 0.4761125761 :=
    radius_upper 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12925 96 θ ≤ 0.4778022329 :=
    radius_upper 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.4752722211 : ℝ) ≤ 0.6893998993 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.4744696599 : ℝ) / 12925) ≤ 0.0060588326 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.4744 : ℝ) ≤ 0.6887670144 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.4852690657 : ℝ) * 0.7266963134 * 0.4761125761 * 1.001921 / 0.815475 +
        (77 / 100) * 0.6893998993 / 0.815475 *
          (0.0060588326 + 0.7266963134 * 6.7 * 0.4778022329 * 1.003879 / 113.6881700090 +
            2 * ((0.4744 + 0.6887670144 * 0.4745741881 * 1.000123) / 12925)) := by gcongr
    _ ≤ (0.2282055781 : ℝ) := by norm_num

theorem idealCell1 {θ e : ℝ} (hw : θ ∈ Icc (0.4744 : ℝ) 0.4816)
    (he : 0.665 ≤ e) : paperIdeal 12925 θ e ≤ 0.2282055781 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12925 θ ≤ 0.7250367918 :=
    amplitude_upper hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : kernelSlope (1 - θ) ≤ 0.4841628418 := by
    apply slope_upper (Q := (0.5256 : ℝ)) (K := (0.6262687782 : ℝ)) (s := (0.8507318262 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12925 1 θ ≤ 0.4816717906 :=
    radius_upper 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12925 4 θ ≤ 0.4817795165 :=
    radius_upper 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12925 24 θ ≤ 0.4824989226 :=
    radius_upper 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12925 48 θ ≤ 0.4833650510 :=
    radius_upper 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12925 96 θ ≤ 0.4851066701 :=
    radius_upper 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.4824989226 : ℝ) ≤ 0.6946214240 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.4816717906 : ℝ) / 12925) ≤ 0.0061046439 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.4816 : ℝ) ≤ 0.6939740630 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.4841628418 : ℝ) * 0.7250367918 * 0.4833650510 * 1.001921 / 0.815475 +
        (77 / 100) * 0.6946214240 / 0.815475 *
          (0.0061046439 + 0.7250367918 * 6.7 * 0.4851066701 * 1.003879 / 113.6881700090 +
            2 * ((0.4816 + 0.6939740630 * 0.4817795165 * 1.000123) / 12925)) := by gcongr
    _ ≤ (0.2282055781 : ℝ) := by norm_num

theorem idealCell2 {θ e : ℝ} (hw : θ ∈ Icc (0.4816 : ℝ) 0.4888)
    (he : 0.665 ≤ e) : paperIdeal 12925 θ e ≤ 0.2282055781 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12925 θ ≤ 0.7200544644 :=
    amplitude_upper hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : kernelSlope (1 - θ) ≤ 0.4808808001 := by
    apply slope_upper (Q := (0.5184 : ℝ)) (K := (0.6214020372 : ℝ)) (s := (0.8551382579 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12925 1 θ ≤ 0.4888739533 :=
    radius_upper 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12925 4 θ ≤ 0.4889849253 :=
    radius_upper 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12925 24 θ ≤ 0.4897260274 :=
    radius_upper 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12925 48 θ ≤ 0.4906183207 :=
    radius_upper 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12925 96 θ ≤ 0.4924126977 :=
    radius_upper 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.4897260274 : ℝ) ≤ 0.6998042780 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.4888739533 : ℝ) / 12925) ≤ 0.0061501142 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.4888 : ℝ) ≤ 0.6991423318 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.4808808001 : ℝ) * 0.7200544644 * 0.4906183207 * 1.001921 / 0.815475 +
        (77 / 100) * 0.6998042780 / 0.815475 *
          (0.0061501142 + 0.7200544644 * 6.7 * 0.4924126977 * 1.003879 / 113.6881700090 +
            2 * ((0.4888 + 0.6991423318 * 0.4889849253 * 1.000123) / 12925)) := by gcongr
    _ ≤ (0.2282055781 : ℝ) := by norm_num

theorem idealCell3 {θ e : ℝ} (hw : θ ∈ Icc (0.4888 : ℝ) 0.496)
    (he : 0.665 ≤ e) : paperIdeal 12925 θ e ≤ 0.2282055781 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12925 θ ≤ 0.7150373989 :=
    amplitude_upper hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : kernelSlope (1 - θ) ≤ 0.4776323653 := by
    apply slope_upper (Q := (0.5112 : ℝ)) (K := (0.6165552547 : ℝ)) (s := (0.8594617851 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12925 1 θ ≤ 0.4960761482 :=
    radius_upper 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12925 4 θ ≤ 0.4961904143 :=
    radius_upper 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12925 24 θ ≤ 0.4969535357 :=
    radius_upper 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12925 48 θ ≤ 0.4978723854 :=
    radius_upper 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12925 96 θ ≤ 0.4997203163 :=
    radius_upper 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.4969535357 : ℝ) ≤ 0.7049493143 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.4960761482 : ℝ) / 12925) ≤ 0.0061952509 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.496 : ℝ) ≤ 0.7042726745 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.4776323653 : ℝ) * 0.7150373989 * 0.4978723854 * 1.001921 / 0.815475 +
        (77 / 100) * 0.7049493143 / 0.815475 *
          (0.0061952509 + 0.7150373989 * 6.7 * 0.4997203163 * 1.003879 / 113.6881700090 +
            2 * ((0.496 + 0.7042726745 * 0.4961904143 * 1.000123) / 12925)) := by gcongr
    _ ≤ (0.2282055781 : ℝ) := by norm_num

end BstLean.Part269.D23

/-! The interval certificates bound the deterministic ideal term. -/
namespace BstLean.Part269.D23
open Real Set BstLean.Part219 BstLean.Part215

theorem idealCell4 {θ e : ℝ} (hw : θ ∈ Icc (0.496 : ℝ) 0.5032)
    (he : 0.665 ≤ e) : paperIdeal 12925 θ e ≤ 0.2282055781 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12925 θ ≤ 0.7099848589 :=
    amplitude_upper hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : kernelSlope (1 - θ) ≤ 0.4744167304 := by
    apply slope_upper (Q := (0.504 : ℝ)) (K := (0.6117282922 : ℝ)) (s := (0.8637036529 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12925 1 θ ≤ 0.5032783752 :=
    radius_upper 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12925 4 θ ≤ 0.5033959837 :=
    radius_upper 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12925 24 θ ≤ 0.5041814473 :=
    radius_upper 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12925 48 θ ≤ 0.5051272451 :=
    radius_upper 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12925 96 θ ≤ 0.5070295264 :=
    radius_upper 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.5041814473 : ℝ) ≤ 0.7100573550 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.5032783752 : ℝ) / 12925) ≤ 0.0062400614 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.5032 : ℝ) ≤ 0.7093659141 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.4744167304 : ℝ) * 0.7099848589 * 0.5051272451 * 1.001921 / 0.815475 +
        (77 / 100) * 0.7100573550 / 0.815475 *
          (0.0062400614 + 0.7099848589 * 6.7 * 0.5070295264 * 1.003879 / 113.6881700090 +
            2 * ((0.5032 + 0.7093659141 * 0.5033959837 * 1.000123) / 12925)) := by gcongr
    _ ≤ (0.2282055781 : ℝ) := by norm_num

theorem idealCell5 {θ e : ℝ} (hw : θ ∈ Icc (0.5032 : ℝ) 0.5104)
    (he : 0.665 ≤ e) : paperIdeal 12925 θ e ≤ 0.2282055781 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12925 θ ≤ 0.7048960815 :=
    amplitude_upper hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : kernelSlope (1 - θ) ≤ 0.4712331153 := by
    apply slope_upper (Q := (0.4968 : ℝ)) (K := (0.6069210150 : ℝ)) (s := (0.8678650587 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12925 1 θ ≤ 0.5104806343 :=
    radius_upper 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12925 4 θ ≤ 0.5106016334 :=
    radius_upper 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12925 24 θ ≤ 0.5114097623 :=
    radius_upper 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12925 48 θ ≤ 0.5123829001 :=
    radius_upper 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12925 96 θ ≤ 0.5143403285 :=
    radius_upper 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.5114097623 : ℝ) ≤ 0.7151291928 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.5104806343 : ℝ) / 12925) ≤ 0.0062845526 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.5104 : ℝ) ≤ 0.7144228440 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.4712331153 : ℝ) * 0.7048960815 * 0.5123829001 * 1.001921 / 0.815475 +
        (77 / 100) * 0.7151291928 / 0.815475 *
          (0.0062845526 + 0.7048960815 * 6.7 * 0.5143403285 * 1.003879 / 113.6881700090 +
            2 * ((0.5104 + 0.7144228440 * 0.5106016334 * 1.000123) / 12925)) := by gcongr
    _ ≤ (0.2282055781 : ℝ) := by norm_num

theorem idealCell6 {θ e : ℝ} (hw : θ ∈ Icc (0.5104 : ℝ) 0.5176)
    (he : 0.665 ≤ e) : paperIdeal 12925 θ e ≤ 0.2282055781 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12925 θ ≤ 0.6997702763 :=
    amplitude_upper hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : kernelSlope (1 - θ) ≤ 0.4680807664 := by
    apply slope_upper (Q := (0.4896 : ℝ)) (K := (0.6021332928 : ℝ)) (s := (0.8719471544 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12925 1 θ ≤ 0.5176829254 :=
    radius_upper 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12925 4 θ ≤ 0.5178073634 :=
    radius_upper 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12925 24 θ ≤ 0.5186384808 :=
    radius_upper 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12925 48 θ ≤ 0.5196393503 :=
    radius_upper 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12925 96 θ ≤ 0.5216527231 :=
    radius_upper 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.5186384808 : ℝ) ≤ 0.7201655927 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.5176829254 : ℝ) / 12925) ≤ 0.0063287312 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.5176 : ℝ) ≤ 0.7194442300 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.4680807664 : ℝ) * 0.6997702763 * 0.5196393503 * 1.001921 / 0.815475 +
        (77 / 100) * 0.7201655927 / 0.815475 *
          (0.0063287312 + 0.6997702763 * 6.7 * 0.5216527231 * 1.003879 / 113.6881700090 +
            2 * ((0.5176 + 0.7194442300 * 0.5178073634 * 1.000123) / 12925)) := by gcongr
    _ ≤ (0.2282055781 : ℝ) := by norm_num

theorem idealCell7 {θ e : ℝ} (hw : θ ∈ Icc (0.5176 : ℝ) 0.52358)
    (he : 0.665 ≤ e) : paperIdeal 12925 θ e ≤ 0.2282055781 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12925 θ ≤ 0.6946064923 :=
    amplitude_upper hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : kernelSlope (1 - θ) ≤ 0.4649589553 := by
    apply slope_upper (Q := (0.4824 : ℝ)) (K := (0.5973649992 : ℝ)) (s := (0.8759510489 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12925 1 θ ≤ 0.5236648528 :=
    radius_upper 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12925 4 θ ≤ 0.5237921835 :=
    radius_upper 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12925 24 θ ≤ 0.5246426399 :=
    radius_upper 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12925 48 θ ≤ 0.5256668401 :=
    radius_upper 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12925 96 θ ≤ 0.5277272840 :=
    radius_upper 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.5246426399 : ℝ) ≤ 0.7243221935 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.5236648528 : ℝ) / 12925) ≤ 0.0063651910 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.52358 : ℝ) ≤ 0.7235882808 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.4649589553 : ℝ) * 0.6946064923 * 0.5256668401 * 1.001921 / 0.815475 +
        (77 / 100) * 0.7243221935 / 0.815475 *
          (0.0063651910 + 0.6946064923 * 6.7 * 0.5277272840 * 1.003879 / 113.6881700090 +
            2 * ((0.52358 + 0.7235882808 * 0.5237921835 * 1.000123) / 12925)) := by gcongr
    _ ≤ (0.2282055781 : ℝ) := by norm_num

end BstLean.Part269.D23

/-! The actual pair error allowance decreases with dimension from 12925. -/
namespace BstLean.Part269.D23
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part209

theorem sqrt_div_self {x : ℝ} (hx : 0 < x) : √x / x = 1 / √x := by
  calc
    _ = √x / (√x)^2 := by rw [sq_sqrt hx.le]
    _ = _ := by field_simp

theorem pairQ_normalized {n : ℕ} (hn : 0 < n) (P : ℕ) :
    pairQ n P = 2 * (1 / √(n : ℝ) + gaussMomConst P / n) *
      (1 / √(2 : ℝ) + gaussMomConst P / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold pairQ
  calc
    _ = 2 * (√(n : ℝ) / n + gaussMomConst P / n) *
        (1 / √(2 : ℝ) + gaussMomConst P / n) := by field_simp
    _ = _ := by rw [sqrt_div_self hnR]

theorem tangentU_normalized {n : ℕ} (hn : 0 < n) (P : ℕ) :
    tangentU n P = 2 * (√((1 / 2 : ℝ) + twoGaussConst P / (2 * n)) +
      1 / √(n : ℝ) + gaussMomConst (2 * P) / n)^2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrad : √((n : ℝ)^2 / 2 + (n : ℝ) / 2 * twoGaussConst P) =
      (n : ℝ) * √((1 / 2 : ℝ) + twoGaussConst P / (2 * n)) := by
    calc
      _ = √((n : ℝ)^2 * ((1 / 2 : ℝ) + twoGaussConst P / (2 * n))) := by
        congr 1
        field_simp
        <;> ring
      _ = _ := by rw [sqrt_mul (sq_nonneg _), sqrt_sq hnR.le]
  unfold tangentU activeB
  rw [hrad]
  calc
    _ = 2 * (√((1 / 2 : ℝ) + twoGaussConst P / (2 * n)) +
        √(n : ℝ) / n + gaussMomConst (2 * P) / n)^2 := by field_simp
    _ = _ := by rw [sqrt_div_self hnR]

theorem lengthAlpha_le {n : ℕ} (hn : 12925 ≤ n) (P : ℕ) :
    lengthAlpha n P ≤ lengthAlpha 12925 P := by
  have hnR : (12925 : ℝ) ≤ n := by exact_mod_cast hn
  have hg := twoGaussConst_nonneg P
  unfold lengthAlpha
  gcongr

theorem pairQ_le {n : ℕ} (hn : 12925 ≤ n) (P : ℕ) : pairQ n P ≤ pairQ 12925 P := by
  have hnR : (12925 : ℝ) ≤ n := by exact_mod_cast hn
  have hroot : √(12925 : ℝ) ≤ √(n : ℝ) := sqrt_le_sqrt hnR
  have hg := gaussMomConst_nonneg P
  rw [pairQ_normalized (n := n) (by omega) P, pairQ_normalized (n := 12925) (by norm_num) P]
  gcongr

theorem tangentU_le {n : ℕ} (hn : 12925 ≤ n) (P : ℕ) :
    tangentU n P ≤ tangentU 12925 P := by
  have hnR : (12925 : ℝ) ≤ n := by exact_mod_cast hn
  have hroot : √(12925 : ℝ) ≤ √(n : ℝ) := sqrt_le_sqrt hnR
  have hg := gaussMomConst_nonneg (2 * P)
  have ht := twoGaussConst_nonneg P
  rw [tangentU_normalized (n := n) (by omega) P, tangentU_normalized (n := 12925) (by norm_num) P]
  gcongr

theorem overlapC_normalized {n : ℕ} (hn : 0 < n) (P : ℕ) :
    overlapC n P = 2 * √32 * (2 * (P.factorial : ℝ)) ^ (1 / (2 * (P : ℝ))) / n +
      8 * (2 * ((2 * P).factorial : ℝ)) ^ (1 / (2 * (P : ℝ))) / (n : ℝ)^2 := by
  unfold overlapC
  field_simp
  <;> ring

theorem overlapC_le {n : ℕ} (hn : 12925 ≤ n) (P : ℕ) : overlapC n P ≤ overlapC 12925 P := by
  have hnR : (12925 : ℝ) ≤ n := by exact_mod_cast hn
  rw [overlapC_normalized (n := n) (by omega) P, overlapC_normalized (n := 12925) (by norm_num) P]
  gcongr

theorem pairV_normalized {n : ℕ} (hn : 0 < n) (P : ℕ) :
    pairV n P = pairQ n P + 4 * √32 * √(log 162 + factorialRoot P) / n +
      16 * (log 162 + factorialRoot (2 * P)) / (n : ℝ)^2 := by
  unfold pairV pairPlane
  field_simp
  <;> ring

theorem pairV_le {n : ℕ} (hn : 12925 ≤ n) (P : ℕ) : pairV n P ≤ pairV 12925 P := by
  have hnR : (12925 : ℝ) ≤ n := by exact_mod_cast hn
  have hq := pairQ_le hn P
  have hlog : 0 ≤ log (162 : ℝ) := log_nonneg (by norm_num)
  have hf : 0 ≤ factorialRoot (2 * P) := by unfold factorialRoot; positivity
  rw [pairV_normalized (n := n) (by omega) P, pairV_normalized (n := 12925) (by norm_num) P]
  gcongr

theorem pairDelta_le {n : ℕ} (hn : 12925 ≤ n) (P : ℕ) (η : ℝ) :
    pairDelta n P η ≤ pairDelta 12925 P η := by
  have ho := overlapC_le hn P
  have hl := lengthAlpha_le hn P
  have hl2 := lengthAlpha_le hn (2 * P)
  have hl0 := lengthAlpha_nonneg n (2 * P)
  unfold pairDelta
  gcongr

theorem lowLengthProb_normalized {n : ℕ} (hn : 0 < n) (η : ℝ) :
    lowLengthProb n η = 4 * exp (-((n : ℝ) * η - 2 / n)^2 / 4) := by
  unfold lowLengthProb
  congr 2
  field_simp
  <;> ring

theorem lowLengthProb_le {n : ℕ} (hn : 12925 ≤ n) :
    lowLengthProb n (1 / 100) ≤ lowLengthProb 12925 (1 / 100) := by
  have hnR : (12925 : ℝ) ≤ n := by exact_mod_cast hn
  have hdiv : 2 / (n : ℝ) ≤ 2 / (12925 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have harg : (12925 : ℝ) * (1 / 100) - 2 / 12925 ≤ (n : ℝ) * (1 / 100) - 2 / n := by
    linarith
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 12925 * (1 / 100) - 2 / 12925)
    harg 2
  rw [lowLengthProb_normalized (n := n) (by omega), lowLengthProb_normalized (n := 12925) (by norm_num)]
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) (by norm_num)

theorem complementRoot_le {n : ℕ} (hn : 12925 ≤ n) (P : ℕ) :
    complementRoot n P ≤ complementRoot 12925 P := by
  have ht := tangentU_le hn (4 * P)
  have hl := lengthAlpha_le hn (8 * P)
  have hl0 := lengthAlpha_nonneg n (8 * P)
  unfold complementRoot
  gcongr

theorem complementB_le {n : ℕ} (hn : 12925 ≤ n) (P : ℕ) :
    complementB n P (1 / 100) ≤ complementB 12925 P (1 / 100) := by
  have hc := complementRoot_le hn P
  have hl := lowLengthProb_le hn
  have hc0 := complementRoot_nonneg n P
  have hlow0 : 0 ≤ lowLengthProb n (1 / 100) := by unfold lowLengthProb; positivity
  unfold complementB
  exact mul_le_mul hc (Real.rpow_le_rpow hlow0 hl (by positivity))
    (rpow_nonneg hlow0 _) (complementRoot_nonneg 12925 P)

theorem pairEpsilon_le {n : ℕ} (hn : 12925 ≤ n) :
    pairEpsilon n 16 (1 / 100) ≤ pairEpsilon 12925 16 (1 / 100) := by
  have hV := pairV_le hn 32
  have hQ := pairQ_le hn 32
  have hd := pairDelta_le hn 16 (1 / 100)
  have ht := tangentU_le hn 32
  have hl := lengthAlpha_le hn 64
  have hc := complementB_le hn 16
  have hV0 := pairV_nonneg n 32
  have hVOld0 := pairV_nonneg 12925 32
  have hQ0 := pairQ_nonneg n 32
  have hl0 := lengthAlpha_nonneg n 64
  have hr0 := radialCoefficient_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100)
    (by norm_num : (1 / 100 : ℝ) < 1)
  unfold pairEpsilon meanEpsilon fluctuationRoot
  norm_num only [Nat.reduceMul] at *
  gcongr <;> positivity

theorem uniform_error_epsilon_upper {n : ℕ} (hn : 12925 ≤ n) :
    pairEpsilon n 16 (1 / 100) ≤ (0.0623535369 : ℝ) :=
  (pairEpsilon_le hn).trans BstLean.Part269.D23.error_epsilon_upper

end BstLean.Part269.D23

/-! The actual direction scalar has a uniform bound on the World window. -/
namespace BstLean.Part269.D23
open Real Set MeasureTheory
open scoped ENNReal
open BstLean.Part130 BstLean.Part219 BstLean.Part215

theorem radius_nonneg_and_le {n : ℕ} (hn : 12925 ≤ n) (j : ℕ) (hj : j ≤ 96)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθhi : θ ≤ 54 / 100) :
    0 ≤ radiusCoefficient n j θ ∧ radiusCoefficient n j θ ≤ radiusCoefficient 12925 j θ := by
  have hnR : (12925 : ℝ) ≤ n := by exact_mod_cast hn
  have hjR : (j : ℝ) ≤ 96 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ 2 * j + 2 := by positivity
  have hc : (2 * j + 2 : ℝ) * θ / n ≤ 194 * (54 / 100 : ℝ) / 12925 := by gcongr <;> linarith
  have hc0 : (2 * j + 2 : ℝ) * θ / 12925 ≤ 194 * (54 / 100 : ℝ) / 12925 := by gcongr <;> linarith
  have hd : (2 * j + 2 : ℝ) * θ / n ≤ (2 * j + 2 : ℝ) * θ / 12925 := by gcongr
  unfold radiusCoefficient
  exact ⟨div_nonneg hθ (by linarith),
    div_le_div_of_nonneg_left hθ (by linarith) (by linarith)⟩

theorem amplitude_le {n : ℕ} (hn : 12925 ≤ n) {θ : ℝ}
    (hθ : 0 ≤ θ) (hθhi : θ ≤ 54 / 100) : paperAmplitude n θ ≤ paperAmplitude 12925 θ := by
  have hnR : (12925 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 4 * θ / n ≤ 4 * θ / 12925 := by gcongr
  have hnum : 0 ≤ 1 - θ := by linarith
  unfold paperAmplitude
  apply sqrt_le_sqrt
  exact div_le_div_of_nonneg_left hnum (by linarith) (by linarith)

theorem bias_le {n : ℕ} (hn : 12925 ≤ n) {θ : ℝ}
    (hθ : 0 ≤ θ) (hθhi : θ ≤ 54 / 100) : paperBias n θ ≤ paperBias 12925 θ := by
  have hnR : (12925 : ℝ) ≤ n := by exact_mod_cast hn
  have hr := radius_nonneg_and_le hn 4 (by norm_num) hθ hθhi
  have hr0 := hr.1
  have hrle := hr.2
  have hrold0 := hr.1.trans hr.2
  unfold paperBias
  gcongr <;> positivity

theorem paperIdeal_le {n : ℕ} (hn : 12925 ≤ n) {θ e : ℝ}
    (hθ : 0 ≤ θ) (hθhi : θ ≤ 54 / 100) (he : 0 < e) :
    paperIdeal n θ e ≤ paperIdeal 12925 θ e := by
  have hnR : (12925 : ℝ) ≤ n := by exact_mod_cast hn
  have hroot : √(12925 : ℝ) ≤ √(n : ℝ) := sqrt_le_sqrt hnR
  have h1 := radius_nonneg_and_le hn 1 (by norm_num) hθ hθhi
  have h24 := radius_nonneg_and_le hn 24 (by norm_num) hθ hθhi
  have h48 := radius_nonneg_and_le hn 48 (by norm_num) hθ hθhi
  have h96 := radius_nonneg_and_le hn 96 (by norm_num) hθ hθhi
  have h4 := radius_nonneg_and_le hn 4 (by norm_num) hθ hθhi
  have h40 := h4.1
  have h10 := h1.1
  have h240 := h24.1
  have h480 := h48.1
  have h960 := h96.1
  have h1le := h1.2
  have h24le := h24.2
  have h48le := h48.2
  have h96le := h96.2
  have h24old0 := h24.1.trans h24.2
  have h1old0 := h1.1.trans h1.2
  have h48old0 := h48.1.trans h48.2
  have h96old0 := h96.1.trans h96.2
  have ha := amplitude_le hn hθ hθhi
  have hb := bias_le hn hθ hθhi
  have hk := kernelSlope_nonneg (1 - θ)
  have hrot := BstLean.Part195.rotationConstant_nonneg 24
  have hb0 : 0 ≤ paperBias n θ := by unfold paperBias; positivity
  have hbold0 := hb0.trans hb
  have ha0 : 0 ≤ paperAmplitude n θ := sqrt_nonneg _
  have haold0 : 0 ≤ paperAmplitude 12925 θ := sqrt_nonneg _
  unfold paperIdeal
  gcongr <;> positivity

theorem baseline_ideal_window {θ e : ℝ} (hw : θ ∈ Icc (0.47199 : ℝ) 0.52358)
    (he : 0.665 ≤ e) : paperIdeal 12925 θ e ≤ 0.2282055781 := by
  by_cases h1 : θ ≤ 0.4744
  · exact idealCell0 ⟨hw.1, h1⟩ he
  by_cases h2 : θ ≤ 0.4816
  · exact idealCell1 ⟨by linarith, h2⟩ he
  by_cases h3 : θ ≤ 0.4888
  · exact idealCell2 ⟨by linarith, h3⟩ he
  by_cases h4 : θ ≤ 0.496
  · exact idealCell3 ⟨by linarith, h4⟩ he
  by_cases h5 : θ ≤ 0.5032
  · exact idealCell4 ⟨by linarith, h5⟩ he
  by_cases h6 : θ ≤ 0.5104
  · exact idealCell5 ⟨by linarith, h6⟩ he
  by_cases h7 : θ ≤ 0.5176
  · exact idealCell6 ⟨by linarith, h7⟩ he
  exact idealCell7 ⟨by linarith, hw.2⟩ he

theorem ideal_window {n : ℕ} (hn : 12925 ≤ n) {θ e : ℝ}
    (hw : θ ∈ Icc (0.47199 : ℝ) 0.52358) (he : 0.665 ≤ e) : paperIdeal n θ e ≤ 0.2282055781 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  exact (paperIdeal_le hn hθ (hw.2.trans (by norm_num)) (by linarith)).trans
    (baseline_ideal_window hw he)

theorem direction_budget_le {n : ℕ} (hn : 12925 ≤ n)
    (c : Fin n → ℝ) (τ e xi eta : ℝ) (δ : ℝ≥0∞)
    (hw : BstLean.Part150.thetaC c τ ∈ Icc (0.47199 : ℝ) 0.52358)
    (he : 0.665 ≤ e) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.1)
    (hop : operatorAllowance c τ eta δ ^ 2 ≤ 1.22) :
    paperDirectionBudget c τ e xi eta δ ≤ (0.0870703307 : ℝ) := by
  have hnR : (12925 : ℝ) ≤ n := by exact_mod_cast hn
  let θ := BstLean.Part150.thetaC c τ
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hθ1 : θ ≤ 0.52358 := hw.2
  have hrad := radius_nonneg_and_le hn 12 (by norm_num) hθ (hθ1.trans (by norm_num))
  have hR : radiusCoefficient n 12 θ ≤ 0.525 := (BstLean.Part264.radius_nonneg_and_le (by omega : 12225 ≤ n) 12 (by norm_num) hθ (hθ1.trans (by norm_num))).2.trans
    (BstLean.Part253.radius_upper 12 hθ hw.2 (by norm_num) (by norm_num))
  have hRs : √(radiusCoefficient n 12 θ / e) ≤ 0.889 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (div_le_div₀ (by norm_num) hR (by norm_num) he).trans (by norm_num)
  have heps := uniform_error_epsilon_upper hn
  have heps0 := BstLean.Part209.meanEpsilon_nonneg n 16
    (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num : (1 / 100 : ℝ) < 1)
  have hEp0 : 0 ≤ BstLean.Part209.pairEpsilon n 16 (1 / 100) :=
    add_nonneg heps0 (BstLean.Part209.fluctuationRoot_nonneg _ _)
  have hroot : (0.88 : ℝ) ≤ (7 / 25000 : ℝ) ^ (1 / 64 : ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by positivity)
    have hh := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 7 / 25000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hh
    rw [hh]
    norm_num
  have htransfer : √(operatorAllowance c τ eta δ ^ 2 * xi / ((n : ℝ) * e)) ≤ 0.00388 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1.22 : ℝ) * 0.1 / (12925 * 0.665) := by gcongr
      _ ≤ (0.00388 : ℝ)^2 := by norm_num
  have hi := ideal_window hn hw he
  have hi0 : 0 ≤ paperIdeal n θ e := by
    have hr (j : ℕ) (hj : j ≤ 96) :=
      (radius_nonneg_and_le hn j hj hθ (hθ1.trans (by norm_num))).1
    have hr48 := hr 48 (by norm_num)
    have hr96 := hr 96 (by norm_num)
    have hr4 := hr 4 (by norm_num)
    have hk := kernelSlope_nonneg (1 - θ)
    have hrot := BstLean.Part195.rotationConstant_nonneg 24
    unfold paperIdeal paperAmplitude paperBias
    positivity
  unfold paperDirectionBudget
  change (paperIdeal n θ e + _ + _) ^ 2 ≤ _
  calc
    _ ≤ ((0.2282055781 : ℝ) + 0.0623535369 * 0.889 / 0.88 + 0.00388)^2 := by gcongr
    _ ≤ (0.0870703307 : ℝ) := by norm_num

end BstLean.Part269.D23
