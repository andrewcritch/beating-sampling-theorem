import BstLean.Part252All
import BstLean.Part262ActualInterface
import BstLean.Part266Parameters


/-! Exact rational parameters for the dimension-12450 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12450
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (591101 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12450 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12450 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12450 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12450.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12450] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12450 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12450 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12450.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12450

namespace BstLean.Part266.Row12450
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12450 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12450 : ℝ)) ≤ ((113591451 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12450 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12450)
  change 0 ≤ agentLayerAllowance 12450 at ha0
  have he : energyWeightAllowance 12450 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12450)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12450)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12450).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12450).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12450)) :
    ∫ a in K, fbR c a ^ k ∂muI 12450 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12450])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12450

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12450
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12450 / 12450 ≤ chi := by
  have hs : √((12450 : ℝ) * 12) ≤ (193261481 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12450}
    (hc : c ∈ outputCentreEvent (paperCentres 12450)) :
    normSq c.2.1.2 ≤ (2 / (12450 : ℝ)) * eR c * 12450 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12450 : ℝ) * normSq (bR c) * chiUp 12450 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12450)).real (outputCentreEvent (paperCentres 12450))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12450

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12450
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12450) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12450) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12450)]
  norm_num [varianceMax]

end BstLean.Part266.Row12450

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12450
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12450) (hc : A1 c ∈ Eop 12450) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12450 : ℝ)) ≤ (12674485011 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12450 : ℝ) ≤ (111579569 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12450 : ℝ) + 2 * √12450 ≤ (6336579569 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12450) (hc : c ∈ BstLean.Part164.Eop2 12450) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12450 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12450) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12450 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12450) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12450).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12450) (FirstMatrix 12450))
    (h2 : c ∈ BstLean.Part164.Eop2 12450) (a : BstLean.Part161.Ix 12450) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12450

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12450
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12450) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12450) c ∈ BstLean.Part212.latitudeEvent 12450
      (ENNReal.ofReal (C / 12450))) (K : Set (Ix 12450)) :
    ∫ a in K, ((12450 : ℝ) * VR c a) ^ 2 ∂muI 12450 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12450

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12450
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12450 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12450 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12450 - 1 - 1) 80 ≤ (12606 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12450 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12606 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12450) ≤ (78 * 10 ^ 6 * ((12450 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12450 : ℝ) / 2 + 160) ≤ (4401744257 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12450 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12450 : ℝ) ^ 2 / 2 + 320 = 155003140 / 2 by norm_num,
    show (12450 : ℝ) ^ 2 / 2 + 160 = 155002820 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12450 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12450 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12450 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12450 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12450)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12450) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12450 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12450)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12450 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12450 ≤ (161 : ℝ) := by
  have hs : √(2 / (12450 : ℝ)) ≤ (12674485011 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12450 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12450 : ℝ) = 12450 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12450 : ℝ) + √12450 + gaussMomConst 80 ≤ 12571 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12450 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12450 : ℝ)) ≤ (113591451 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12450 4 +
      2 / (mA 12450 : ℝ) * frobEnvelopeSquared160 12450 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12450 4 +
      2 / (mA 12450 : ℝ) * frobEnvelopeSquared160 12450) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12450 : ℝ)) *
      operatorEnvelope160 12450 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12450 4 +
      2 / (mA 12450 : ℝ) * frobEnvelopeSquared160 12450) +
      transverseConstant160 * √(2 / (mA 12450 : ℝ)) * operatorEnvelope160 12450 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12450 4 +
      2 / (mA 12450 : ℝ) * frobEnvelopeSquared160 12450) +
      transverseConstant160 * √(2 / (mA 12450 : ℝ)) * operatorEnvelope160 12450 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12450 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12450 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12450 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12450 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12450

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12450
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12450) :=
  agentEv (paperDesignP 12450) (Energy32 12450) ∩
  agentEv (paperDesignP 12450) (freshRetainedEvent160 12450 4) ∩
  agentEv (paperDesignP 12450) (FirstMatrix 12450) ∩
  BstLean.Part164.Eop2 12450 ∩ outputCentreEvent (paperCentres 12450)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12450)).real
      (agentEv (paperDesignP 12450) (FirstMatrix 12450))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12450)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12450 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12450)).real (BstLean.Part164.Eop2 12450)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12450)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12450)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12450) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12450) hτ
  have hL := fresh_retained_charge160 (n := 12450) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12450) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12450 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12450) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12450 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12450) (hw : WINDOW (paperDesignP 12450) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12450))
    (hW : ∫ a in K, ((12450 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12450 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12450 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12450 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12450) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12450 : ℝ)) * eR c * 12450 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12450

/-! Exact rational parameters for the dimension-12451 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12451
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (591077 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12451 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12451 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12451 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12451.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12451] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12451 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12451 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12451.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12451

namespace BstLean.Part266.Row12451
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12451 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12451 : ℝ)) ≤ ((14197791 / 125000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12451 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12451)
  change 0 ≤ agentLayerAllowance 12451 at ha0
  have he : energyWeightAllowance 12451 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12451)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12451)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12451).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12451).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12451)) :
    ∫ a in K, fbR c a ^ k ∂muI 12451 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12451])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12451

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12451
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12451 / 12451 ≤ chi := by
  have hs : √((12451 : ℝ) * 12) ≤ (77307697 / 200000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12451}
    (hc : c ∈ outputCentreEvent (paperCentres 12451)) :
    normSq c.2.1.2 ≤ (2 / (12451 : ℝ)) * eR c * 12451 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12451 : ℝ) * normSq (bR c) * chiUp 12451 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12451)).real (outputCentreEvent (paperCentres 12451))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12451

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12451
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12451) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12451) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12451)]
  norm_num [varianceMax]

end BstLean.Part266.Row12451

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12451
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12451) (hc : A1 c ∈ Eop 12451) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12451 : ℝ)) ≤ (6336988013 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12451 : ℝ) ≤ (2231681 / 20000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12451 : ℝ) + 2 * √12451 ≤ (126741681 / 10000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12451) (hc : c ∈ BstLean.Part164.Eop2 12451) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12451 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12451) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12451 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12451) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12451).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12451) (FirstMatrix 12451))
    (h2 : c ∈ BstLean.Part164.Eop2 12451) (a : BstLean.Part161.Ix 12451) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12451

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12451
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12451) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12451) c ∈ BstLean.Part212.latitudeEvent 12451
      (ENNReal.ofReal (C / 12451))) (K : Set (Ix 12451)) :
    ∫ a in K, ((12451 : ℝ) * VR c a) ^ 2 ∂muI 12451 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12451

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12451
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12451 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12451 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12451 - 1 - 1) 80 ≤ (12607 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12451 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12607 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12451) ≤ (78 * 10 ^ 6 * ((12451 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12451 : ℝ) / 2 + 160) ≤ (440209781 / 50000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12451 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12451 : ℝ) ^ 2 / 2 + 320 = 155028041 / 2 by norm_num,
    show (12451 : ℝ) ^ 2 / 2 + 160 = 155027721 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12451 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12451 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12451 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12451 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12451)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12451) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12451 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12451)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12451 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12451 ≤ (161 : ℝ) := by
  have hs : √(2 / (12451 : ℝ)) ≤ (6336988013 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12451 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12451 : ℝ) = 12451 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12451 : ℝ) + √12451 + gaussMomConst 80 ≤ 12572 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12451 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12451 : ℝ)) ≤ (14197791 / 125000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12451 4 +
      2 / (mA 12451 : ℝ) * frobEnvelopeSquared160 12451 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12451 4 +
      2 / (mA 12451 : ℝ) * frobEnvelopeSquared160 12451) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12451 : ℝ)) *
      operatorEnvelope160 12451 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12451 4 +
      2 / (mA 12451 : ℝ) * frobEnvelopeSquared160 12451) +
      transverseConstant160 * √(2 / (mA 12451 : ℝ)) * operatorEnvelope160 12451 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12451 4 +
      2 / (mA 12451 : ℝ) * frobEnvelopeSquared160 12451) +
      transverseConstant160 * √(2 / (mA 12451 : ℝ)) * operatorEnvelope160 12451 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12451 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12451 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12451 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12451 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12451

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12451
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12451) :=
  agentEv (paperDesignP 12451) (Energy32 12451) ∩
  agentEv (paperDesignP 12451) (freshRetainedEvent160 12451 4) ∩
  agentEv (paperDesignP 12451) (FirstMatrix 12451) ∩
  BstLean.Part164.Eop2 12451 ∩ outputCentreEvent (paperCentres 12451)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12451)).real
      (agentEv (paperDesignP 12451) (FirstMatrix 12451))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12451)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12451 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12451)).real (BstLean.Part164.Eop2 12451)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12451)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12451)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12451) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12451) hτ
  have hL := fresh_retained_charge160 (n := 12451) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12451) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12451 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12451) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12451 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12451) (hw : WINDOW (paperDesignP 12451) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12451))
    (hW : ∫ a in K, ((12451 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12451 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12451 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12451 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12451) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12451 : ℝ)) * eR c * 12451 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12451

/-! Exact rational parameters for the dimension-12452 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12452
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (591053 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12452 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12452 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12452 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12452.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12452] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12452 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12452 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12452.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12452

namespace BstLean.Part266.Row12452
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12452 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12452 : ℝ)) ≤ ((113573207 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12452 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12452)
  change 0 ≤ agentLayerAllowance 12452 at ha0
  have he : energyWeightAllowance 12452 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12452)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12452)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12452).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12452).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12452)) :
    ∫ a in K, fbR c a ^ k ∂muI 12452 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12452])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12452

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12452
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12452 / 12452 ≤ chi := by
  have hs : √((12452 : ℝ) * 12) ≤ (386554007 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12452}
    (hc : c ∈ outputCentreEvent (paperCentres 12452)) :
    normSq c.2.1.2 ≤ (2 / (12452 : ℝ)) * eR c * 12452 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12452 : ℝ) * normSq (bR c) * chiUp 12452 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12452)).real (outputCentreEvent (paperCentres 12452))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12452

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12452
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12452) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12452) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12452)]
  norm_num [varianceMax]

end BstLean.Part266.Row12452

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12452
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12452) (hc : A1 c ∈ Eop 12452) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12452 : ℝ)) ≤ (12673467103 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12452 : ℝ) ≤ (11158853 / 100000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12452 : ℝ) + 2 * √12452 ≤ (633758853 / 50000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12452) (hc : c ∈ BstLean.Part164.Eop2 12452) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12452 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12452) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12452 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12452) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12452).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12452) (FirstMatrix 12452))
    (h2 : c ∈ BstLean.Part164.Eop2 12452) (a : BstLean.Part161.Ix 12452) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12452

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12452
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12452) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12452) c ∈ BstLean.Part212.latitudeEvent 12452
      (ENNReal.ofReal (C / 12452))) (K : Set (Ix 12452)) :
    ∫ a in K, ((12452 : ℝ) * VR c a) ^ 2 ∂muI 12452 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12452

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12452
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12452 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12452 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12452 - 1 - 1) 80 ≤ (12608 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12452 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12608 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12452) ≤ (78 * 10 ^ 6 * ((12452 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12452 : ℝ) / 2 + 160) ≤ (4402451363 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12452 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12452 : ℝ) ^ 2 / 2 + 320 = 155052944 / 2 by norm_num,
    show (12452 : ℝ) ^ 2 / 2 + 160 = 155052624 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12452 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12452 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12452 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12452 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12452)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12452) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12452 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12452)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12452 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12452 ≤ (161 : ℝ) := by
  have hs : √(2 / (12452 : ℝ)) ≤ (12673467103 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12452 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12452 : ℝ) = 12452 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12452 : ℝ) + √12452 + gaussMomConst 80 ≤ 12573 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12452 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12452 : ℝ)) ≤ (113573207 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12452 4 +
      2 / (mA 12452 : ℝ) * frobEnvelopeSquared160 12452 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12452 4 +
      2 / (mA 12452 : ℝ) * frobEnvelopeSquared160 12452) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12452 : ℝ)) *
      operatorEnvelope160 12452 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12452 4 +
      2 / (mA 12452 : ℝ) * frobEnvelopeSquared160 12452) +
      transverseConstant160 * √(2 / (mA 12452 : ℝ)) * operatorEnvelope160 12452 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12452 4 +
      2 / (mA 12452 : ℝ) * frobEnvelopeSquared160 12452) +
      transverseConstant160 * √(2 / (mA 12452 : ℝ)) * operatorEnvelope160 12452 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12452 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12452 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12452 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12452 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12452

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12452
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12452) :=
  agentEv (paperDesignP 12452) (Energy32 12452) ∩
  agentEv (paperDesignP 12452) (freshRetainedEvent160 12452 4) ∩
  agentEv (paperDesignP 12452) (FirstMatrix 12452) ∩
  BstLean.Part164.Eop2 12452 ∩ outputCentreEvent (paperCentres 12452)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12452)).real
      (agentEv (paperDesignP 12452) (FirstMatrix 12452))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12452)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12452 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12452)).real (BstLean.Part164.Eop2 12452)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12452)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12452)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12452) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12452) hτ
  have hL := fresh_retained_charge160 (n := 12452) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12452) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12452 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12452) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12452 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12452) (hw : WINDOW (paperDesignP 12452) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12452))
    (hW : ∫ a in K, ((12452 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12452 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12452 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12452 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12452) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12452 : ℝ)) * eR c * 12452 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12452

/-! Exact rational parameters for the dimension-12453 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12453
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (59103 / 10000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12453 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12453 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12453 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12453.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12453] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12453 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12453 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12453.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12453

namespace BstLean.Part266.Row12453
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12453 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12453 : ℝ)) ≤ ((56782043 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12453 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12453)
  change 0 ≤ agentLayerAllowance 12453 at ha0
  have he : energyWeightAllowance 12453 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12453)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12453)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12453).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12453).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12453)) :
    ∫ a in K, fbR c a ^ k ∂muI 12453 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12453])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12453

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12453
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12453 / 12453 ≤ chi := by
  have hs : √((12453 : ℝ) * 12) ≤ (386569529 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12453}
    (hc : c ∈ outputCentreEvent (paperCentres 12453)) :
    normSq c.2.1.2 ≤ (2 / (12453 : ℝ)) * eR c * 12453 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12453 : ℝ) * normSq (bR c) * chiUp 12453 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12453)).real (outputCentreEvent (paperCentres 12453))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12453

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12453
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12453) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12453) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12453)]
  norm_num [varianceMax]

end BstLean.Part266.Row12453

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12453
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12453) (hc : A1 c ∈ Eop 12453) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12453 : ℝ)) ≤ (12672958241 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12453 : ℝ) ≤ (111593011 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12453 : ℝ) + 2 * √12453 ≤ (6338093011 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12453) (hc : c ∈ BstLean.Part164.Eop2 12453) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12453 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12453) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12453 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12453) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12453).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12453) (FirstMatrix 12453))
    (h2 : c ∈ BstLean.Part164.Eop2 12453) (a : BstLean.Part161.Ix 12453) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12453

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12453
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12453) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12453) c ∈ BstLean.Part212.latitudeEvent 12453
      (ENNReal.ofReal (C / 12453))) (K : Set (Ix 12453)) :
    ∫ a in K, ((12453 : ℝ) * VR c a) ^ 2 ∂muI 12453 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12453

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12453
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12453 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12453 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12453 - 1 - 1) 80 ≤ (12609 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12453 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12609 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12453) ≤ (78 * 10 ^ 6 * ((12453 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12453 : ℝ) / 2 + 160) ≤ (1100701229 / 125000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12453 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12453 : ℝ) ^ 2 / 2 + 320 = 155077849 / 2 by norm_num,
    show (12453 : ℝ) ^ 2 / 2 + 160 = 155077529 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12453 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12453 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12453 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12453 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12453)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12453) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12453 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12453)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12453 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12453 ≤ (161 : ℝ) := by
  have hs : √(2 / (12453 : ℝ)) ≤ (12672958241 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12453 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12453 : ℝ) = 12453 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12453 : ℝ) + √12453 + gaussMomConst 80 ≤ 12574 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12453 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12453 : ℝ)) ≤ (56782043 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12453 4 +
      2 / (mA 12453 : ℝ) * frobEnvelopeSquared160 12453 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12453 4 +
      2 / (mA 12453 : ℝ) * frobEnvelopeSquared160 12453) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12453 : ℝ)) *
      operatorEnvelope160 12453 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12453 4 +
      2 / (mA 12453 : ℝ) * frobEnvelopeSquared160 12453) +
      transverseConstant160 * √(2 / (mA 12453 : ℝ)) * operatorEnvelope160 12453 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12453 4 +
      2 / (mA 12453 : ℝ) * frobEnvelopeSquared160 12453) +
      transverseConstant160 * √(2 / (mA 12453 : ℝ)) * operatorEnvelope160 12453 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12453 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12453 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12453 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12453 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12453

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12453
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12453) :=
  agentEv (paperDesignP 12453) (Energy32 12453) ∩
  agentEv (paperDesignP 12453) (freshRetainedEvent160 12453 4) ∩
  agentEv (paperDesignP 12453) (FirstMatrix 12453) ∩
  BstLean.Part164.Eop2 12453 ∩ outputCentreEvent (paperCentres 12453)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12453)).real
      (agentEv (paperDesignP 12453) (FirstMatrix 12453))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12453)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12453 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12453)).real (BstLean.Part164.Eop2 12453)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12453)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12453)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12453) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12453) hτ
  have hL := fresh_retained_charge160 (n := 12453) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12453) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12453 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12453) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12453 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12453) (hw : WINDOW (paperDesignP 12453) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12453))
    (hW : ∫ a in K, ((12453 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12453 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12453 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12453 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12453) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12453 : ℝ)) * eR c * 12453 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12453

/-! Exact rational parameters for the dimension-12454 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12454
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (295503 / 50000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12454 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12454 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12454 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12454.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12454] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12454 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12454 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12454.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12454

namespace BstLean.Part266.Row12454
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12454 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12454 : ℝ)) ≤ ((14194371 / 125000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12454 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12454)
  change 0 ≤ agentLayerAllowance 12454 at ha0
  have he : energyWeightAllowance 12454 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12454)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12454)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12454).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12454).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12454)) :
    ∫ a in K, fbR c a ^ k ∂muI 12454 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12454])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12454

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12454
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12454 / 12454 ≤ chi := by
  have hs : √((12454 : ℝ) * 12) ≤ (386585049 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12454}
    (hc : c ∈ outputCentreEvent (paperCentres 12454)) :
    normSq c.2.1.2 ≤ (2 / (12454 : ℝ)) * eR c * 12454 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12454 : ℝ) * normSq (bR c) * chiUp 12454 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12454)).real (outputCentreEvent (paperCentres 12454))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12454

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12454
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12454) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12454) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12454)]
  norm_num [varianceMax]

end BstLean.Part266.Row12454

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12454
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12454) (hc : A1 c ∈ Eop 12454) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12454 : ℝ)) ≤ (79202809 / 6250000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12454 : ℝ) ≤ (27899373 / 250000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12454 : ℝ) + 2 * √12454 ≤ (1584649373 / 125000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12454) (hc : c ∈ BstLean.Part164.Eop2 12454) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12454 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12454) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12454 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12454) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12454).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12454) (FirstMatrix 12454))
    (h2 : c ∈ BstLean.Part164.Eop2 12454) (a : BstLean.Part161.Ix 12454) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12454

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12454
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12454) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12454) c ∈ BstLean.Part212.latitudeEvent 12454
      (ENNReal.ofReal (C / 12454))) (K : Set (Ix 12454)) :
    ∫ a in K, ((12454 : ℝ) * VR c a) ^ 2 ∂muI 12454 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12454

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12454
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12454 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12454 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12454 - 1 - 1) 80 ≤ (12610 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12454 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12610 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12454) ≤ (78 * 10 ^ 6 * ((12454 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12454 : ℝ) / 2 + 160) ≤ (4403158469 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12454 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12454 : ℝ) ^ 2 / 2 + 320 = 155102756 / 2 by norm_num,
    show (12454 : ℝ) ^ 2 / 2 + 160 = 155102436 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12454 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12454 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12454 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12454 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12454)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12454) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12454 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12454)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12454 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12454 ≤ (161 : ℝ) := by
  have hs : √(2 / (12454 : ℝ)) ≤ (79202809 / 6250000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12454 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12454 : ℝ) = 12454 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12454 : ℝ) + √12454 + gaussMomConst 80 ≤ 12575 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12454 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12454 : ℝ)) ≤ (14194371 / 125000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12454 4 +
      2 / (mA 12454 : ℝ) * frobEnvelopeSquared160 12454 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12454 4 +
      2 / (mA 12454 : ℝ) * frobEnvelopeSquared160 12454) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12454 : ℝ)) *
      operatorEnvelope160 12454 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12454 4 +
      2 / (mA 12454 : ℝ) * frobEnvelopeSquared160 12454) +
      transverseConstant160 * √(2 / (mA 12454 : ℝ)) * operatorEnvelope160 12454 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12454 4 +
      2 / (mA 12454 : ℝ) * frobEnvelopeSquared160 12454) +
      transverseConstant160 * √(2 / (mA 12454 : ℝ)) * operatorEnvelope160 12454 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12454 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12454 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12454 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12454 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12454

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12454
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12454) :=
  agentEv (paperDesignP 12454) (Energy32 12454) ∩
  agentEv (paperDesignP 12454) (freshRetainedEvent160 12454 4) ∩
  agentEv (paperDesignP 12454) (FirstMatrix 12454) ∩
  BstLean.Part164.Eop2 12454 ∩ outputCentreEvent (paperCentres 12454)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12454)).real
      (agentEv (paperDesignP 12454) (FirstMatrix 12454))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12454)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12454 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12454)).real (BstLean.Part164.Eop2 12454)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12454)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12454)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12454) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12454) hτ
  have hL := fresh_retained_charge160 (n := 12454) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12454) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12454 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12454) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12454 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12454) (hw : WINDOW (paperDesignP 12454) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12454))
    (hW : ∫ a in K, ((12454 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12454 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12454 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12454 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12454) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12454 : ℝ)) * eR c * 12454 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12454

/-! Exact rational parameters for the dimension-12455 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12455
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (295491 / 50000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12455 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12455 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12455 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12455.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12455] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12455 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12455 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12455.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12455

namespace BstLean.Part266.Row12455
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12455 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12455 : ℝ)) ≤ ((113545851 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12455 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12455)
  change 0 ≤ agentLayerAllowance 12455 at ha0
  have he : energyWeightAllowance 12455 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12455)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12455)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12455).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12455).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12455)) :
    ∫ a in K, fbR c a ^ k ∂muI 12455 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12455])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12455

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12455
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12455 / 12455 ≤ chi := by
  have hs : √((12455 : ℝ) * 12) ≤ (38660057 / 100000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12455}
    (hc : c ∈ outputCentreEvent (paperCentres 12455)) :
    normSq c.2.1.2 ≤ (2 / (12455 : ℝ)) * eR c * 12455 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12455 : ℝ) * normSq (bR c) * chiUp 12455 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12455)).real (outputCentreEvent (paperCentres 12455))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12455

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12455
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12455) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12455) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12455)]
  norm_num [varianceMax]

end BstLean.Part266.Row12455

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12455
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12455) (hc : A1 c ∈ Eop 12455) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12455 : ℝ)) ≤ (126719407 / 10000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12455 : ℝ) ≤ (27900493 / 250000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12455 : ℝ) + 2 * √12455 ≤ (1584775493 / 125000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12455) (hc : c ∈ BstLean.Part164.Eop2 12455) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12455 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12455) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12455 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12455) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12455).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12455) (FirstMatrix 12455))
    (h2 : c ∈ BstLean.Part164.Eop2 12455) (a : BstLean.Part161.Ix 12455) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12455

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12455
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12455) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12455) c ∈ BstLean.Part212.latitudeEvent 12455
      (ENNReal.ofReal (C / 12455))) (K : Set (Ix 12455)) :
    ∫ a in K, ((12455 : ℝ) * VR c a) ^ 2 ∂muI 12455 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12455

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12455
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12455 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12455 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12455 - 1 - 1) 80 ≤ (12611 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12455 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12611 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12455) ≤ (78 * 10 ^ 6 * ((12455 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12455 : ℝ) / 2 + 160) ≤ (2201756011 / 250000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12455 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12455 : ℝ) ^ 2 / 2 + 320 = 155127665 / 2 by norm_num,
    show (12455 : ℝ) ^ 2 / 2 + 160 = 155127345 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12455 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12455 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12455 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12455 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12455)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12455) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12455 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12455)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12455 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12455 ≤ (161 : ℝ) := by
  have hs : √(2 / (12455 : ℝ)) ≤ (126719407 / 10000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12455 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12455 : ℝ) = 12455 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12455 : ℝ) + √12455 + gaussMomConst 80 ≤ 12576 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12455 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12455 : ℝ)) ≤ (113545851 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12455 4 +
      2 / (mA 12455 : ℝ) * frobEnvelopeSquared160 12455 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12455 4 +
      2 / (mA 12455 : ℝ) * frobEnvelopeSquared160 12455) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12455 : ℝ)) *
      operatorEnvelope160 12455 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12455 4 +
      2 / (mA 12455 : ℝ) * frobEnvelopeSquared160 12455) +
      transverseConstant160 * √(2 / (mA 12455 : ℝ)) * operatorEnvelope160 12455 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12455 4 +
      2 / (mA 12455 : ℝ) * frobEnvelopeSquared160 12455) +
      transverseConstant160 * √(2 / (mA 12455 : ℝ)) * operatorEnvelope160 12455 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12455 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12455 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12455 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12455 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12455

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12455
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12455) :=
  agentEv (paperDesignP 12455) (Energy32 12455) ∩
  agentEv (paperDesignP 12455) (freshRetainedEvent160 12455 4) ∩
  agentEv (paperDesignP 12455) (FirstMatrix 12455) ∩
  BstLean.Part164.Eop2 12455 ∩ outputCentreEvent (paperCentres 12455)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12455)).real
      (agentEv (paperDesignP 12455) (FirstMatrix 12455))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12455)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12455 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12455)).real (BstLean.Part164.Eop2 12455)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12455)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12455)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12455) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12455) hτ
  have hL := fresh_retained_charge160 (n := 12455) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12455) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12455 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12455) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12455 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12455) (hw : WINDOW (paperDesignP 12455) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12455))
    (hW : ∫ a in K, ((12455 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12455 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12455 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12455 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12455) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12455 : ℝ)) * eR c * 12455 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12455

/-! Exact rational parameters for the dimension-12456 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12456
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (590959 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12456 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12456 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12456 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12456.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12456] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12456 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12456 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12456.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12456

namespace BstLean.Part266.Row12456
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12456 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12456 : ℝ)) ≤ ((22707347 / 200000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12456 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12456)
  change 0 ≤ agentLayerAllowance 12456 at ha0
  have he : energyWeightAllowance 12456 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12456)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12456)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12456).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12456).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12456)) :
    ∫ a in K, fbR c a ^ k ∂muI 12456 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12456])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12456

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12456
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12456 / 12456 ≤ chi := by
  have hs : √((12456 : ℝ) * 12) ≤ (386616089 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12456}
    (hc : c ∈ outputCentreEvent (paperCentres 12456)) :
    normSq c.2.1.2 ≤ (2 / (12456 : ℝ)) * eR c * 12456 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12456 : ℝ) * normSq (bR c) * chiUp 12456 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12456)).real (outputCentreEvent (paperCentres 12456))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12456

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12456
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12456) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12456) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12456)]
  norm_num [varianceMax]

end BstLean.Part266.Row12456

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12456
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12456) (hc : A1 c ∈ Eop 12456) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12456 : ℝ)) ≤ (6335716011 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12456 : ℝ) ≤ (27901613 / 250000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12456 : ℝ) + 2 * √12456 ≤ (1584901613 / 125000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12456) (hc : c ∈ BstLean.Part164.Eop2 12456) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12456 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12456) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12456 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12456) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12456).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12456) (FirstMatrix 12456))
    (h2 : c ∈ BstLean.Part164.Eop2 12456) (a : BstLean.Part161.Ix 12456) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12456

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12456
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12456) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12456) c ∈ BstLean.Part212.latitudeEvent 12456
      (ENNReal.ofReal (C / 12456))) (K : Set (Ix 12456)) :
    ∫ a in K, ((12456 : ℝ) * VR c a) ^ 2 ∂muI 12456 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12456

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12456
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12456 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12456 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12456 - 1 - 1) 80 ≤ (12612 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12456 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12612 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12456) ≤ (78 * 10 ^ 6 * ((12456 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12456 : ℝ) / 2 + 160) ≤ (176154623 / 20000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12456 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12456 : ℝ) ^ 2 / 2 + 320 = 155152576 / 2 by norm_num,
    show (12456 : ℝ) ^ 2 / 2 + 160 = 155152256 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12456 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12456 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12456 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12456 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12456)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12456) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12456 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12456)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12456 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12456 ≤ (161 : ℝ) := by
  have hs : √(2 / (12456 : ℝ)) ≤ (6335716011 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12456 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12456 : ℝ) = 12456 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12456 : ℝ) + √12456 + gaussMomConst 80 ≤ 12577 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12456 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12456 : ℝ)) ≤ (22707347 / 200000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12456 4 +
      2 / (mA 12456 : ℝ) * frobEnvelopeSquared160 12456 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12456 4 +
      2 / (mA 12456 : ℝ) * frobEnvelopeSquared160 12456) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12456 : ℝ)) *
      operatorEnvelope160 12456 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12456 4 +
      2 / (mA 12456 : ℝ) * frobEnvelopeSquared160 12456) +
      transverseConstant160 * √(2 / (mA 12456 : ℝ)) * operatorEnvelope160 12456 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12456 4 +
      2 / (mA 12456 : ℝ) * frobEnvelopeSquared160 12456) +
      transverseConstant160 * √(2 / (mA 12456 : ℝ)) * operatorEnvelope160 12456 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12456 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12456 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12456 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12456 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12456

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12456
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12456) :=
  agentEv (paperDesignP 12456) (Energy32 12456) ∩
  agentEv (paperDesignP 12456) (freshRetainedEvent160 12456 4) ∩
  agentEv (paperDesignP 12456) (FirstMatrix 12456) ∩
  BstLean.Part164.Eop2 12456 ∩ outputCentreEvent (paperCentres 12456)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12456)).real
      (agentEv (paperDesignP 12456) (FirstMatrix 12456))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12456)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12456 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12456)).real (BstLean.Part164.Eop2 12456)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12456)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12456)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12456) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12456) hτ
  have hL := fresh_retained_charge160 (n := 12456) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12456) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12456 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12456) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12456 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12456) (hw : WINDOW (paperDesignP 12456) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12456))
    (hW : ∫ a in K, ((12456 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12456 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12456 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12456 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12456) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12456 : ℝ)) * eR c * 12456 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12456

/-! Exact rational parameters for the dimension-12457 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12457
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (118187 / 20000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12457 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12457 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12457 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12457.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12457] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12457 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12457 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12457.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12457

namespace BstLean.Part266.Row12457
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12457 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12457 : ℝ)) ≤ ((113527621 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12457 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12457)
  change 0 ≤ agentLayerAllowance 12457 at ha0
  have he : energyWeightAllowance 12457 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12457)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12457)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12457).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12457).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12457)) :
    ∫ a in K, fbR c a ^ k ∂muI 12457 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12457])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12457

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12457
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12457 / 12457 ≤ chi := by
  have hs : √((12457 : ℝ) * 12) ≤ (48328951 / 125000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12457}
    (hc : c ∈ outputCentreEvent (paperCentres 12457)) :
    normSq c.2.1.2 ≤ (2 / (12457 : ℝ)) * eR c * 12457 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12457 : ℝ) * normSq (bR c) * chiUp 12457 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12457)).real (outputCentreEvent (paperCentres 12457))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12457

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12457
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12457) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12457) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12457)]
  norm_num [varianceMax]

end BstLean.Part266.Row12457

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12457
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12457) (hc : A1 c ∈ Eop 12457) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12457 : ℝ)) ≤ (2534184681 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12457 : ℝ) ≤ (27902733 / 250000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12457 : ℝ) + 2 * √12457 ≤ (1585027733 / 125000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12457) (hc : c ∈ BstLean.Part164.Eop2 12457) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12457 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12457) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12457 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12457) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12457).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12457) (FirstMatrix 12457))
    (h2 : c ∈ BstLean.Part164.Eop2 12457) (a : BstLean.Part161.Ix 12457) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12457

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12457
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12457) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12457) c ∈ BstLean.Part212.latitudeEvent 12457
      (ENNReal.ofReal (C / 12457))) (K : Set (Ix 12457)) :
    ∫ a in K, ((12457 : ℝ) * VR c a) ^ 2 ∂muI 12457 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12457

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12457
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12457 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12457 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12457 - 1 - 1) 80 ≤ (12613 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12457 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12613 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12457) ≤ (78 * 10 ^ 6 * ((12457 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12457 : ℝ) / 2 + 160) ≤ (550527391 / 62500) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12457 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12457 : ℝ) ^ 2 / 2 + 320 = 155177489 / 2 by norm_num,
    show (12457 : ℝ) ^ 2 / 2 + 160 = 155177169 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12457 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12457 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12457 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12457 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12457)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12457) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12457 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12457)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12457 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12457 ≤ (161 : ℝ) := by
  have hs : √(2 / (12457 : ℝ)) ≤ (2534184681 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12457 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12457 : ℝ) = 12457 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12457 : ℝ) + √12457 + gaussMomConst 80 ≤ 12578 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12457 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12457 : ℝ)) ≤ (113527621 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12457 4 +
      2 / (mA 12457 : ℝ) * frobEnvelopeSquared160 12457 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12457 4 +
      2 / (mA 12457 : ℝ) * frobEnvelopeSquared160 12457) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12457 : ℝ)) *
      operatorEnvelope160 12457 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12457 4 +
      2 / (mA 12457 : ℝ) * frobEnvelopeSquared160 12457) +
      transverseConstant160 * √(2 / (mA 12457 : ℝ)) * operatorEnvelope160 12457 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12457 4 +
      2 / (mA 12457 : ℝ) * frobEnvelopeSquared160 12457) +
      transverseConstant160 * √(2 / (mA 12457 : ℝ)) * operatorEnvelope160 12457 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12457 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12457 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12457 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12457 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12457

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12457
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12457) :=
  agentEv (paperDesignP 12457) (Energy32 12457) ∩
  agentEv (paperDesignP 12457) (freshRetainedEvent160 12457 4) ∩
  agentEv (paperDesignP 12457) (FirstMatrix 12457) ∩
  BstLean.Part164.Eop2 12457 ∩ outputCentreEvent (paperCentres 12457)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12457)).real
      (agentEv (paperDesignP 12457) (FirstMatrix 12457))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12457)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12457 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12457)).real (BstLean.Part164.Eop2 12457)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12457)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12457)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12457) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12457) hτ
  have hL := fresh_retained_charge160 (n := 12457) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12457) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12457 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12457) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12457 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12457) (hw : WINDOW (paperDesignP 12457) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12457))
    (hW : ∫ a in K, ((12457 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12457 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12457 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12457 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12457) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12457 : ℝ)) * eR c * 12457 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12457

/-! Exact rational parameters for the dimension-12458 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12458
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (590911 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12458 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12458 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12458 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12458.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12458] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12458 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12458 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12458.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12458

namespace BstLean.Part266.Row12458
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12458 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12458 : ℝ)) ≤ ((28379627 / 250000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12458 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12458)
  change 0 ≤ agentLayerAllowance 12458 at ha0
  have he : energyWeightAllowance 12458 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12458)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12458)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12458).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12458).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12458)) :
    ∫ a in K, fbR c a ^ k ∂muI 12458 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12458])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12458

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12458
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12458 / 12458 ≤ chi := by
  have hs : √((12458 : ℝ) * 12) ≤ (193323563 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12458}
    (hc : c ∈ outputCentreEvent (paperCentres 12458)) :
    normSq c.2.1.2 ≤ (2 / (12458 : ℝ)) * eR c * 12458 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12458 : ℝ) * normSq (bR c) * chiUp 12458 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12458)).real (outputCentreEvent (paperCentres 12458))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12458

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12458
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12458) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12458) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12458)]
  norm_num [varianceMax]

end BstLean.Part266.Row12458

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12458
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12458) (hc : A1 c ∈ Eop 12458) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12458 : ℝ)) ≤ (12670414849 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12458 : ℝ) ≤ (27903853 / 250000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12458 : ℝ) + 2 * √12458 ≤ (1585153853 / 125000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12458) (hc : c ∈ BstLean.Part164.Eop2 12458) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12458 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12458) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12458 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12458) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12458).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12458) (FirstMatrix 12458))
    (h2 : c ∈ BstLean.Part164.Eop2 12458) (a : BstLean.Part161.Ix 12458) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12458

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12458
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12458) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12458) c ∈ BstLean.Part212.latitudeEvent 12458
      (ENNReal.ofReal (C / 12458))) (K : Set (Ix 12458)) :
    ∫ a in K, ((12458 : ℝ) * VR c a) ^ 2 ∂muI 12458 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12458

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12458
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12458 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12458 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12458 - 1 - 1) 80 ≤ (12614 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12458 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12614 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12458) ≤ (78 * 10 ^ 6 * ((12458 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12458 : ℝ) / 2 + 160) ≤ (4404572681 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12458 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12458 : ℝ) ^ 2 / 2 + 320 = 155202404 / 2 by norm_num,
    show (12458 : ℝ) ^ 2 / 2 + 160 = 155202084 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12458 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12458 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12458 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12458 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12458)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12458) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12458 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12458)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12458 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12458 ≤ (161 : ℝ) := by
  have hs : √(2 / (12458 : ℝ)) ≤ (12670414849 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12458 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12458 : ℝ) = 12458 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12458 : ℝ) + √12458 + gaussMomConst 80 ≤ 12579 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12458 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12458 : ℝ)) ≤ (28379627 / 250000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12458 4 +
      2 / (mA 12458 : ℝ) * frobEnvelopeSquared160 12458 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12458 4 +
      2 / (mA 12458 : ℝ) * frobEnvelopeSquared160 12458) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12458 : ℝ)) *
      operatorEnvelope160 12458 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12458 4 +
      2 / (mA 12458 : ℝ) * frobEnvelopeSquared160 12458) +
      transverseConstant160 * √(2 / (mA 12458 : ℝ)) * operatorEnvelope160 12458 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12458 4 +
      2 / (mA 12458 : ℝ) * frobEnvelopeSquared160 12458) +
      transverseConstant160 * √(2 / (mA 12458 : ℝ)) * operatorEnvelope160 12458 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12458 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12458 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12458 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12458 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12458

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12458
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12458) :=
  agentEv (paperDesignP 12458) (Energy32 12458) ∩
  agentEv (paperDesignP 12458) (freshRetainedEvent160 12458 4) ∩
  agentEv (paperDesignP 12458) (FirstMatrix 12458) ∩
  BstLean.Part164.Eop2 12458 ∩ outputCentreEvent (paperCentres 12458)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12458)).real
      (agentEv (paperDesignP 12458) (FirstMatrix 12458))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12458)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12458 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12458)).real (BstLean.Part164.Eop2 12458)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12458)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12458)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12458) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12458) hτ
  have hL := fresh_retained_charge160 (n := 12458) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12458) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12458 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12458) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12458 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12458) (hw : WINDOW (paperDesignP 12458) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12458))
    (hW : ∫ a in K, ((12458 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12458 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12458 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12458 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12458) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12458 : ℝ)) * eR c * 12458 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12458

/-! Exact rational parameters for the dimension-12459 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12459
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (590887 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12459 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12459 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12459 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12459.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12459] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12459 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12459 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12459.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12459

namespace BstLean.Part266.Row12459
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12459 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12459 : ℝ)) ≤ ((28377349 / 250000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12459 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12459)
  change 0 ≤ agentLayerAllowance 12459 at ha0
  have he : energyWeightAllowance 12459 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12459)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12459)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12459).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12459).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12459)) :
    ∫ a in K, fbR c a ^ k ∂muI 12459 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12459])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12459

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12459
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12459 / 12459 ≤ chi := by
  have hs : √((12459 : ℝ) * 12) ≤ (96665661 / 250000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12459}
    (hc : c ∈ outputCentreEvent (paperCentres 12459)) :
    normSq c.2.1.2 ≤ (2 / (12459 : ℝ)) * eR c * 12459 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12459 : ℝ) * normSq (bR c) * chiUp 12459 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12459)).real (outputCentreEvent (paperCentres 12459))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12459

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12459
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12459) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12459) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12459)]
  norm_num [varianceMax]

end BstLean.Part266.Row12459

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12459
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12459) (hc : A1 c ∈ Eop 12459) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12459 : ℝ)) ≤ (6334953177 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12459 : ℝ) ≤ (111619891 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12459 : ℝ) + 2 * √12459 ≤ (6341119891 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12459) (hc : c ∈ BstLean.Part164.Eop2 12459) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12459 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12459) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12459 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12459) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12459).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12459) (FirstMatrix 12459))
    (h2 : c ∈ BstLean.Part164.Eop2 12459) (a : BstLean.Part161.Ix 12459) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12459

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12459
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12459) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12459) c ∈ BstLean.Part212.latitudeEvent 12459
      (ENNReal.ofReal (C / 12459))) (K : Set (Ix 12459)) :
    ∫ a in K, ((12459 : ℝ) * VR c a) ^ 2 ∂muI 12459 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12459

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12459
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12459 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12459 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12459 - 1 - 1) 80 ≤ (12615 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12459 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12615 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12459) ≤ (78 * 10 ^ 6 * ((12459 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12459 : ℝ) / 2 + 160) ≤ (2202463117 / 250000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12459 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12459 : ℝ) ^ 2 / 2 + 320 = 155227321 / 2 by norm_num,
    show (12459 : ℝ) ^ 2 / 2 + 160 = 155227001 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12459 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12459 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12459 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12459 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12459)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12459) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12459 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12459)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12459 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12459 ≤ (161 : ℝ) := by
  have hs : √(2 / (12459 : ℝ)) ≤ (6334953177 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12459 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12459 : ℝ) = 12459 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12459 : ℝ) + √12459 + gaussMomConst 80 ≤ 12580 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12459 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12459 : ℝ)) ≤ (28377349 / 250000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12459 4 +
      2 / (mA 12459 : ℝ) * frobEnvelopeSquared160 12459 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12459 4 +
      2 / (mA 12459 : ℝ) * frobEnvelopeSquared160 12459) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12459 : ℝ)) *
      operatorEnvelope160 12459 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12459 4 +
      2 / (mA 12459 : ℝ) * frobEnvelopeSquared160 12459) +
      transverseConstant160 * √(2 / (mA 12459 : ℝ)) * operatorEnvelope160 12459 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12459 4 +
      2 / (mA 12459 : ℝ) * frobEnvelopeSquared160 12459) +
      transverseConstant160 * √(2 / (mA 12459 : ℝ)) * operatorEnvelope160 12459 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12459 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12459 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12459 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12459 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12459

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12459
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12459) :=
  agentEv (paperDesignP 12459) (Energy32 12459) ∩
  agentEv (paperDesignP 12459) (freshRetainedEvent160 12459 4) ∩
  agentEv (paperDesignP 12459) (FirstMatrix 12459) ∩
  BstLean.Part164.Eop2 12459 ∩ outputCentreEvent (paperCentres 12459)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12459)).real
      (agentEv (paperDesignP 12459) (FirstMatrix 12459))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12459)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12459 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12459)).real (BstLean.Part164.Eop2 12459)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12459)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12459)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12459) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12459) hτ
  have hL := fresh_retained_charge160 (n := 12459) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12459) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12459 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12459) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12459 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12459) (hw : WINDOW (paperDesignP 12459) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12459))
    (hW : ∫ a in K, ((12459 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12459 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12459 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12459 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12459) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12459 : ℝ)) * eR c * 12459 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12459

/-! Exact rational parameters for the dimension-12460 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12460
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (36929 / 6250000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12460 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12460 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12460 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12460.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12460] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12460 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12460 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12460.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12460

namespace BstLean.Part266.Row12460
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12460 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12460 : ℝ)) ≤ ((56750143 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12460 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12460)
  change 0 ≤ agentLayerAllowance 12460 at ha0
  have he : energyWeightAllowance 12460 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12460)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12460)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12460).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12460).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12460)) :
    ∫ a in K, fbR c a ^ k ∂muI 12460 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12460])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12460

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12460
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12460 / 12460 ≤ chi := by
  have hs : √((12460 : ℝ) * 12) ≤ (386678161 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12460}
    (hc : c ∈ outputCentreEvent (paperCentres 12460)) :
    normSq c.2.1.2 ≤ (2 / (12460 : ℝ)) * eR c * 12460 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12460 : ℝ) * normSq (bR c) * chiUp 12460 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12460)).real (outputCentreEvent (paperCentres 12460))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12460

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12460
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12460) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12460) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12460)]
  norm_num [varianceMax]

end BstLean.Part266.Row12460

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12460
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12460) (hc : A1 c ∈ Eop 12460) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12460 : ℝ)) ≤ (12669397921 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12460 : ℝ) ≤ (111624371 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12460 : ℝ) + 2 * √12460 ≤ (6341624371 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12460) (hc : c ∈ BstLean.Part164.Eop2 12460) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12460 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12460) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12460 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12460) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12460).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12460) (FirstMatrix 12460))
    (h2 : c ∈ BstLean.Part164.Eop2 12460) (a : BstLean.Part161.Ix 12460) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12460

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12460
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12460) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12460) c ∈ BstLean.Part212.latitudeEvent 12460
      (ENNReal.ofReal (C / 12460))) (K : Set (Ix 12460)) :
    ∫ a in K, ((12460 : ℝ) * VR c a) ^ 2 ∂muI 12460 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12460

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12460
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12460 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12460 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12460 - 1 - 1) 80 ≤ (12616 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12460 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12616 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12460) ≤ (78 * 10 ^ 6 * ((12460 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12460 : ℝ) / 2 + 160) ≤ (4405279787 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12460 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12460 : ℝ) ^ 2 / 2 + 320 = 155252240 / 2 by norm_num,
    show (12460 : ℝ) ^ 2 / 2 + 160 = 155251920 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12460 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12460 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12460 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12460 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12460)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12460) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12460 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12460)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12460 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12460 ≤ (161 : ℝ) := by
  have hs : √(2 / (12460 : ℝ)) ≤ (12669397921 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12460 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12460 : ℝ) = 12460 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12460 : ℝ) + √12460 + gaussMomConst 80 ≤ 12581 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12460 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12460 : ℝ)) ≤ (56750143 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12460 4 +
      2 / (mA 12460 : ℝ) * frobEnvelopeSquared160 12460 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12460 4 +
      2 / (mA 12460 : ℝ) * frobEnvelopeSquared160 12460) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12460 : ℝ)) *
      operatorEnvelope160 12460 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12460 4 +
      2 / (mA 12460 : ℝ) * frobEnvelopeSquared160 12460) +
      transverseConstant160 * √(2 / (mA 12460 : ℝ)) * operatorEnvelope160 12460 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12460 4 +
      2 / (mA 12460 : ℝ) * frobEnvelopeSquared160 12460) +
      transverseConstant160 * √(2 / (mA 12460 : ℝ)) * operatorEnvelope160 12460 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12460 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12460 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12460 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12460 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12460

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12460
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12460) :=
  agentEv (paperDesignP 12460) (Energy32 12460) ∩
  agentEv (paperDesignP 12460) (freshRetainedEvent160 12460 4) ∩
  agentEv (paperDesignP 12460) (FirstMatrix 12460) ∩
  BstLean.Part164.Eop2 12460 ∩ outputCentreEvent (paperCentres 12460)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12460)).real
      (agentEv (paperDesignP 12460) (FirstMatrix 12460))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12460)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12460 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12460)).real (BstLean.Part164.Eop2 12460)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12460)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12460)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12460) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12460) hτ
  have hL := fresh_retained_charge160 (n := 12460) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12460) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12460 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12460) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12460 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12460) (hw : WINDOW (paperDesignP 12460) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12460))
    (hW : ∫ a in K, ((12460 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12460 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12460 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12460 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12460) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12460 : ℝ)) * eR c * 12460 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12460

/-! Exact rational parameters for the dimension-12461 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12461
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (14771 / 2500000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12461 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12461 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12461 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12461.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12461] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12461 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12461 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12461.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12461

namespace BstLean.Part266.Row12461
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12461 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12461 : ℝ)) ≤ ((56745589 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12461 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12461)
  change 0 ≤ agentLayerAllowance 12461 at ha0
  have he : energyWeightAllowance 12461 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12461)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12461)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12461).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12461).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12461)) :
    ∫ a in K, fbR c a ^ k ∂muI 12461 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12461])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12461

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12461
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12461 / 12461 ≤ chi := by
  have hs : √((12461 : ℝ) * 12) ≤ (193346839 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12461}
    (hc : c ∈ outputCentreEvent (paperCentres 12461)) :
    normSq c.2.1.2 ≤ (2 / (12461 : ℝ)) * eR c * 12461 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12461 : ℝ) * normSq (bR c) * chiUp 12461 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12461)).real (outputCentreEvent (paperCentres 12461))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12461

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12461
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12461) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12461) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12461)]
  norm_num [varianceMax]

end BstLean.Part266.Row12461

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12461
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12461) (hc : A1 c ∈ Eop 12461) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12461 : ℝ)) ≤ (3167222387 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12461 : ℝ) ≤ (2232577 / 20000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12461 : ℝ) + 2 * √12461 ≤ (126842577 / 10000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12461) (hc : c ∈ BstLean.Part164.Eop2 12461) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12461 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12461) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12461 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12461) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12461).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12461) (FirstMatrix 12461))
    (h2 : c ∈ BstLean.Part164.Eop2 12461) (a : BstLean.Part161.Ix 12461) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12461

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12461
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12461) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12461) c ∈ BstLean.Part212.latitudeEvent 12461
      (ENNReal.ofReal (C / 12461))) (K : Set (Ix 12461)) :
    ∫ a in K, ((12461 : ℝ) * VR c a) ^ 2 ∂muI 12461 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12461

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12461
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12461 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12461 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12461 - 1 - 1) 80 ≤ (12617 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12461 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12617 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12461) ≤ (78 * 10 ^ 6 * ((12461 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12461 : ℝ) / 2 + 160) ≤ (220281667 / 25000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12461 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12461 : ℝ) ^ 2 / 2 + 320 = 155277161 / 2 by norm_num,
    show (12461 : ℝ) ^ 2 / 2 + 160 = 155276841 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12461 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12461 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12461 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12461 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12461)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12461) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12461 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12461)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12461 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12461 ≤ (161 : ℝ) := by
  have hs : √(2 / (12461 : ℝ)) ≤ (3167222387 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12461 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12461 : ℝ) = 12461 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12461 : ℝ) + √12461 + gaussMomConst 80 ≤ 12582 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12461 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12461 : ℝ)) ≤ (56745589 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12461 4 +
      2 / (mA 12461 : ℝ) * frobEnvelopeSquared160 12461 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12461 4 +
      2 / (mA 12461 : ℝ) * frobEnvelopeSquared160 12461) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12461 : ℝ)) *
      operatorEnvelope160 12461 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12461 4 +
      2 / (mA 12461 : ℝ) * frobEnvelopeSquared160 12461) +
      transverseConstant160 * √(2 / (mA 12461 : ℝ)) * operatorEnvelope160 12461 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12461 4 +
      2 / (mA 12461 : ℝ) * frobEnvelopeSquared160 12461) +
      transverseConstant160 * √(2 / (mA 12461 : ℝ)) * operatorEnvelope160 12461 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12461 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12461 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12461 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12461 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12461

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12461
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12461) :=
  agentEv (paperDesignP 12461) (Energy32 12461) ∩
  agentEv (paperDesignP 12461) (freshRetainedEvent160 12461 4) ∩
  agentEv (paperDesignP 12461) (FirstMatrix 12461) ∩
  BstLean.Part164.Eop2 12461 ∩ outputCentreEvent (paperCentres 12461)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12461)).real
      (agentEv (paperDesignP 12461) (FirstMatrix 12461))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12461)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12461 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12461)).real (BstLean.Part164.Eop2 12461)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12461)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12461)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12461) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12461) hτ
  have hL := fresh_retained_charge160 (n := 12461) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12461) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12461 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12461) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12461 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12461) (hw : WINDOW (paperDesignP 12461) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12461))
    (hW : ∫ a in K, ((12461 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12461 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12461 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12461 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12461) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12461 : ℝ)) * eR c * 12461 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12461

/-! Exact rational parameters for the dimension-12462 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12462
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (18463 / 3125000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12462 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12462 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12462 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12462.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12462] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12462 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12462 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12462.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12462

namespace BstLean.Part266.Row12462
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12462 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12462 : ℝ)) ≤ ((113482071 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12462 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12462)
  change 0 ≤ agentLayerAllowance 12462 at ha0
  have he : energyWeightAllowance 12462 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12462)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12462)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12462).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12462).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12462)) :
    ∫ a in K, fbR c a ^ k ∂muI 12462 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12462])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12462

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12462
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12462 / 12462 ≤ chi := by
  have hs : √((12462 : ℝ) * 12) ≤ (193354597 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12462}
    (hc : c ∈ outputCentreEvent (paperCentres 12462)) :
    normSq c.2.1.2 ≤ (2 / (12462 : ℝ)) * eR c * 12462 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12462 : ℝ) * normSq (bR c) * chiUp 12462 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12462)).real (outputCentreEvent (paperCentres 12462))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12462

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12462
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12462) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12462) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12462)]
  norm_num [varianceMax]

end BstLean.Part266.Row12462

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12462
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12462) (hc : A1 c ∈ Eop 12462) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12462 : ℝ)) ≤ (12668381237 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12462 : ℝ) ≤ (111633329 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12462 : ℝ) + 2 * √12462 ≤ (6342633329 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12462) (hc : c ∈ BstLean.Part164.Eop2 12462) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12462 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12462) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12462 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12462) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12462).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12462) (FirstMatrix 12462))
    (h2 : c ∈ BstLean.Part164.Eop2 12462) (a : BstLean.Part161.Ix 12462) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12462

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12462
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12462) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12462) c ∈ BstLean.Part212.latitudeEvent 12462
      (ENNReal.ofReal (C / 12462))) (K : Set (Ix 12462)) :
    ∫ a in K, ((12462 : ℝ) * VR c a) ^ 2 ∂muI 12462 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12462

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12462
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12462 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12462 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12462 - 1 - 1) 80 ≤ (12618 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12462 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12618 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12462) ≤ (78 * 10 ^ 6 * ((12462 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12462 : ℝ) / 2 + 160) ≤ (4405986893 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12462 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12462 : ℝ) ^ 2 / 2 + 320 = 155302084 / 2 by norm_num,
    show (12462 : ℝ) ^ 2 / 2 + 160 = 155301764 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12462 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12462 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12462 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12462 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12462)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12462) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12462 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12462)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12462 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12462 ≤ (161 : ℝ) := by
  have hs : √(2 / (12462 : ℝ)) ≤ (12668381237 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12462 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12462 : ℝ) = 12462 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12462 : ℝ) + √12462 + gaussMomConst 80 ≤ 12583 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12462 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12462 : ℝ)) ≤ (113482071 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12462 4 +
      2 / (mA 12462 : ℝ) * frobEnvelopeSquared160 12462 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12462 4 +
      2 / (mA 12462 : ℝ) * frobEnvelopeSquared160 12462) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12462 : ℝ)) *
      operatorEnvelope160 12462 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12462 4 +
      2 / (mA 12462 : ℝ) * frobEnvelopeSquared160 12462) +
      transverseConstant160 * √(2 / (mA 12462 : ℝ)) * operatorEnvelope160 12462 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12462 4 +
      2 / (mA 12462 : ℝ) * frobEnvelopeSquared160 12462) +
      transverseConstant160 * √(2 / (mA 12462 : ℝ)) * operatorEnvelope160 12462 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12462 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12462 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12462 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12462 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12462

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12462
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12462) :=
  agentEv (paperDesignP 12462) (Energy32 12462) ∩
  agentEv (paperDesignP 12462) (freshRetainedEvent160 12462 4) ∩
  agentEv (paperDesignP 12462) (FirstMatrix 12462) ∩
  BstLean.Part164.Eop2 12462 ∩ outputCentreEvent (paperCentres 12462)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12462)).real
      (agentEv (paperDesignP 12462) (FirstMatrix 12462))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12462)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12462 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12462)).real (BstLean.Part164.Eop2 12462)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12462)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12462)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12462) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12462) hτ
  have hL := fresh_retained_charge160 (n := 12462) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12462) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12462 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12462) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12462 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12462) (hw : WINDOW (paperDesignP 12462) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12462))
    (hW : ∫ a in K, ((12462 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12462 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12462 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12462 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12462) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12462 : ℝ)) * eR c * 12462 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12462

/-! Exact rational parameters for the dimension-12463 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12463
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (590793 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12463 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12463 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12463 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12463.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12463] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12463 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12463 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12463.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12463

namespace BstLean.Part266.Row12463
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12463 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12463 : ℝ)) ≤ ((22694593 / 200000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12463 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12463)
  change 0 ≤ agentLayerAllowance 12463 at ha0
  have he : energyWeightAllowance 12463 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12463)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12463)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12463).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12463).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12463)) :
    ∫ a in K, fbR c a ^ k ∂muI 12463 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12463])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12463

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12463
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12463 / 12463 ≤ chi := by
  have hs : √((12463 : ℝ) * 12) ≤ (386724709 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12463}
    (hc : c ∈ outputCentreEvent (paperCentres 12463)) :
    normSq c.2.1.2 ≤ (2 / (12463 : ℝ)) * eR c * 12463 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12463 : ℝ) * normSq (bR c) * chiUp 12463 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12463)).real (outputCentreEvent (paperCentres 12463))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12463

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12463
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12463) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12463) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12463)]
  norm_num [varianceMax]

end BstLean.Part266.Row12463

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12463
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12463) (hc : A1 c ∈ Eop 12463) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12463 : ℝ)) ≤ (3166968247 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12463 : ℝ) ≤ (6977363 / 62500) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12463 : ℝ) + 2 * √12463 ≤ (396446113 / 31250) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12463) (hc : c ∈ BstLean.Part164.Eop2 12463) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12463 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12463) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12463 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12463) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12463).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12463) (FirstMatrix 12463))
    (h2 : c ∈ BstLean.Part164.Eop2 12463) (a : BstLean.Part161.Ix 12463) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12463

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12463
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12463) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12463) c ∈ BstLean.Part212.latitudeEvent 12463
      (ENNReal.ofReal (C / 12463))) (K : Set (Ix 12463)) :
    ∫ a in K, ((12463 : ℝ) * VR c a) ^ 2 ∂muI 12463 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12463

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12463
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12463 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12463 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12463 - 1 - 1) 80 ≤ (12619 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12463 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12619 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12463) ≤ (78 * 10 ^ 6 * ((12463 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12463 : ℝ) / 2 + 160) ≤ (2203170223 / 250000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12463 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12463 : ℝ) ^ 2 / 2 + 320 = 155327009 / 2 by norm_num,
    show (12463 : ℝ) ^ 2 / 2 + 160 = 155326689 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12463 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12463 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12463 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12463 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12463)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12463) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12463 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12463)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12463 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12463 ≤ (161 : ℝ) := by
  have hs : √(2 / (12463 : ℝ)) ≤ (3166968247 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12463 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12463 : ℝ) = 12463 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12463 : ℝ) + √12463 + gaussMomConst 80 ≤ 12584 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12463 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12463 : ℝ)) ≤ (22694593 / 200000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12463 4 +
      2 / (mA 12463 : ℝ) * frobEnvelopeSquared160 12463 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12463 4 +
      2 / (mA 12463 : ℝ) * frobEnvelopeSquared160 12463) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12463 : ℝ)) *
      operatorEnvelope160 12463 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12463 4 +
      2 / (mA 12463 : ℝ) * frobEnvelopeSquared160 12463) +
      transverseConstant160 * √(2 / (mA 12463 : ℝ)) * operatorEnvelope160 12463 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12463 4 +
      2 / (mA 12463 : ℝ) * frobEnvelopeSquared160 12463) +
      transverseConstant160 * √(2 / (mA 12463 : ℝ)) * operatorEnvelope160 12463 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12463 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12463 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12463 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12463 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12463

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12463
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12463) :=
  agentEv (paperDesignP 12463) (Energy32 12463) ∩
  agentEv (paperDesignP 12463) (freshRetainedEvent160 12463 4) ∩
  agentEv (paperDesignP 12463) (FirstMatrix 12463) ∩
  BstLean.Part164.Eop2 12463 ∩ outputCentreEvent (paperCentres 12463)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12463)).real
      (agentEv (paperDesignP 12463) (FirstMatrix 12463))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12463)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12463 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12463)).real (BstLean.Part164.Eop2 12463)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12463)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12463)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12463) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12463) hτ
  have hL := fresh_retained_charge160 (n := 12463) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12463) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12463 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12463) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12463 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12463) (hw : WINDOW (paperDesignP 12463) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12463))
    (hW : ∫ a in K, ((12463 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12463 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12463 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12463 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12463) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12463 : ℝ)) * eR c * 12463 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12463

/-! Exact rational parameters for the dimension-12464 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12464
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (590769 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12464 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12464 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12464 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12464.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12464] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12464 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12464 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12464.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12464

namespace BstLean.Part266.Row12464
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12464 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12464 : ℝ)) ≤ ((113463861 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12464 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12464)
  change 0 ≤ agentLayerAllowance 12464 at ha0
  have he : energyWeightAllowance 12464 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12464)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12464)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12464).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12464).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12464)) :
    ∫ a in K, fbR c a ^ k ∂muI 12464 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12464])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12464

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12464
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12464 / 12464 ≤ chi := by
  have hs : √((12464 : ℝ) * 12) ≤ (386740223 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12464}
    (hc : c ∈ outputCentreEvent (paperCentres 12464)) :
    normSq c.2.1.2 ≤ (2 / (12464 : ℝ)) * eR c * 12464 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12464 : ℝ) * normSq (bR c) * chiUp 12464 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12464)).real (outputCentreEvent (paperCentres 12464))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12464

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12464
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12464) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12464) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12464)]
  norm_num [varianceMax]

end BstLean.Part266.Row12464

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12464
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12464) (hc : A1 c ∈ Eop 12464) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12464 : ℝ)) ≤ (12667364799 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12464 : ℝ) ≤ (55821143 / 500000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12464 : ℝ) + 2 * √12464 ≤ (3171821143 / 250000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12464) (hc : c ∈ BstLean.Part164.Eop2 12464) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12464 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12464) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12464 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12464) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12464).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12464) (FirstMatrix 12464))
    (h2 : c ∈ BstLean.Part164.Eop2 12464) (a : BstLean.Part161.Ix 12464) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12464

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12464
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12464) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12464) c ∈ BstLean.Part212.latitudeEvent 12464
      (ENNReal.ofReal (C / 12464))) (K : Set (Ix 12464)) :
    ∫ a in K, ((12464 : ℝ) * VR c a) ^ 2 ∂muI 12464 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12464

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12464
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12464 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12464 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12464 - 1 - 1) 80 ≤ (12620 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12464 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12620 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12464) ≤ (78 * 10 ^ 6 * ((12464 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12464 : ℝ) / 2 + 160) ≤ (4406693999 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12464 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12464 : ℝ) ^ 2 / 2 + 320 = 155351936 / 2 by norm_num,
    show (12464 : ℝ) ^ 2 / 2 + 160 = 155351616 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12464 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12464 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12464 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12464 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12464)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12464) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12464 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12464)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12464 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12464 ≤ (161 : ℝ) := by
  have hs : √(2 / (12464 : ℝ)) ≤ (12667364799 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12464 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12464 : ℝ) = 12464 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12464 : ℝ) + √12464 + gaussMomConst 80 ≤ 12585 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12464 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12464 : ℝ)) ≤ (113463861 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12464 4 +
      2 / (mA 12464 : ℝ) * frobEnvelopeSquared160 12464 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12464 4 +
      2 / (mA 12464 : ℝ) * frobEnvelopeSquared160 12464) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12464 : ℝ)) *
      operatorEnvelope160 12464 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12464 4 +
      2 / (mA 12464 : ℝ) * frobEnvelopeSquared160 12464) +
      transverseConstant160 * √(2 / (mA 12464 : ℝ)) * operatorEnvelope160 12464 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12464 4 +
      2 / (mA 12464 : ℝ) * frobEnvelopeSquared160 12464) +
      transverseConstant160 * √(2 / (mA 12464 : ℝ)) * operatorEnvelope160 12464 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12464 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12464 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12464 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12464 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12464

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12464
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12464) :=
  agentEv (paperDesignP 12464) (Energy32 12464) ∩
  agentEv (paperDesignP 12464) (freshRetainedEvent160 12464 4) ∩
  agentEv (paperDesignP 12464) (FirstMatrix 12464) ∩
  BstLean.Part164.Eop2 12464 ∩ outputCentreEvent (paperCentres 12464)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12464)).real
      (agentEv (paperDesignP 12464) (FirstMatrix 12464))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12464)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12464 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12464)).real (BstLean.Part164.Eop2 12464)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12464)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12464)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12464) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12464) hτ
  have hL := fresh_retained_charge160 (n := 12464) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12464) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12464 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12464) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12464 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12464) (hw : WINDOW (paperDesignP 12464) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12464))
    (hW : ∫ a in K, ((12464 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12464 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12464 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12464 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12464) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12464 : ℝ)) * eR c * 12464 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12464

/-! Exact rational parameters for the dimension-12465 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12465
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (118149 / 20000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12465 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12465 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12465 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12465.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12465] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12465 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12465 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12465.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12465

namespace BstLean.Part266.Row12465
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12465 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12465 : ℝ)) ≤ ((113454759 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12465 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12465)
  change 0 ≤ agentLayerAllowance 12465 at ha0
  have he : energyWeightAllowance 12465 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12465)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12465)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12465).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12465).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12465)) :
    ∫ a in K, fbR c a ^ k ∂muI 12465 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12465])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12465

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12465
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12465 / 12465 ≤ chi := by
  have hs : √((12465 : ℝ) * 12) ≤ (386755737 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12465}
    (hc : c ∈ outputCentreEvent (paperCentres 12465)) :
    normSq c.2.1.2 ≤ (2 / (12465 : ℝ)) * eR c * 12465 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12465 : ℝ) * normSq (bR c) * chiUp 12465 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12465)).real (outputCentreEvent (paperCentres 12465))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12465

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12465
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12465) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12465) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12465)]
  norm_num [varianceMax]

end BstLean.Part266.Row12465

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12465
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12465) (hc : A1 c ∈ Eop 12465) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12465 : ℝ)) ≤ (12666856671 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12465 : ℝ) ≤ (22329353 / 200000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12465 : ℝ) + 2 * √12465 ≤ (1268829353 / 100000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12465) (hc : c ∈ BstLean.Part164.Eop2 12465) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12465 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12465) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12465 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12465) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12465).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12465) (FirstMatrix 12465))
    (h2 : c ∈ BstLean.Part164.Eop2 12465) (a : BstLean.Part161.Ix 12465) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12465

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12465
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12465) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12465) c ∈ BstLean.Part212.latitudeEvent 12465
      (ENNReal.ofReal (C / 12465))) (K : Set (Ix 12465)) :
    ∫ a in K, ((12465 : ℝ) * VR c a) ^ 2 ∂muI 12465 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12465

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12465
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12465 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12465 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12465 - 1 - 1) 80 ≤ (12621 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12465 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12621 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12465) ≤ (78 * 10 ^ 6 * ((12465 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12465 : ℝ) / 2 + 160) ≤ (137720236 / 15625) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12465 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12465 : ℝ) ^ 2 / 2 + 320 = 155376865 / 2 by norm_num,
    show (12465 : ℝ) ^ 2 / 2 + 160 = 155376545 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12465 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12465 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12465 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12465 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12465)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12465) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12465 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12465)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12465 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12465 ≤ (161 : ℝ) := by
  have hs : √(2 / (12465 : ℝ)) ≤ (12666856671 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12465 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12465 : ℝ) = 12465 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12465 : ℝ) + √12465 + gaussMomConst 80 ≤ 12586 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12465 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12465 : ℝ)) ≤ (113454759 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12465 4 +
      2 / (mA 12465 : ℝ) * frobEnvelopeSquared160 12465 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12465 4 +
      2 / (mA 12465 : ℝ) * frobEnvelopeSquared160 12465) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12465 : ℝ)) *
      operatorEnvelope160 12465 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12465 4 +
      2 / (mA 12465 : ℝ) * frobEnvelopeSquared160 12465) +
      transverseConstant160 * √(2 / (mA 12465 : ℝ)) * operatorEnvelope160 12465 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12465 4 +
      2 / (mA 12465 : ℝ) * frobEnvelopeSquared160 12465) +
      transverseConstant160 * √(2 / (mA 12465 : ℝ)) * operatorEnvelope160 12465 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12465 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12465 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12465 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12465 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12465

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12465
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12465) :=
  agentEv (paperDesignP 12465) (Energy32 12465) ∩
  agentEv (paperDesignP 12465) (freshRetainedEvent160 12465 4) ∩
  agentEv (paperDesignP 12465) (FirstMatrix 12465) ∩
  BstLean.Part164.Eop2 12465 ∩ outputCentreEvent (paperCentres 12465)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12465)).real
      (agentEv (paperDesignP 12465) (FirstMatrix 12465))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12465)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12465 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12465)).real (BstLean.Part164.Eop2 12465)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12465)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12465)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12465) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12465) hτ
  have hL := fresh_retained_charge160 (n := 12465) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12465) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12465 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12465) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12465 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12465) (hw : WINDOW (paperDesignP 12465) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12465))
    (hW : ∫ a in K, ((12465 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12465 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12465 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12465 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12465) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12465 : ℝ)) * eR c * 12465 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12465

/-! Exact rational parameters for the dimension-12466 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12466
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (590721 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12466 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12466 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12466 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12466.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12466] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12466 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12466 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12466.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12466

namespace BstLean.Part266.Row12466
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12466 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12466 : ℝ)) ≤ ((56722829 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12466 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12466)
  change 0 ≤ agentLayerAllowance 12466 at ha0
  have he : energyWeightAllowance 12466 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12466)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12466)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12466).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12466).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12466)) :
    ∫ a in K, fbR c a ^ k ∂muI 12466 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12466])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12466

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12466
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12466 / 12466 ≤ chi := by
  have hs : √((12466 : ℝ) * 12) ≤ (386771251 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12466}
    (hc : c ∈ outputCentreEvent (paperCentres 12466)) :
    normSq c.2.1.2 ≤ (2 / (12466 : ℝ)) * eR c * 12466 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12466 : ℝ) * normSq (bR c) * chiUp 12466 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12466)).real (outputCentreEvent (paperCentres 12466))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12466

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12466
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12466) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12466) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12466)]
  norm_num [varianceMax]

end BstLean.Part266.Row12466

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12466
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12466) (hc : A1 c ∈ Eop 12466) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12466 : ℝ)) ≤ (2533269721 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12466 : ℝ) ≤ (111651243 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12466 : ℝ) + 2 * √12466 ≤ (6344651243 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12466) (hc : c ∈ BstLean.Part164.Eop2 12466) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12466 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12466) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12466 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12466) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12466).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12466) (FirstMatrix 12466))
    (h2 : c ∈ BstLean.Part164.Eop2 12466) (a : BstLean.Part161.Ix 12466) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12466

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12466
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12466) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12466) c ∈ BstLean.Part212.latitudeEvent 12466
      (ENNReal.ofReal (C / 12466))) (K : Set (Ix 12466)) :
    ∫ a in K, ((12466 : ℝ) * VR c a) ^ 2 ∂muI 12466 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12466

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12466
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12466 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12466 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12466 - 1 - 1) 80 ≤ (12622 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12466 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12622 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12466) ≤ (78 * 10 ^ 6 * ((12466 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12466 : ℝ) / 2 + 160) ≤ (881480221 / 100000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12466 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12466 : ℝ) ^ 2 / 2 + 320 = 155401796 / 2 by norm_num,
    show (12466 : ℝ) ^ 2 / 2 + 160 = 155401476 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12466 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12466 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12466 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12466 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12466)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12466) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12466 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12466)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12466 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12466 ≤ (161 : ℝ) := by
  have hs : √(2 / (12466 : ℝ)) ≤ (2533269721 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12466 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12466 : ℝ) = 12466 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12466 : ℝ) + √12466 + gaussMomConst 80 ≤ 12587 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12466 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12466 : ℝ)) ≤ (56722829 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12466 4 +
      2 / (mA 12466 : ℝ) * frobEnvelopeSquared160 12466 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12466 4 +
      2 / (mA 12466 : ℝ) * frobEnvelopeSquared160 12466) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12466 : ℝ)) *
      operatorEnvelope160 12466 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12466 4 +
      2 / (mA 12466 : ℝ) * frobEnvelopeSquared160 12466) +
      transverseConstant160 * √(2 / (mA 12466 : ℝ)) * operatorEnvelope160 12466 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12466 4 +
      2 / (mA 12466 : ℝ) * frobEnvelopeSquared160 12466) +
      transverseConstant160 * √(2 / (mA 12466 : ℝ)) * operatorEnvelope160 12466 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12466 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12466 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12466 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12466 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12466

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12466
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12466) :=
  agentEv (paperDesignP 12466) (Energy32 12466) ∩
  agentEv (paperDesignP 12466) (freshRetainedEvent160 12466 4) ∩
  agentEv (paperDesignP 12466) (FirstMatrix 12466) ∩
  BstLean.Part164.Eop2 12466 ∩ outputCentreEvent (paperCentres 12466)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12466)).real
      (agentEv (paperDesignP 12466) (FirstMatrix 12466))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12466)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12466 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12466)).real (BstLean.Part164.Eop2 12466)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12466)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12466)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12466) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12466) hτ
  have hL := fresh_retained_charge160 (n := 12466) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12466) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12466 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12466) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12466 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12466) (hw : WINDOW (paperDesignP 12466) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12466))
    (hW : ∫ a in K, ((12466 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12466 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12466 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12466 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12466) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12466 : ℝ)) * eR c * 12466 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12466

/-! Exact rational parameters for the dimension-12467 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12467
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (295349 / 50000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12467 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12467 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12467 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12467.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12467] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12467 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12467 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12467.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12467

namespace BstLean.Part266.Row12467
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12467 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12467 : ℝ)) ≤ ((56718279 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12467 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12467)
  change 0 ≤ agentLayerAllowance 12467 at ha0
  have he : energyWeightAllowance 12467 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12467)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12467)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12467).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12467).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12467)) :
    ∫ a in K, fbR c a ^ k ∂muI 12467 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12467])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12467

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12467
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12467 / 12467 ≤ chi := by
  have hs : √((12467 : ℝ) * 12) ≤ (386786763 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12467}
    (hc : c ∈ outputCentreEvent (paperCentres 12467)) :
    normSq c.2.1.2 ≤ (2 / (12467 : ℝ)) * eR c * 12467 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12467 : ℝ) * normSq (bR c) * chiUp 12467 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12467)).real (outputCentreEvent (paperCentres 12467))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12467

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12467
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12467) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12467) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12467)]
  norm_num [varianceMax]

end BstLean.Part266.Row12467

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12467
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12467) (hc : A1 c ∈ Eop 12467) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12467 : ℝ)) ≤ (63329203 / 5000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12467 : ℝ) ≤ (111655721 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12467 : ℝ) + 2 * √12467 ≤ (6345155721 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12467) (hc : c ∈ BstLean.Part164.Eop2 12467) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12467 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12467) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12467 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12467) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12467).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12467) (FirstMatrix 12467))
    (h2 : c ∈ BstLean.Part164.Eop2 12467) (a : BstLean.Part161.Ix 12467) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12467

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12467
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12467) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12467) c ∈ BstLean.Part212.latitudeEvent 12467
      (ENNReal.ofReal (C / 12467))) (K : Set (Ix 12467)) :
    ∫ a in K, ((12467 : ℝ) * VR c a) ^ 2 ∂muI 12467 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12467

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12467
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12467 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12467 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12467 - 1 - 1) 80 ≤ (12623 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12467 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12623 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12467) ≤ (78 * 10 ^ 6 * ((12467 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12467 : ℝ) / 2 + 160) ≤ (2203877329 / 250000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12467 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12467 : ℝ) ^ 2 / 2 + 320 = 155426729 / 2 by norm_num,
    show (12467 : ℝ) ^ 2 / 2 + 160 = 155426409 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12467 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12467 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12467 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12467 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12467)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12467) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12467 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12467)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12467 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12467 ≤ (161 : ℝ) := by
  have hs : √(2 / (12467 : ℝ)) ≤ (63329203 / 5000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12467 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12467 : ℝ) = 12467 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12467 : ℝ) + √12467 + gaussMomConst 80 ≤ 12588 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12467 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12467 : ℝ)) ≤ (56718279 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12467 4 +
      2 / (mA 12467 : ℝ) * frobEnvelopeSquared160 12467 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12467 4 +
      2 / (mA 12467 : ℝ) * frobEnvelopeSquared160 12467) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12467 : ℝ)) *
      operatorEnvelope160 12467 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12467 4 +
      2 / (mA 12467 : ℝ) * frobEnvelopeSquared160 12467) +
      transverseConstant160 * √(2 / (mA 12467 : ℝ)) * operatorEnvelope160 12467 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12467 4 +
      2 / (mA 12467 : ℝ) * frobEnvelopeSquared160 12467) +
      transverseConstant160 * √(2 / (mA 12467 : ℝ)) * operatorEnvelope160 12467 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12467 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12467 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12467 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12467 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12467

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12467
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12467) :=
  agentEv (paperDesignP 12467) (Energy32 12467) ∩
  agentEv (paperDesignP 12467) (freshRetainedEvent160 12467 4) ∩
  agentEv (paperDesignP 12467) (FirstMatrix 12467) ∩
  BstLean.Part164.Eop2 12467 ∩ outputCentreEvent (paperCentres 12467)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12467)).real
      (agentEv (paperDesignP 12467) (FirstMatrix 12467))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12467)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12467 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12467)).real (BstLean.Part164.Eop2 12467)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12467)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12467)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12467) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12467) hτ
  have hL := fresh_retained_charge160 (n := 12467) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12467) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12467 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12467) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12467 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12467) (hw : WINDOW (paperDesignP 12467) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12467))
    (hW : ∫ a in K, ((12467 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12467 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12467 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12467 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12467) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12467 : ℝ)) * eR c * 12467 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12467

/-! Exact rational parameters for the dimension-12468 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12468
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (295337 / 50000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12468 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12468 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12468 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12468.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12468] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12468 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12468 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12468.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12468

namespace BstLean.Part266.Row12468
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12468 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12468 : ℝ)) ≤ ((5671373 / 50000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12468 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12468)
  change 0 ≤ agentLayerAllowance 12468 at ha0
  have he : energyWeightAllowance 12468 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12468)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12468)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12468).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12468).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12468)) :
    ∫ a in K, fbR c a ^ k ∂muI 12468 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12468])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12468

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12468
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12468 / 12468 ≤ chi := by
  have hs : √((12468 : ℝ) * 12) ≤ (96700569 / 250000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12468}
    (hc : c ∈ outputCentreEvent (paperCentres 12468)) :
    normSq c.2.1.2 ≤ (2 / (12468 : ℝ)) * eR c * 12468 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12468 : ℝ) * normSq (bR c) * chiUp 12468 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12468)).real (outputCentreEvent (paperCentres 12468))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12468

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12468
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12468) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12468) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12468)]
  norm_num [varianceMax]

end BstLean.Part266.Row12468

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12468
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12468) (hc : A1 c ∈ Eop 12468) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12468 : ℝ)) ≤ (791583291 / 62500000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12468 : ℝ) ≤ (111660199 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12468 : ℝ) + 2 * √12468 ≤ (6345660199 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12468) (hc : c ∈ BstLean.Part164.Eop2 12468) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12468 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12468) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12468 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12468) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12468).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12468) (FirstMatrix 12468))
    (h2 : c ∈ BstLean.Part164.Eop2 12468) (a : BstLean.Part161.Ix 12468) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12468

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12468
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12468) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12468) c ∈ BstLean.Part212.latitudeEvent 12468
      (ENNReal.ofReal (C / 12468))) (K : Set (Ix 12468)) :
    ∫ a in K, ((12468 : ℝ) * VR c a) ^ 2 ∂muI 12468 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12468

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12468
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12468 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12468 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12468 - 1 - 1) 80 ≤ (12624 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12468 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12624 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12468) ≤ (78 * 10 ^ 6 * ((12468 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12468 : ℝ) / 2 + 160) ≤ (8816216423 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12468 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12468 : ℝ) ^ 2 / 2 + 320 = 155451664 / 2 by norm_num,
    show (12468 : ℝ) ^ 2 / 2 + 160 = 155451344 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12468 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12468 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12468 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12468 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12468)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12468) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12468 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12468)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12468 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12468 ≤ (161 : ℝ) := by
  have hs : √(2 / (12468 : ℝ)) ≤ (791583291 / 62500000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12468 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12468 : ℝ) = 12468 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12468 : ℝ) + √12468 + gaussMomConst 80 ≤ 12589 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12468 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12468 : ℝ)) ≤ (5671373 / 50000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12468 4 +
      2 / (mA 12468 : ℝ) * frobEnvelopeSquared160 12468 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12468 4 +
      2 / (mA 12468 : ℝ) * frobEnvelopeSquared160 12468) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12468 : ℝ)) *
      operatorEnvelope160 12468 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12468 4 +
      2 / (mA 12468 : ℝ) * frobEnvelopeSquared160 12468) +
      transverseConstant160 * √(2 / (mA 12468 : ℝ)) * operatorEnvelope160 12468 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12468 4 +
      2 / (mA 12468 : ℝ) * frobEnvelopeSquared160 12468) +
      transverseConstant160 * √(2 / (mA 12468 : ℝ)) * operatorEnvelope160 12468 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12468 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12468 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12468 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12468 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12468

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12468
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12468) :=
  agentEv (paperDesignP 12468) (Energy32 12468) ∩
  agentEv (paperDesignP 12468) (freshRetainedEvent160 12468 4) ∩
  agentEv (paperDesignP 12468) (FirstMatrix 12468) ∩
  BstLean.Part164.Eop2 12468 ∩ outputCentreEvent (paperCentres 12468)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12468)).real
      (agentEv (paperDesignP 12468) (FirstMatrix 12468))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12468)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12468 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12468)).real (BstLean.Part164.Eop2 12468)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12468)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12468)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12468) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12468) hτ
  have hL := fresh_retained_charge160 (n := 12468) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12468) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12468 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12468) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12468 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12468) (hw : WINDOW (paperDesignP 12468) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12468))
    (hW : ∫ a in K, ((12468 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12468 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12468 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12468 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12468) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12468 : ℝ)) * eR c * 12468 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12468

/-! Exact rational parameters for the dimension-12469 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12469
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (11813 / 2000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12469 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12469 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12469 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12469.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12469] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12469 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12469 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12469.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12469

namespace BstLean.Part266.Row12469
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12469 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12469 : ℝ)) ≤ ((113418363 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12469 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12469)
  change 0 ≤ agentLayerAllowance 12469 at ha0
  have he : energyWeightAllowance 12469 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12469)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12469)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12469).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12469).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12469)) :
    ∫ a in K, fbR c a ^ k ∂muI 12469 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12469])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12469

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12469
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12469 / 12469 ≤ chi := by
  have hs : √((12469 : ℝ) * 12) ≤ (386817787 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12469}
    (hc : c ∈ outputCentreEvent (paperCentres 12469)) :
    normSq c.2.1.2 ≤ (2 / (12469 : ℝ)) * eR c * 12469 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12469 : ℝ) * normSq (bR c) * chiUp 12469 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12469)).real (outputCentreEvent (paperCentres 12469))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12469

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12469
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12469) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12469) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12469)]
  norm_num [varianceMax]

end BstLean.Part266.Row12469

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12469
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12469) (hc : A1 c ∈ Eop 12469) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12469 : ℝ)) ≤ (12664824773 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12469 : ℝ) ≤ (111664677 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12469 : ℝ) + 2 * √12469 ≤ (6346164677 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12469) (hc : c ∈ BstLean.Part164.Eop2 12469) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12469 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12469) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12469 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12469) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12469).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12469) (FirstMatrix 12469))
    (h2 : c ∈ BstLean.Part164.Eop2 12469) (a : BstLean.Part161.Ix 12469) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12469

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12469
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12469) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12469) c ∈ BstLean.Part212.latitudeEvent 12469
      (ENNReal.ofReal (C / 12469))) (K : Set (Ix 12469)) :
    ∫ a in K, ((12469 : ℝ) * VR c a) ^ 2 ∂muI 12469 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12469

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12469
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12469 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12469 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12469 - 1 - 1) 80 ≤ (12625 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12469 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12625 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12469) ≤ (78 * 10 ^ 6 * ((12469 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12469 : ℝ) / 2 + 160) ≤ (8816923529 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12469 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12469 : ℝ) ^ 2 / 2 + 320 = 155476601 / 2 by norm_num,
    show (12469 : ℝ) ^ 2 / 2 + 160 = 155476281 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12469 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12469 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12469 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12469 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12469)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12469) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12469 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12469)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12469 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12469 ≤ (161 : ℝ) := by
  have hs : √(2 / (12469 : ℝ)) ≤ (12664824773 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12469 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12469 : ℝ) = 12469 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12469 : ℝ) + √12469 + gaussMomConst 80 ≤ 12590 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12469 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12469 : ℝ)) ≤ (113418363 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12469 4 +
      2 / (mA 12469 : ℝ) * frobEnvelopeSquared160 12469 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12469 4 +
      2 / (mA 12469 : ℝ) * frobEnvelopeSquared160 12469) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12469 : ℝ)) *
      operatorEnvelope160 12469 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12469 4 +
      2 / (mA 12469 : ℝ) * frobEnvelopeSquared160 12469) +
      transverseConstant160 * √(2 / (mA 12469 : ℝ)) * operatorEnvelope160 12469 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12469 4 +
      2 / (mA 12469 : ℝ) * frobEnvelopeSquared160 12469) +
      transverseConstant160 * √(2 / (mA 12469 : ℝ)) * operatorEnvelope160 12469 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12469 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12469 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12469 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12469 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12469

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12469
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12469) :=
  agentEv (paperDesignP 12469) (Energy32 12469) ∩
  agentEv (paperDesignP 12469) (freshRetainedEvent160 12469 4) ∩
  agentEv (paperDesignP 12469) (FirstMatrix 12469) ∩
  BstLean.Part164.Eop2 12469 ∩ outputCentreEvent (paperCentres 12469)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12469)).real
      (agentEv (paperDesignP 12469) (FirstMatrix 12469))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12469)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12469 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12469)).real (BstLean.Part164.Eop2 12469)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12469)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12469)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12469) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12469) hτ
  have hL := fresh_retained_charge160 (n := 12469) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12469) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12469 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12469) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12469 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12469) (hw : WINDOW (paperDesignP 12469) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12469))
    (hW : ∫ a in K, ((12469 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12469 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12469 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12469 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12469) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12469 : ℝ)) * eR c * 12469 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12469

/-! Exact rational parameters for the dimension-12470 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12470
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (590627 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12470 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12470 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12470 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12470.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12470] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12470 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12470 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12470.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12470

namespace BstLean.Part266.Row12470
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12470 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12470 : ℝ)) ≤ ((28352317 / 250000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12470 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12470)
  change 0 ≤ agentLayerAllowance 12470 at ha0
  have he : energyWeightAllowance 12470 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12470)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12470)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12470).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12470).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12470)) :
    ∫ a in K, fbR c a ^ k ∂muI 12470 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12470])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12470

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12470
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12470 / 12470 ≤ chi := by
  have hs : √((12470 : ℝ) * 12) ≤ (193416649 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12470}
    (hc : c ∈ outputCentreEvent (paperCentres 12470)) :
    normSq c.2.1.2 ≤ (2 / (12470 : ℝ)) * eR c * 12470 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12470 : ℝ) * normSq (bR c) * chiUp 12470 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12470)).real (outputCentreEvent (paperCentres 12470))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12470

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12470
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12470) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12470) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12470)]
  norm_num [varianceMax]

end BstLean.Part266.Row12470

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12470
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12470) (hc : A1 c ∈ Eop 12470) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12470 : ℝ)) ≤ (12664316951 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12470 : ℝ) ≤ (22333831 / 200000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12470 : ℝ) + 2 * √12470 ≤ (1269333831 / 100000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12470) (hc : c ∈ BstLean.Part164.Eop2 12470) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12470 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12470) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12470 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12470) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12470).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12470) (FirstMatrix 12470))
    (h2 : c ∈ BstLean.Part164.Eop2 12470) (a : BstLean.Part161.Ix 12470) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12470

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12470
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12470) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12470) c ∈ BstLean.Part212.latitudeEvent 12470
      (ENNReal.ofReal (C / 12470))) (K : Set (Ix 12470)) :
    ∫ a in K, ((12470 : ℝ) * VR c a) ^ 2 ∂muI 12470 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12470

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12470
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12470 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12470 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12470 - 1 - 1) 80 ≤ (12626 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12470 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12626 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12470) ≤ (78 * 10 ^ 6 * ((12470 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12470 : ℝ) / 2 + 160) ≤ (1763526127 / 200000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12470 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12470 : ℝ) ^ 2 / 2 + 320 = 155501540 / 2 by norm_num,
    show (12470 : ℝ) ^ 2 / 2 + 160 = 155501220 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12470 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12470 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12470 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12470 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12470)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12470) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12470 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12470)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12470 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12470 ≤ (161 : ℝ) := by
  have hs : √(2 / (12470 : ℝ)) ≤ (12664316951 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12470 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12470 : ℝ) = 12470 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12470 : ℝ) + √12470 + gaussMomConst 80 ≤ 12591 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12470 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12470 : ℝ)) ≤ (28352317 / 250000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12470 4 +
      2 / (mA 12470 : ℝ) * frobEnvelopeSquared160 12470 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12470 4 +
      2 / (mA 12470 : ℝ) * frobEnvelopeSquared160 12470) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12470 : ℝ)) *
      operatorEnvelope160 12470 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12470 4 +
      2 / (mA 12470 : ℝ) * frobEnvelopeSquared160 12470) +
      transverseConstant160 * √(2 / (mA 12470 : ℝ)) * operatorEnvelope160 12470 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12470 4 +
      2 / (mA 12470 : ℝ) * frobEnvelopeSquared160 12470) +
      transverseConstant160 * √(2 / (mA 12470 : ℝ)) * operatorEnvelope160 12470 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12470 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12470 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12470 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12470 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12470

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12470
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12470) :=
  agentEv (paperDesignP 12470) (Energy32 12470) ∩
  agentEv (paperDesignP 12470) (freshRetainedEvent160 12470 4) ∩
  agentEv (paperDesignP 12470) (FirstMatrix 12470) ∩
  BstLean.Part164.Eop2 12470 ∩ outputCentreEvent (paperCentres 12470)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12470)).real
      (agentEv (paperDesignP 12470) (FirstMatrix 12470))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12470)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12470 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12470)).real (BstLean.Part164.Eop2 12470)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12470)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12470)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12470) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12470) hτ
  have hL := fresh_retained_charge160 (n := 12470) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12470) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12470 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12470) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12470 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12470) (hw : WINDOW (paperDesignP 12470) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12470))
    (hW : ∫ a in K, ((12470 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12470 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12470 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12470 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12470) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12470 : ℝ)) * eR c * 12470 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12470

/-! Exact rational parameters for the dimension-12471 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12471
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (590603 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12471 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12471 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12471 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12471.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12471] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12471 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12471 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12471.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12471

namespace BstLean.Part266.Row12471
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12471 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12471 : ℝ)) ≤ ((56700087 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12471 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12471)
  change 0 ≤ agentLayerAllowance 12471 at ha0
  have he : energyWeightAllowance 12471 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12471)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12471)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12471).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12471).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12471)) :
    ∫ a in K, fbR c a ^ k ∂muI 12471 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12471])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12471

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12471
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12471 / 12471 ≤ chi := by
  have hs : √((12471 : ℝ) * 12) ≤ (48356101 / 125000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12471}
    (hc : c ∈ outputCentreEvent (paperCentres 12471)) :
    normSq c.2.1.2 ≤ (2 / (12471 : ℝ)) * eR c * 12471 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12471 : ℝ) * normSq (bR c) * chiUp 12471 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12471)).real (outputCentreEvent (paperCentres 12471))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12471

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12471
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12471) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12471) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12471)]
  norm_num [varianceMax]

end BstLean.Part266.Row12471

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12471
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12471) (hc : A1 c ∈ Eop 12471) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12471 : ℝ)) ≤ (1266380919 / 100000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12471 : ℝ) ≤ (3489801 / 31250) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12471 : ℝ) + 2 * √12471 ≤ (198349176 / 15625) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12471) (hc : c ∈ BstLean.Part164.Eop2 12471) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12471 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12471) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12471 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12471) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12471).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12471) (FirstMatrix 12471))
    (h2 : c ∈ BstLean.Part164.Eop2 12471) (a : BstLean.Part161.Ix 12471) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12471

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12471
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12471) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12471) c ∈ BstLean.Part212.latitudeEvent 12471
      (ENNReal.ofReal (C / 12471))) (K : Set (Ix 12471)) :
    ∫ a in K, ((12471 : ℝ) * VR c a) ^ 2 ∂muI 12471 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12471

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12471
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12471 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12471 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12471 - 1 - 1) 80 ≤ (12627 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12471 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12627 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12471) ≤ (78 * 10 ^ 6 * ((12471 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12471 : ℝ) / 2 + 160) ≤ (8818337741 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12471 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12471 : ℝ) ^ 2 / 2 + 320 = 155526481 / 2 by norm_num,
    show (12471 : ℝ) ^ 2 / 2 + 160 = 155526161 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12471 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12471 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12471 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12471 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12471)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12471) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12471 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12471)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12471 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12471 ≤ (161 : ℝ) := by
  have hs : √(2 / (12471 : ℝ)) ≤ (1266380919 / 100000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12471 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12471 : ℝ) = 12471 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12471 : ℝ) + √12471 + gaussMomConst 80 ≤ 12592 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12471 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12471 : ℝ)) ≤ (56700087 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12471 4 +
      2 / (mA 12471 : ℝ) * frobEnvelopeSquared160 12471 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12471 4 +
      2 / (mA 12471 : ℝ) * frobEnvelopeSquared160 12471) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12471 : ℝ)) *
      operatorEnvelope160 12471 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12471 4 +
      2 / (mA 12471 : ℝ) * frobEnvelopeSquared160 12471) +
      transverseConstant160 * √(2 / (mA 12471 : ℝ)) * operatorEnvelope160 12471 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12471 4 +
      2 / (mA 12471 : ℝ) * frobEnvelopeSquared160 12471) +
      transverseConstant160 * √(2 / (mA 12471 : ℝ)) * operatorEnvelope160 12471 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12471 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12471 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12471 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12471 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12471

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12471
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12471) :=
  agentEv (paperDesignP 12471) (Energy32 12471) ∩
  agentEv (paperDesignP 12471) (freshRetainedEvent160 12471 4) ∩
  agentEv (paperDesignP 12471) (FirstMatrix 12471) ∩
  BstLean.Part164.Eop2 12471 ∩ outputCentreEvent (paperCentres 12471)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12471)).real
      (agentEv (paperDesignP 12471) (FirstMatrix 12471))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12471)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12471 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12471)).real (BstLean.Part164.Eop2 12471)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12471)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12471)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12471) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12471) hτ
  have hL := fresh_retained_charge160 (n := 12471) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12471) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12471 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12471) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12471 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12471) (hw : WINDOW (paperDesignP 12471) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12471))
    (hW : ∫ a in K, ((12471 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12471 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12471 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12471 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12471) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12471 : ℝ)) * eR c * 12471 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12471

/-! Exact rational parameters for the dimension-12472 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12472
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (590579 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12472 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12472 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12472 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12472.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12472] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12472 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12472 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12472.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12472

namespace BstLean.Part266.Row12472
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12472 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12472 : ℝ)) ≤ ((56695541 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12472 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12472)
  change 0 ≤ agentLayerAllowance 12472 at ha0
  have he : energyWeightAllowance 12472 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12472)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12472)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12472).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12472).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12472)) :
    ∫ a in K, fbR c a ^ k ∂muI 12472 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12472])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12472

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12472
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12472 / 12472 ≤ chi := by
  have hs : √((12472 : ℝ) * 12) ≤ (193432159 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12472}
    (hc : c ∈ outputCentreEvent (paperCentres 12472)) :
    normSq c.2.1.2 ≤ (2 / (12472 : ℝ)) * eR c * 12472 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12472 : ℝ) * normSq (bR c) * chiUp 12472 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12472)).real (outputCentreEvent (paperCentres 12472))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12472

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12472
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12472) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12472) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12472)]
  norm_num [varianceMax]

end BstLean.Part266.Row12472

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12472
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12472) (hc : A1 c ∈ Eop 12472) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12472 : ℝ)) ≤ (1266330149 / 100000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12472 : ℝ) ≤ (111678109 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12472 : ℝ) + 2 * √12472 ≤ (6347678109 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12472) (hc : c ∈ BstLean.Part164.Eop2 12472) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12472 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12472) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12472 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12472) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12472).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12472) (FirstMatrix 12472))
    (h2 : c ∈ BstLean.Part164.Eop2 12472) (a : BstLean.Part161.Ix 12472) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12472

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12472
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12472) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12472) c ∈ BstLean.Part212.latitudeEvent 12472
      (ENNReal.ofReal (C / 12472))) (K : Set (Ix 12472)) :
    ∫ a in K, ((12472 : ℝ) * VR c a) ^ 2 ∂muI 12472 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12472

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12472
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12472 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12472 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12472 - 1 - 1) 80 ≤ (12628 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12472 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12628 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12472) ≤ (78 * 10 ^ 6 * ((12472 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12472 : ℝ) / 2 + 160) ≤ (8819044847 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12472 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12472 : ℝ) ^ 2 / 2 + 320 = 155551424 / 2 by norm_num,
    show (12472 : ℝ) ^ 2 / 2 + 160 = 155551104 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12472 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12472 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12472 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12472 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12472)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12472) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12472 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12472)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12472 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12472 ≤ (161 : ℝ) := by
  have hs : √(2 / (12472 : ℝ)) ≤ (1266330149 / 100000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12472 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12472 : ℝ) = 12472 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12472 : ℝ) + √12472 + gaussMomConst 80 ≤ 12593 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12472 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12472 : ℝ)) ≤ (56695541 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12472 4 +
      2 / (mA 12472 : ℝ) * frobEnvelopeSquared160 12472 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12472 4 +
      2 / (mA 12472 : ℝ) * frobEnvelopeSquared160 12472) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12472 : ℝ)) *
      operatorEnvelope160 12472 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12472 4 +
      2 / (mA 12472 : ℝ) * frobEnvelopeSquared160 12472) +
      transverseConstant160 * √(2 / (mA 12472 : ℝ)) * operatorEnvelope160 12472 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12472 4 +
      2 / (mA 12472 : ℝ) * frobEnvelopeSquared160 12472) +
      transverseConstant160 * √(2 / (mA 12472 : ℝ)) * operatorEnvelope160 12472 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12472 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12472 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12472 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12472 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12472

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12472
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12472) :=
  agentEv (paperDesignP 12472) (Energy32 12472) ∩
  agentEv (paperDesignP 12472) (freshRetainedEvent160 12472 4) ∩
  agentEv (paperDesignP 12472) (FirstMatrix 12472) ∩
  BstLean.Part164.Eop2 12472 ∩ outputCentreEvent (paperCentres 12472)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12472)).real
      (agentEv (paperDesignP 12472) (FirstMatrix 12472))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12472)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12472 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12472)).real (BstLean.Part164.Eop2 12472)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12472)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12472)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12472) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12472) hτ
  have hL := fresh_retained_charge160 (n := 12472) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12472) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12472 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12472) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12472 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12472) (hw : WINDOW (paperDesignP 12472) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12472))
    (hW : ∫ a in K, ((12472 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12472 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12472 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12472 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12472) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12472 : ℝ)) * eR c * 12472 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12472

/-! Exact rational parameters for the dimension-12473 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12473
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (147639 / 25000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12473 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12473 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12473 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12473.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12473] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12473 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12473 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12473.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12473

namespace BstLean.Part266.Row12473
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12473 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12473 : ℝ)) ≤ ((113381991 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12473 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12473)
  change 0 ≤ agentLayerAllowance 12473 at ha0
  have he : energyWeightAllowance 12473 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12473)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12473)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12473).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12473).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12473)) :
    ∫ a in K, fbR c a ^ k ∂muI 12473 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12473])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12473

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12473
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12473 / 12473 ≤ chi := by
  have hs : √((12473 : ℝ) * 12) ≤ (386879827 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12473}
    (hc : c ∈ outputCentreEvent (paperCentres 12473)) :
    normSq c.2.1.2 ≤ (2 / (12473 : ℝ)) * eR c * 12473 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12473 : ℝ) * normSq (bR c) * chiUp 12473 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12473)).real (outputCentreEvent (paperCentres 12473))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12473

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12473
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12473) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12473) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12473)]
  norm_num [varianceMax]

end BstLean.Part266.Row12473

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12473
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12473) (hc : A1 c ∈ Eop 12473) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12473 : ℝ)) ≤ (12662793851 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12473 : ℝ) ≤ (55841293 / 500000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12473 : ℝ) + 2 * √12473 ≤ (3174091293 / 250000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12473) (hc : c ∈ BstLean.Part164.Eop2 12473) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12473 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12473) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12473 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12473) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12473).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12473) (FirstMatrix 12473))
    (h2 : c ∈ BstLean.Part164.Eop2 12473) (a : BstLean.Part161.Ix 12473) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12473

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12473
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12473) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12473) c ∈ BstLean.Part212.latitudeEvent 12473
      (ENNReal.ofReal (C / 12473))) (K : Set (Ix 12473)) :
    ∫ a in K, ((12473 : ℝ) * VR c a) ^ 2 ∂muI 12473 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12473

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12473
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12473 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12473 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12473 - 1 - 1) 80 ≤ (12629 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12473 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12629 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12473) ≤ (78 * 10 ^ 6 * ((12473 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12473 : ℝ) / 2 + 160) ≤ (8819751953 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12473 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12473 : ℝ) ^ 2 / 2 + 320 = 155576369 / 2 by norm_num,
    show (12473 : ℝ) ^ 2 / 2 + 160 = 155576049 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12473 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12473 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12473 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12473 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12473)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12473) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12473 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12473)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12473 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12473 ≤ (161 : ℝ) := by
  have hs : √(2 / (12473 : ℝ)) ≤ (12662793851 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12473 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12473 : ℝ) = 12473 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12473 : ℝ) + √12473 + gaussMomConst 80 ≤ 12594 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12473 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12473 : ℝ)) ≤ (113381991 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12473 4 +
      2 / (mA 12473 : ℝ) * frobEnvelopeSquared160 12473 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12473 4 +
      2 / (mA 12473 : ℝ) * frobEnvelopeSquared160 12473) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12473 : ℝ)) *
      operatorEnvelope160 12473 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12473 4 +
      2 / (mA 12473 : ℝ) * frobEnvelopeSquared160 12473) +
      transverseConstant160 * √(2 / (mA 12473 : ℝ)) * operatorEnvelope160 12473 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12473 4 +
      2 / (mA 12473 : ℝ) * frobEnvelopeSquared160 12473) +
      transverseConstant160 * √(2 / (mA 12473 : ℝ)) * operatorEnvelope160 12473 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12473 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12473 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12473 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12473 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12473

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12473
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12473) :=
  agentEv (paperDesignP 12473) (Energy32 12473) ∩
  agentEv (paperDesignP 12473) (freshRetainedEvent160 12473 4) ∩
  agentEv (paperDesignP 12473) (FirstMatrix 12473) ∩
  BstLean.Part164.Eop2 12473 ∩ outputCentreEvent (paperCentres 12473)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12473)).real
      (agentEv (paperDesignP 12473) (FirstMatrix 12473))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12473)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12473 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12473)).real (BstLean.Part164.Eop2 12473)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12473)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12473)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12473) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12473) hτ
  have hL := fresh_retained_charge160 (n := 12473) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12473) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12473 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12473) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12473 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12473) (hw : WINDOW (paperDesignP 12473) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12473))
    (hW : ∫ a in K, ((12473 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12473 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12473 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12473 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12473) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12473 : ℝ)) * eR c * 12473 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12473

/-! Exact rational parameters for the dimension-12474 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12474
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2630 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 219356 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
noncomputable def energyError : ℝ := 250 / 1000
noncomputable def locationError : ℝ := 75 / 1000
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 2000 / 10 ^ 6
noncomputable def displacementBudget : ℝ := (327 / 10 ^ 6) ^ 2
noncomputable def biasRootCap : ℝ := (147633 / 25000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12474 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12474 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]

theorem displacement_root : √displacementBudget = 327 / 10 ^ 6 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 327 / 10 ^ 6)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12474 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12474.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12474] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12474 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12474 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12474.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12474

namespace BstLean.Part266.Row12474
open BstLean.Part252
open Real MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part195 BstLean.Part222

theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num, rotationConstant_pow (by norm_num) (by norm_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ]

theorem energy_allowance_row : energyAllowance 12474 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12474 : ℝ)) ≤ ((113372901 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12474 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12474)
  change 0 ≤ agentLayerAllowance 12474 at ha0
  have he : energyWeightAllowance 12474 ≤ (1395 / 1000000 : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 7 / 5 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 7 / 5)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12474)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12474)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12474).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12474).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12474)) :
    ∫ a in K, fbR c a ^ k ∂muI 12474 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12474])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12474

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12474
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12474 / 12474 ≤ chi := by
  have hs : √((12474 : ℝ) * 12) ≤ (77379067 / 200000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12474}
    (hc : c ∈ outputCentreEvent (paperCentres 12474)) :
    normSq c.2.1.2 ≤ (2 / (12474 : ℝ)) * eR c * 12474 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12474 : ℝ) * normSq (bR c) * chiUp 12474 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12474)).real (outputCentreEvent (paperCentres 12474))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12474

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12474
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12474) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 161) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12474) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12474)]
  norm_num [varianceMax]

end BstLean.Part266.Row12474

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12474
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12474) (hc : A1 c ∈ Eop 12474) : OpB (A1 c) 161 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12474 : ℝ)) ≤ (6331143137 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12474 : ℝ) ≤ (111687063 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12474 : ℝ) + 2 * √12474 ≤ (6348687063 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12474) (hc : c ∈ BstLean.Part164.Eop2 12474) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12474 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12474) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12474 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12474) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12474).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12474) (FirstMatrix 12474))
    (h2 : c ∈ BstLean.Part164.Eop2 12474) (a : BstLean.Part161.Ix 12474) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12474

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12474
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12474) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12474) c ∈ BstLean.Part212.latitudeEvent 12474
      (ENNReal.ofReal (C / 12474))) (K : Set (Ix 12474)) :
    ∫ a in K, ((12474 : ℝ) * VR c a) ^ 2 ∂muI 12474 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12474

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12474
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12474 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12474 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12474 - 1 - 1) 80 ≤ (12630 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12474 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12630 : ℝ) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        norm_num
        linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp]
  refine (div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) 80)).trans ?_
  norm_num

theorem plane_envelope_row : planeEnvelope80 (mA 12474) ≤ (78 * 10 ^ 6 * ((12474 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12474 : ℝ) / 2 + 160) ≤ (8820459059 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12474 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12474 : ℝ) ^ 2 / 2 + 320 = 155601316 / 2 by norm_num,
    show (12474 : ℝ) ^ 2 / 2 + 160 = 155600996 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12474 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12474 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12474 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12474 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12474)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12474) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12474 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12474)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12474 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12474 ≤ (161 : ℝ) := by
  have hs : √(2 / (12474 : ℝ)) ≤ (6331143137 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12474 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12474 : ℝ) = 12474 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12474 : ℝ) + √12474 + gaussMomConst 80 ≤ 12595 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12474 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12474 : ℝ)) ≤ (113372901 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12474 4 +
      2 / (mA 12474 : ℝ) * frobEnvelopeSquared160 12474 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12474 4 +
      2 / (mA 12474 : ℝ) * frobEnvelopeSquared160 12474) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12474 : ℝ)) *
      operatorEnvelope160 12474 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12474 4 +
      2 / (mA 12474 : ℝ) * frobEnvelopeSquared160 12474) +
      transverseConstant160 * √(2 / (mA 12474 : ℝ)) * operatorEnvelope160 12474 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12474 4 +
      2 / (mA 12474 : ℝ) * frobEnvelopeSquared160 12474) +
      transverseConstant160 * √(2 / (mA 12474 : ℝ)) * operatorEnvelope160 12474 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12474 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12474 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12474 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12474 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12474

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12474
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12474) :=
  agentEv (paperDesignP 12474) (Energy32 12474) ∩
  agentEv (paperDesignP 12474) (freshRetainedEvent160 12474 4) ∩
  agentEv (paperDesignP 12474) (FirstMatrix 12474) ∩
  BstLean.Part164.Eop2 12474 ∩ outputCentreEvent (paperCentres 12474)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12474)).real
      (agentEv (paperDesignP 12474) (FirstMatrix 12474))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12474)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12474 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12474)).real (BstLean.Part164.Eop2 12474)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12474)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12474)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12474) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12474) hτ
  have hL := fresh_retained_charge160 (n := 12474) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12474) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12474 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12474) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12474 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12474) (hw : WINDOW (paperDesignP 12474) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12474))
    (hW : ∫ a in K, ((12474 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12474 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12474 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12474 ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact variance_of_matrix_events c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact full_location_moment_row c hw.1 hw.2.1 hE (by norm_num) (by decide) (by norm_num) K
  · exact variance_moment_row c he fresh_latitude_constant_pos_row latitude_constant_row hL K

theorem pass_centre_of_events (c : Ret 12474) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12474 : ℝ)) * eR c * 12474 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12474
