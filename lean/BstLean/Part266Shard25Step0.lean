import BstLean.Part252All
import BstLean.Part262ActualInterface
import BstLean.Part266Parameters


/-! Exact rational parameters for the dimension-12975 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12975
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
noncomputable def biasRootCap : ℝ := (289509 / 50000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12975 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12975 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12975 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12975.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12975] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12975 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12975 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12975.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12975

namespace BstLean.Part266.Row12975
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

theorem energy_allowance_row : energyAllowance 12975 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12975 : ℝ)) ≤ ((21799053 / 200000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12975 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12975)
  change 0 ≤ agentLayerAllowance 12975 at ha0
  have he : energyWeightAllowance 12975 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12975)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12975)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12975).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12975).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12975)) :
    ∫ a in K, fbR c a ^ k ∂muI 12975 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12975])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12975

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12975
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12975 / 12975 ≤ chi := by
  have hs : √((12975 : ℝ) * 12) ≤ (197294197 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12975}
    (hc : c ∈ outputCentreEvent (paperCentres 12975)) :
    normSq c.2.1.2 ≤ (2 / (12975 : ℝ)) * eR c * 12975 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12975 : ℝ) * normSq (bR c) * chiUp 12975 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12975)).real (outputCentreEvent (paperCentres 12975))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12975

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12975
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12975) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 164) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12975) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12975)]
  norm_num [varianceMax]

end BstLean.Part266.Row12975

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12975
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12975) (hc : A1 c ∈ Eop 12975) : OpB (A1 c) 164 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12975 : ℝ)) ≤ (2483083421 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12975 : ℝ) ≤ (56953929 / 500000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12975 : ℝ) + 2 * √12975 ≤ (3300703929 / 250000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12975) (hc : c ∈ BstLean.Part164.Eop2 12975) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12975 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12975) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12975 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12975) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12975).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12975) (FirstMatrix 12975))
    (h2 : c ∈ BstLean.Part164.Eop2 12975) (a : BstLean.Part161.Ix 12975) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12975

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12975
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12975) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12975) c ∈ BstLean.Part212.latitudeEvent 12975
      (ENNReal.ofReal (C / 12975))) (K : Set (Ix 12975)) :
    ∫ a in K, ((12975 : ℝ) * VR c a) ^ 2 ∂muI 12975 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12975

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12975
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12975 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12975 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12975 - 1 - 1) 80 ≤ (13131 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12975 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13131 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12975) ≤ (78 * 10 ^ 6 * ((12975 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12975 : ℝ) / 2 + 160) ≤ (4587359603 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12975 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12975 : ℝ) ^ 2 / 2 + 320 = 168351265 / 2 by norm_num,
    show (12975 : ℝ) ^ 2 / 2 + 160 = 168350945 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12975 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12975 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12975 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12975 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12975)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12975) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12975 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12975)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12975 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12975 ≤ (164 : ℝ) := by
  have hs : √(2 / (12975 : ℝ)) ≤ (2483083421 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12975 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12975 : ℝ) = 12975 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12975 : ℝ) + √12975 + gaussMomConst 80 ≤ 13098 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12975 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12975 : ℝ)) ≤ (21799053 / 200000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12975 4 +
      2 / (mA 12975 : ℝ) * frobEnvelopeSquared160 12975 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12975 4 +
      2 / (mA 12975 : ℝ) * frobEnvelopeSquared160 12975) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12975 : ℝ)) *
      operatorEnvelope160 12975 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12975 4 +
      2 / (mA 12975 : ℝ) * frobEnvelopeSquared160 12975) +
      transverseConstant160 * √(2 / (mA 12975 : ℝ)) * operatorEnvelope160 12975 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12975 4 +
      2 / (mA 12975 : ℝ) * frobEnvelopeSquared160 12975) +
      transverseConstant160 * √(2 / (mA 12975 : ℝ)) * operatorEnvelope160 12975 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12975 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12975 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12975 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12975 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12975

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12975
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12975) :=
  agentEv (paperDesignP 12975) (Energy32 12975) ∩
  agentEv (paperDesignP 12975) (freshRetainedEvent160 12975 4) ∩
  agentEv (paperDesignP 12975) (FirstMatrix 12975) ∩
  BstLean.Part164.Eop2 12975 ∩ outputCentreEvent (paperCentres 12975)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12975)).real
      (agentEv (paperDesignP 12975) (FirstMatrix 12975))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12975)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12975 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12975)).real (BstLean.Part164.Eop2 12975)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12975)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12975)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12975) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12975) hτ
  have hL := fresh_retained_charge160 (n := 12975) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12975) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12975 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12975) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12975 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12975) (hw : WINDOW (paperDesignP 12975) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12975))
    (hW : ∫ a in K, ((12975 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12975 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12975 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12975 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12975) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12975 : ℝ)) * eR c * 12975 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12975

/-! Exact rational parameters for the dimension-12976 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12976
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
noncomputable def biasRootCap : ℝ := (144749 / 25000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12976 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12976 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12976 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12976.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12976] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12976 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12976 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12976.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12976

namespace BstLean.Part266.Row12976
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

theorem energy_allowance_row : energyAllowance 12976 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12976 : ℝ)) ≤ ((54493433 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12976 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12976)
  change 0 ≤ agentLayerAllowance 12976 at ha0
  have he : energyWeightAllowance 12976 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12976)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12976)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12976).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12976).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12976)) :
    ∫ a in K, fbR c a ^ k ∂muI 12976 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12976])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12976

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12976
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12976 / 12976 ≤ chi := by
  have hs : √((12976 : ℝ) * 12) ≤ (394603599 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12976}
    (hc : c ∈ outputCentreEvent (paperCentres 12976)) :
    normSq c.2.1.2 ≤ (2 / (12976 : ℝ)) * eR c * 12976 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12976 : ℝ) * normSq (bR c) * chiUp 12976 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12976)).real (outputCentreEvent (paperCentres 12976))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12976

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12976
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12976) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 164) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12976) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12976)]
  norm_num [varianceMax]

end BstLean.Part266.Row12976

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12976
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12976) (hc : A1 c ∈ Eop 12976) : OpB (A1 c) 164 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12976 : ℝ)) ≤ (12414938697 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12976 : ℝ) ≤ (113912247 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12976 : ℝ) + 2 * √12976 ≤ (6601912247 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12976) (hc : c ∈ BstLean.Part164.Eop2 12976) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12976 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12976) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12976 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12976) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12976).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12976) (FirstMatrix 12976))
    (h2 : c ∈ BstLean.Part164.Eop2 12976) (a : BstLean.Part161.Ix 12976) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12976

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12976
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12976) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12976) c ∈ BstLean.Part212.latitudeEvent 12976
      (ENNReal.ofReal (C / 12976))) (K : Set (Ix 12976)) :
    ∫ a in K, ((12976 : ℝ) * VR c a) ^ 2 ∂muI 12976 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12976

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12976
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12976 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12976 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12976 - 1 - 1) 80 ≤ (13132 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12976 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13132 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12976) ≤ (78 * 10 ^ 6 * ((12976 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12976 : ℝ) / 2 + 160) ≤ (1146928289 / 125000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12976 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12976 : ℝ) ^ 2 / 2 + 320 = 168377216 / 2 by norm_num,
    show (12976 : ℝ) ^ 2 / 2 + 160 = 168376896 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12976 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12976 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12976 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12976 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12976)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12976) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12976 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12976)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12976 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12976 ≤ (164 : ℝ) := by
  have hs : √(2 / (12976 : ℝ)) ≤ (12414938697 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12976 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12976 : ℝ) = 12976 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12976 : ℝ) + √12976 + gaussMomConst 80 ≤ 13099 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12976 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12976 : ℝ)) ≤ (54493433 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12976 4 +
      2 / (mA 12976 : ℝ) * frobEnvelopeSquared160 12976 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12976 4 +
      2 / (mA 12976 : ℝ) * frobEnvelopeSquared160 12976) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12976 : ℝ)) *
      operatorEnvelope160 12976 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12976 4 +
      2 / (mA 12976 : ℝ) * frobEnvelopeSquared160 12976) +
      transverseConstant160 * √(2 / (mA 12976 : ℝ)) * operatorEnvelope160 12976 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12976 4 +
      2 / (mA 12976 : ℝ) * frobEnvelopeSquared160 12976) +
      transverseConstant160 * √(2 / (mA 12976 : ℝ)) * operatorEnvelope160 12976 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12976 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12976 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12976 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12976 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12976

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12976
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12976) :=
  agentEv (paperDesignP 12976) (Energy32 12976) ∩
  agentEv (paperDesignP 12976) (freshRetainedEvent160 12976 4) ∩
  agentEv (paperDesignP 12976) (FirstMatrix 12976) ∩
  BstLean.Part164.Eop2 12976 ∩ outputCentreEvent (paperCentres 12976)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12976)).real
      (agentEv (paperDesignP 12976) (FirstMatrix 12976))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12976)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12976 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12976)).real (BstLean.Part164.Eop2 12976)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12976)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12976)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12976) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12976) hτ
  have hL := fresh_retained_charge160 (n := 12976) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12976) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12976 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12976) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12976 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12976) (hw : WINDOW (paperDesignP 12976) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12976))
    (hW : ∫ a in K, ((12976 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12976 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12976 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12976 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12976) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12976 : ℝ)) * eR c * 12976 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12976

/-! Exact rational parameters for the dimension-12977 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12977
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
noncomputable def biasRootCap : ℝ := (289487 / 50000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12977 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12977 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12977 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12977.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12977] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12977 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12977 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12977.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12977

namespace BstLean.Part266.Row12977
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

theorem energy_allowance_row : energyAllowance 12977 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12977 : ℝ)) ≤ ((108978467 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12977 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12977)
  change 0 ≤ agentLayerAllowance 12977 at ha0
  have he : energyWeightAllowance 12977 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12977)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12977)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12977).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12977).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12977)) :
    ∫ a in K, fbR c a ^ k ∂muI 12977 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12977])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12977

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12977
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12977 / 12977 ≤ chi := by
  have hs : √((12977 : ℝ) * 12) ≤ (98654701 / 250000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12977}
    (hc : c ∈ outputCentreEvent (paperCentres 12977)) :
    normSq c.2.1.2 ≤ (2 / (12977 : ℝ)) * eR c * 12977 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12977 : ℝ) * normSq (bR c) * chiUp 12977 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12977)).real (outputCentreEvent (paperCentres 12977))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12977

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12977
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12977) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 164) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12977) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12977)]
  norm_num [varianceMax]

end BstLean.Part266.Row12977

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12977
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12977) (hc : A1 c ∈ Eop 12977) : OpB (A1 c) 164 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12977 : ℝ)) ≤ (1551807543 / 125000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12977 : ℝ) ≤ (113916637 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12977 : ℝ) + 2 * √12977 ≤ (6602416637 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12977) (hc : c ∈ BstLean.Part164.Eop2 12977) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12977 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12977) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12977 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12977) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12977).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12977) (FirstMatrix 12977))
    (h2 : c ∈ BstLean.Part164.Eop2 12977) (a : BstLean.Part161.Ix 12977) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12977

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12977
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12977) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12977) c ∈ BstLean.Part212.latitudeEvent 12977
      (ENNReal.ofReal (C / 12977))) (K : Set (Ix 12977)) :
    ∫ a in K, ((12977 : ℝ) * VR c a) ^ 2 ∂muI 12977 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12977

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12977
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12977 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12977 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12977 - 1 - 1) 80 ≤ (13133 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12977 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13133 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12977) ≤ (78 * 10 ^ 6 * ((12977 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12977 : ℝ) / 2 + 160) ≤ (4588066709 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12977 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12977 : ℝ) ^ 2 / 2 + 320 = 168403169 / 2 by norm_num,
    show (12977 : ℝ) ^ 2 / 2 + 160 = 168402849 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12977 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12977 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12977 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12977 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12977)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12977) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12977 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12977)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12977 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12977 ≤ (164 : ℝ) := by
  have hs : √(2 / (12977 : ℝ)) ≤ (1551807543 / 125000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12977 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12977 : ℝ) = 12977 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12977 : ℝ) + √12977 + gaussMomConst 80 ≤ 13100 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12977 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12977 : ℝ)) ≤ (108978467 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12977 4 +
      2 / (mA 12977 : ℝ) * frobEnvelopeSquared160 12977 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12977 4 +
      2 / (mA 12977 : ℝ) * frobEnvelopeSquared160 12977) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12977 : ℝ)) *
      operatorEnvelope160 12977 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12977 4 +
      2 / (mA 12977 : ℝ) * frobEnvelopeSquared160 12977) +
      transverseConstant160 * √(2 / (mA 12977 : ℝ)) * operatorEnvelope160 12977 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12977 4 +
      2 / (mA 12977 : ℝ) * frobEnvelopeSquared160 12977) +
      transverseConstant160 * √(2 / (mA 12977 : ℝ)) * operatorEnvelope160 12977 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12977 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12977 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12977 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12977 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12977

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12977
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12977) :=
  agentEv (paperDesignP 12977) (Energy32 12977) ∩
  agentEv (paperDesignP 12977) (freshRetainedEvent160 12977 4) ∩
  agentEv (paperDesignP 12977) (FirstMatrix 12977) ∩
  BstLean.Part164.Eop2 12977 ∩ outputCentreEvent (paperCentres 12977)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12977)).real
      (agentEv (paperDesignP 12977) (FirstMatrix 12977))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12977)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12977 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12977)).real (BstLean.Part164.Eop2 12977)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12977)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12977)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12977) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12977) hτ
  have hL := fresh_retained_charge160 (n := 12977) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12977) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12977 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12977) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12977 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12977) (hw : WINDOW (paperDesignP 12977) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12977))
    (hW : ∫ a in K, ((12977 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12977 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12977 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12977 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12977) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12977 : ℝ)) * eR c * 12977 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12977

/-! Exact rational parameters for the dimension-12978 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12978
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
noncomputable def biasRootCap : ℝ := (578951 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12978 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12978 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12978 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12978.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12978] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12978 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12978 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12978.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12978

namespace BstLean.Part266.Row12978
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

theorem energy_allowance_row : energyAllowance 12978 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12978 : ℝ)) ≤ ((10897007 / 100000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12978 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12978)
  change 0 ≤ agentLayerAllowance 12978 at ha0
  have he : energyWeightAllowance 12978 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12978)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12978)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12978).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12978).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12978)) :
    ∫ a in K, fbR c a ^ k ∂muI 12978 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12978])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12978

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12978
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12978 / 12978 ≤ chi := by
  have hs : √((12978 : ℝ) * 12) ≤ (49329251 / 125000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12978}
    (hc : c ∈ outputCentreEvent (paperCentres 12978)) :
    normSq c.2.1.2 ≤ (2 / (12978 : ℝ)) * eR c * 12978 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12978 : ℝ) * normSq (bR c) * chiUp 12978 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12978)).real (outputCentreEvent (paperCentres 12978))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12978

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12978
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12978) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 164) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12978) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12978)]
  norm_num [varianceMax]

end BstLean.Part266.Row12978

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12978
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12978) (hc : A1 c ∈ Eop 12978) : OpB (A1 c) 164 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12978 : ℝ)) ≤ (6206991023 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12978 : ℝ) ≤ (56960513 / 500000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12978 : ℝ) + 2 * √12978 ≤ (3301460513 / 250000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12978) (hc : c ∈ BstLean.Part164.Eop2 12978) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12978 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12978) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12978 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12978) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12978).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12978) (FirstMatrix 12978))
    (h2 : c ∈ BstLean.Part164.Eop2 12978) (a : BstLean.Part161.Ix 12978) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12978

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12978
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12978) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12978) c ∈ BstLean.Part212.latitudeEvent 12978
      (ENNReal.ofReal (C / 12978))) (K : Set (Ix 12978)) :
    ∫ a in K, ((12978 : ℝ) * VR c a) ^ 2 ∂muI 12978 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12978

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12978
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12978 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12978 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12978 - 1 - 1) 80 ≤ (13134 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12978 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13134 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12978) ≤ (78 * 10 ^ 6 * ((12978 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12978 : ℝ) / 2 + 160) ≤ (2294210131 / 250000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12978 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12978 : ℝ) ^ 2 / 2 + 320 = 168429124 / 2 by norm_num,
    show (12978 : ℝ) ^ 2 / 2 + 160 = 168428804 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12978 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12978 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12978 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12978 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12978)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12978) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12978 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12978)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12978 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12978 ≤ (164 : ℝ) := by
  have hs : √(2 / (12978 : ℝ)) ≤ (6206991023 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12978 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12978 : ℝ) = 12978 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12978 : ℝ) + √12978 + gaussMomConst 80 ≤ 13101 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12978 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12978 : ℝ)) ≤ (10897007 / 100000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12978 4 +
      2 / (mA 12978 : ℝ) * frobEnvelopeSquared160 12978 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12978 4 +
      2 / (mA 12978 : ℝ) * frobEnvelopeSquared160 12978) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12978 : ℝ)) *
      operatorEnvelope160 12978 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12978 4 +
      2 / (mA 12978 : ℝ) * frobEnvelopeSquared160 12978) +
      transverseConstant160 * √(2 / (mA 12978 : ℝ)) * operatorEnvelope160 12978 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12978 4 +
      2 / (mA 12978 : ℝ) * frobEnvelopeSquared160 12978) +
      transverseConstant160 * √(2 / (mA 12978 : ℝ)) * operatorEnvelope160 12978 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12978 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12978 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12978 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12978 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12978

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12978
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12978) :=
  agentEv (paperDesignP 12978) (Energy32 12978) ∩
  agentEv (paperDesignP 12978) (freshRetainedEvent160 12978 4) ∩
  agentEv (paperDesignP 12978) (FirstMatrix 12978) ∩
  BstLean.Part164.Eop2 12978 ∩ outputCentreEvent (paperCentres 12978)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12978)).real
      (agentEv (paperDesignP 12978) (FirstMatrix 12978))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12978)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12978 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12978)).real (BstLean.Part164.Eop2 12978)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12978)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12978)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12978) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12978) hτ
  have hL := fresh_retained_charge160 (n := 12978) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12978) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12978 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12978) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12978 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12978) (hw : WINDOW (paperDesignP 12978) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12978))
    (hW : ∫ a in K, ((12978 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12978 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12978 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12978 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12978) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12978 : ℝ)) * eR c * 12978 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12978

/-! Exact rational parameters for the dimension-12979 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12979
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
noncomputable def biasRootCap : ℝ := (578929 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12979 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12979 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12979 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12979.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12979] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12979 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12979 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12979.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12979

namespace BstLean.Part266.Row12979
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

theorem energy_allowance_row : energyAllowance 12979 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12979 : ℝ)) ≤ ((54480837 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12979 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12979)
  change 0 ≤ agentLayerAllowance 12979 at ha0
  have he : energyWeightAllowance 12979 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12979)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12979)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12979).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12979).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12979)) :
    ∫ a in K, fbR c a ^ k ∂muI 12979 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12979])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12979

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12979
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12979 / 12979 ≤ chi := by
  have hs : √((12979 : ℝ) * 12) ≤ (98662303 / 250000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12979}
    (hc : c ∈ outputCentreEvent (paperCentres 12979)) :
    normSq c.2.1.2 ≤ (2 / (12979 : ℝ)) * eR c * 12979 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12979 : ℝ) * normSq (bR c) * chiUp 12979 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12979)).real (outputCentreEvent (paperCentres 12979))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12979

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12979
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12979) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 164) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12979) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12979)]
  norm_num [varianceMax]

end BstLean.Part266.Row12979

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12979
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12979) (hc : A1 c ∈ Eop 12979) : OpB (A1 c) 164 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12979 : ℝ)) ≤ (12413503803 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12979 : ℝ) ≤ (22785083 / 200000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12979 : ℝ) + 2 * √12979 ≤ (1320685083 / 100000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12979) (hc : c ∈ BstLean.Part164.Eop2 12979) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12979 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12979) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12979 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12979) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12979).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12979) (FirstMatrix 12979))
    (h2 : c ∈ BstLean.Part164.Eop2 12979) (a : BstLean.Part161.Ix 12979) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12979

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12979
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12979) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12979) c ∈ BstLean.Part212.latitudeEvent 12979
      (ENNReal.ofReal (C / 12979))) (K : Set (Ix 12979)) :
    ∫ a in K, ((12979 : ℝ) * VR c a) ^ 2 ∂muI 12979 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12979

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12979
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12979 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12979 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12979 - 1 - 1) 80 ≤ (13135 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12979 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13135 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12979) ≤ (78 * 10 ^ 6 * ((12979 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12979 : ℝ) / 2 + 160) ≤ (917754763 / 100000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12979 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12979 : ℝ) ^ 2 / 2 + 320 = 168455081 / 2 by norm_num,
    show (12979 : ℝ) ^ 2 / 2 + 160 = 168454761 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12979 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12979 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12979 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12979 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12979)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12979) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12979 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12979)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12979 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12979 ≤ (164 : ℝ) := by
  have hs : √(2 / (12979 : ℝ)) ≤ (12413503803 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12979 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12979 : ℝ) = 12979 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12979 : ℝ) + √12979 + gaussMomConst 80 ≤ 13102 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12979 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12979 : ℝ)) ≤ (54480837 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12979 4 +
      2 / (mA 12979 : ℝ) * frobEnvelopeSquared160 12979 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12979 4 +
      2 / (mA 12979 : ℝ) * frobEnvelopeSquared160 12979) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12979 : ℝ)) *
      operatorEnvelope160 12979 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12979 4 +
      2 / (mA 12979 : ℝ) * frobEnvelopeSquared160 12979) +
      transverseConstant160 * √(2 / (mA 12979 : ℝ)) * operatorEnvelope160 12979 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12979 4 +
      2 / (mA 12979 : ℝ) * frobEnvelopeSquared160 12979) +
      transverseConstant160 * √(2 / (mA 12979 : ℝ)) * operatorEnvelope160 12979 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12979 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12979 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12979 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12979 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12979

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12979
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12979) :=
  agentEv (paperDesignP 12979) (Energy32 12979) ∩
  agentEv (paperDesignP 12979) (freshRetainedEvent160 12979 4) ∩
  agentEv (paperDesignP 12979) (FirstMatrix 12979) ∩
  BstLean.Part164.Eop2 12979 ∩ outputCentreEvent (paperCentres 12979)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12979)).real
      (agentEv (paperDesignP 12979) (FirstMatrix 12979))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12979)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12979 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12979)).real (BstLean.Part164.Eop2 12979)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12979)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12979)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12979) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12979) hτ
  have hL := fresh_retained_charge160 (n := 12979) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12979) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12979 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12979) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12979 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12979) (hw : WINDOW (paperDesignP 12979) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12979))
    (hW : ∫ a in K, ((12979 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12979 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12979 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12979 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12979) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12979 : ℝ)) * eR c * 12979 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12979

/-! Exact rational parameters for the dimension-12980 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12980
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
noncomputable def biasRootCap : ℝ := (578907 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12980 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12980 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12980 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12980.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12980] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12980 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12980 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12980.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12980

namespace BstLean.Part266.Row12980
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

theorem energy_allowance_row : energyAllowance 12980 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12980 : ℝ)) ≤ ((340479 / 3125000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12980 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12980)
  change 0 ≤ agentLayerAllowance 12980 at ha0
  have he : energyWeightAllowance 12980 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12980)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12980)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12980).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12980).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12980)) :
    ∫ a in K, fbR c a ^ k ∂muI 12980 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12980])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12980

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12980
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12980 / 12980 ≤ chi := by
  have hs : √((12980 : ℝ) * 12) ≤ (78932883 / 200000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12980}
    (hc : c ∈ outputCentreEvent (paperCentres 12980)) :
    normSq c.2.1.2 ≤ (2 / (12980 : ℝ)) * eR c * 12980 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12980 : ℝ) * normSq (bR c) * chiUp 12980 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12980)).real (outputCentreEvent (paperCentres 12980))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12980

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12980
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12980) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 164) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12980) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12980)]
  norm_num [varianceMax]

end BstLean.Part266.Row12980

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12980
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12980) (hc : A1 c ∈ Eop 12980) : OpB (A1 c) 164 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12980 : ℝ)) ≤ (775814101 / 62500000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12980 : ℝ) ≤ (113929803 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12980 : ℝ) + 2 * √12980 ≤ (6603929803 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12980) (hc : c ∈ BstLean.Part164.Eop2 12980) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12980 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12980) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12980 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12980) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12980).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12980) (FirstMatrix 12980))
    (h2 : c ∈ BstLean.Part164.Eop2 12980) (a : BstLean.Part161.Ix 12980) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12980

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12980
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12980) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12980) c ∈ BstLean.Part212.latitudeEvent 12980
      (ENNReal.ofReal (C / 12980))) (K : Set (Ix 12980)) :
    ∫ a in K, ((12980 : ℝ) * VR c a) ^ 2 ∂muI 12980 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12980

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12980
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12980 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12980 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12980 - 1 - 1) 80 ≤ (13136 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12980 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13136 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12980) ≤ (78 * 10 ^ 6 * ((12980 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12980 : ℝ) / 2 + 160) ≤ (9178254737 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12980 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12980 : ℝ) ^ 2 / 2 + 320 = 168481040 / 2 by norm_num,
    show (12980 : ℝ) ^ 2 / 2 + 160 = 168480720 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12980 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12980 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12980 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12980 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12980)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12980) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12980 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12980)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12980 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12980 ≤ (164 : ℝ) := by
  have hs : √(2 / (12980 : ℝ)) ≤ (775814101 / 62500000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12980 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12980 : ℝ) = 12980 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12980 : ℝ) + √12980 + gaussMomConst 80 ≤ 13103 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12980 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12980 : ℝ)) ≤ (340479 / 3125000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12980 4 +
      2 / (mA 12980 : ℝ) * frobEnvelopeSquared160 12980 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12980 4 +
      2 / (mA 12980 : ℝ) * frobEnvelopeSquared160 12980) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12980 : ℝ)) *
      operatorEnvelope160 12980 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12980 4 +
      2 / (mA 12980 : ℝ) * frobEnvelopeSquared160 12980) +
      transverseConstant160 * √(2 / (mA 12980 : ℝ)) * operatorEnvelope160 12980 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12980 4 +
      2 / (mA 12980 : ℝ) * frobEnvelopeSquared160 12980) +
      transverseConstant160 * √(2 / (mA 12980 : ℝ)) * operatorEnvelope160 12980 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12980 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12980 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12980 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12980 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12980

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12980
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12980) :=
  agentEv (paperDesignP 12980) (Energy32 12980) ∩
  agentEv (paperDesignP 12980) (freshRetainedEvent160 12980 4) ∩
  agentEv (paperDesignP 12980) (FirstMatrix 12980) ∩
  BstLean.Part164.Eop2 12980 ∩ outputCentreEvent (paperCentres 12980)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12980)).real
      (agentEv (paperDesignP 12980) (FirstMatrix 12980))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12980)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12980 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12980)).real (BstLean.Part164.Eop2 12980)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12980)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12980)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12980) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12980) hτ
  have hL := fresh_retained_charge160 (n := 12980) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12980) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12980 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12980) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12980 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12980) (hw : WINDOW (paperDesignP 12980) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12980))
    (hW : ∫ a in K, ((12980 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12980 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12980 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12980 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12980) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12980 : ℝ)) * eR c * 12980 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12980

/-! Exact rational parameters for the dimension-12981 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12981
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
noncomputable def biasRootCap : ℝ := (144721 / 25000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12981 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12981 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12981 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12981.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12981] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12981 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12981 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12981.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12981

namespace BstLean.Part266.Row12981
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

theorem energy_allowance_row : energyAllowance 12981 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12981 : ℝ)) ≤ ((54472443 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12981 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12981)
  change 0 ≤ agentLayerAllowance 12981 at ha0
  have he : energyWeightAllowance 12981 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12981)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12981)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12981).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12981).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12981)) :
    ∫ a in K, fbR c a ^ k ∂muI 12981 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12981])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12981

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12981
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12981 / 12981 ≤ chi := by
  have hs : √((12981 : ℝ) * 12) ≤ (394679617 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12981}
    (hc : c ∈ outputCentreEvent (paperCentres 12981)) :
    normSq c.2.1.2 ≤ (2 / (12981 : ℝ)) * eR c * 12981 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12981 : ℝ) * normSq (bR c) * chiUp 12981 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12981)).real (outputCentreEvent (paperCentres 12981))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12981

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12981
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12981) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 164) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12981) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12981)]
  norm_num [varianceMax]

end BstLean.Part266.Row12981

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12981
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12981) (hc : A1 c ∈ Eop 12981) : OpB (A1 c) 164 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12981 : ℝ)) ≤ (3103136871 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12981 : ℝ) ≤ (7120887 / 62500) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12981 : ℝ) + 2 * √12981 ≤ (412777137 / 31250) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12981) (hc : c ∈ BstLean.Part164.Eop2 12981) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12981 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12981) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12981 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12981) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12981).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12981) (FirstMatrix 12981))
    (h2 : c ∈ BstLean.Part164.Eop2 12981) (a : BstLean.Part161.Ix 12981) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12981

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12981
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12981) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12981) c ∈ BstLean.Part212.latitudeEvent 12981
      (ENNReal.ofReal (C / 12981))) (K : Set (Ix 12981)) :
    ∫ a in K, ((12981 : ℝ) * VR c a) ^ 2 ∂muI 12981 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12981

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12981
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12981 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12981 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12981 - 1 - 1) 80 ≤ (13137 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12981 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13137 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12981) ≤ (78 * 10 ^ 6 * ((12981 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12981 : ℝ) / 2 + 160) ≤ (9178961843 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12981 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12981 : ℝ) ^ 2 / 2 + 320 = 168507001 / 2 by norm_num,
    show (12981 : ℝ) ^ 2 / 2 + 160 = 168506681 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12981 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12981 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12981 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12981 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12981)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12981) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12981 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12981)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12981 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12981 ≤ (164 : ℝ) := by
  have hs : √(2 / (12981 : ℝ)) ≤ (3103136871 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12981 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12981 : ℝ) = 12981 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12981 : ℝ) + √12981 + gaussMomConst 80 ≤ 13104 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12981 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12981 : ℝ)) ≤ (54472443 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12981 4 +
      2 / (mA 12981 : ℝ) * frobEnvelopeSquared160 12981 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12981 4 +
      2 / (mA 12981 : ℝ) * frobEnvelopeSquared160 12981) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12981 : ℝ)) *
      operatorEnvelope160 12981 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12981 4 +
      2 / (mA 12981 : ℝ) * frobEnvelopeSquared160 12981) +
      transverseConstant160 * √(2 / (mA 12981 : ℝ)) * operatorEnvelope160 12981 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12981 4 +
      2 / (mA 12981 : ℝ) * frobEnvelopeSquared160 12981) +
      transverseConstant160 * √(2 / (mA 12981 : ℝ)) * operatorEnvelope160 12981 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12981 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12981 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12981 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12981 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12981

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12981
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12981) :=
  agentEv (paperDesignP 12981) (Energy32 12981) ∩
  agentEv (paperDesignP 12981) (freshRetainedEvent160 12981 4) ∩
  agentEv (paperDesignP 12981) (FirstMatrix 12981) ∩
  BstLean.Part164.Eop2 12981 ∩ outputCentreEvent (paperCentres 12981)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12981)).real
      (agentEv (paperDesignP 12981) (FirstMatrix 12981))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12981)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12981 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12981)).real (BstLean.Part164.Eop2 12981)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12981)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12981)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12981) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12981) hτ
  have hL := fresh_retained_charge160 (n := 12981) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12981) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12981 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12981) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12981 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12981) (hw : WINDOW (paperDesignP 12981) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12981))
    (hW : ∫ a in K, ((12981 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12981 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12981 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12981 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12981) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12981 : ℝ)) * eR c * 12981 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12981

/-! Exact rational parameters for the dimension-12982 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12982
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
noncomputable def biasRootCap : ℝ := (289431 / 50000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12982 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12982 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12982 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12982.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12982] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12982 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12982 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12982.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12982

namespace BstLean.Part266.Row12982
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

theorem energy_allowance_row : energyAllowance 12982 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12982 : ℝ)) ≤ ((54468247 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12982 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12982)
  change 0 ≤ agentLayerAllowance 12982 at ha0
  have he : energyWeightAllowance 12982 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12982)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12982)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12982).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12982).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12982)) :
    ∫ a in K, fbR c a ^ k ∂muI 12982 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12982])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12982

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12982
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12982 / 12982 ≤ chi := by
  have hs : √((12982 : ℝ) * 12) ≤ (394694819 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12982}
    (hc : c ∈ outputCentreEvent (paperCentres 12982)) :
    normSq c.2.1.2 ≤ (2 / (12982 : ℝ)) * eR c * 12982 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12982 : ℝ) * normSq (bR c) * chiUp 12982 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12982)).real (outputCentreEvent (paperCentres 12982))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12982

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12982
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12982) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 164) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12982) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12982)]
  norm_num [varianceMax]

end BstLean.Part266.Row12982

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12982
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12982) (hc : A1 c ∈ Eop 12982) : OpB (A1 c) 164 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12982 : ℝ)) ≤ (12412069407 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12982 : ℝ) ≤ (5696929 / 50000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12982 : ℝ) + 2 * √12982 ≤ (330246929 / 25000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12982) (hc : c ∈ BstLean.Part164.Eop2 12982) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12982 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12982) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12982 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12982) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12982).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12982) (FirstMatrix 12982))
    (h2 : c ∈ BstLean.Part164.Eop2 12982) (a : BstLean.Part161.Ix 12982) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12982

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12982
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12982) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12982) c ∈ BstLean.Part212.latitudeEvent 12982
      (ENNReal.ofReal (C / 12982))) (K : Set (Ix 12982)) :
    ∫ a in K, ((12982 : ℝ) * VR c a) ^ 2 ∂muI 12982 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12982

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12982
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12982 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12982 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12982 - 1 - 1) 80 ≤ (13138 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12982 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13138 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12982) ≤ (78 * 10 ^ 6 * ((12982 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12982 : ℝ) / 2 + 160) ≤ (9179668949 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12982 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12982 : ℝ) ^ 2 / 2 + 320 = 168532964 / 2 by norm_num,
    show (12982 : ℝ) ^ 2 / 2 + 160 = 168532644 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12982 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12982 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12982 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12982 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12982)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12982) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12982 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12982)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12982 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12982 ≤ (164 : ℝ) := by
  have hs : √(2 / (12982 : ℝ)) ≤ (12412069407 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12982 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12982 : ℝ) = 12982 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12982 : ℝ) + √12982 + gaussMomConst 80 ≤ 13105 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12982 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12982 : ℝ)) ≤ (54468247 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12982 4 +
      2 / (mA 12982 : ℝ) * frobEnvelopeSquared160 12982 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12982 4 +
      2 / (mA 12982 : ℝ) * frobEnvelopeSquared160 12982) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12982 : ℝ)) *
      operatorEnvelope160 12982 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12982 4 +
      2 / (mA 12982 : ℝ) * frobEnvelopeSquared160 12982) +
      transverseConstant160 * √(2 / (mA 12982 : ℝ)) * operatorEnvelope160 12982 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12982 4 +
      2 / (mA 12982 : ℝ) * frobEnvelopeSquared160 12982) +
      transverseConstant160 * √(2 / (mA 12982 : ℝ)) * operatorEnvelope160 12982 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12982 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12982 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12982 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12982 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12982

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12982
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12982) :=
  agentEv (paperDesignP 12982) (Energy32 12982) ∩
  agentEv (paperDesignP 12982) (freshRetainedEvent160 12982 4) ∩
  agentEv (paperDesignP 12982) (FirstMatrix 12982) ∩
  BstLean.Part164.Eop2 12982 ∩ outputCentreEvent (paperCentres 12982)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12982)).real
      (agentEv (paperDesignP 12982) (FirstMatrix 12982))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12982)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12982 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12982)).real (BstLean.Part164.Eop2 12982)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12982)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12982)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12982) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12982) hτ
  have hL := fresh_retained_charge160 (n := 12982) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12982) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12982 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12982) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12982 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12982) (hw : WINDOW (paperDesignP 12982) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12982))
    (hW : ∫ a in K, ((12982 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12982 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12982 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12982 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12982) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12982 : ℝ)) * eR c * 12982 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12982

/-! Exact rational parameters for the dimension-12983 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12983
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
noncomputable def biasRootCap : ℝ := (14471 / 2500000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12983 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12983 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12983 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12983.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12983] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12983 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12983 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12983.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12983

namespace BstLean.Part266.Row12983
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

theorem energy_allowance_row : energyAllowance 12983 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12983 : ℝ)) ≤ ((13616013 / 125000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12983 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12983)
  change 0 ≤ agentLayerAllowance 12983 at ha0
  have he : energyWeightAllowance 12983 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12983)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12983)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12983).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12983).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12983)) :
    ∫ a in K, fbR c a ^ k ∂muI 12983 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12983])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12983

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12983
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12983 / 12983 ≤ chi := by
  have hs : √((12983 : ℝ) * 12) ≤ (394710021 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12983}
    (hc : c ∈ outputCentreEvent (paperCentres 12983)) :
    normSq c.2.1.2 ≤ (2 / (12983 : ℝ)) * eR c * 12983 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12983 : ℝ) * normSq (bR c) * chiUp 12983 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12983)).real (outputCentreEvent (paperCentres 12983))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12983

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12983
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12983) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 164) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12983) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12983)]
  norm_num [varianceMax]

end BstLean.Part266.Row12983

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12983
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12983) (hc : A1 c ∈ Eop 12983) : OpB (A1 c) 164 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12983 : ℝ)) ≤ (6205795693 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12983 : ℝ) ≤ (113942969 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12983 : ℝ) + 2 * √12983 ≤ (6605442969 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12983) (hc : c ∈ BstLean.Part164.Eop2 12983) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12983 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12983) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12983 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12983) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12983).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12983) (FirstMatrix 12983))
    (h2 : c ∈ BstLean.Part164.Eop2 12983) (a : BstLean.Part161.Ix 12983) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12983

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12983
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12983) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12983) c ∈ BstLean.Part212.latitudeEvent 12983
      (ENNReal.ofReal (C / 12983))) (K : Set (Ix 12983)) :
    ∫ a in K, ((12983 : ℝ) * VR c a) ^ 2 ∂muI 12983 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12983

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12983
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12983 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12983 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12983 - 1 - 1) 80 ≤ (13139 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12983 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13139 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12983) ≤ (78 * 10 ^ 6 * ((12983 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12983 : ℝ) / 2 + 160) ≤ (1836075211 / 200000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12983 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12983 : ℝ) ^ 2 / 2 + 320 = 168558929 / 2 by norm_num,
    show (12983 : ℝ) ^ 2 / 2 + 160 = 168558609 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12983 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12983 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12983 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12983 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12983)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12983) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12983 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12983)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12983 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12983 ≤ (164 : ℝ) := by
  have hs : √(2 / (12983 : ℝ)) ≤ (6205795693 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12983 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12983 : ℝ) = 12983 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12983 : ℝ) + √12983 + gaussMomConst 80 ≤ 13106 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12983 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12983 : ℝ)) ≤ (13616013 / 125000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12983 4 +
      2 / (mA 12983 : ℝ) * frobEnvelopeSquared160 12983 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12983 4 +
      2 / (mA 12983 : ℝ) * frobEnvelopeSquared160 12983) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12983 : ℝ)) *
      operatorEnvelope160 12983 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12983 4 +
      2 / (mA 12983 : ℝ) * frobEnvelopeSquared160 12983) +
      transverseConstant160 * √(2 / (mA 12983 : ℝ)) * operatorEnvelope160 12983 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12983 4 +
      2 / (mA 12983 : ℝ) * frobEnvelopeSquared160 12983) +
      transverseConstant160 * √(2 / (mA 12983 : ℝ)) * operatorEnvelope160 12983 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12983 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12983 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12983 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12983 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12983

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12983
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12983) :=
  agentEv (paperDesignP 12983) (Energy32 12983) ∩
  agentEv (paperDesignP 12983) (freshRetainedEvent160 12983 4) ∩
  agentEv (paperDesignP 12983) (FirstMatrix 12983) ∩
  BstLean.Part164.Eop2 12983 ∩ outputCentreEvent (paperCentres 12983)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12983)).real
      (agentEv (paperDesignP 12983) (FirstMatrix 12983))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12983)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12983 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12983)).real (BstLean.Part164.Eop2 12983)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12983)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12983)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12983) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12983) hτ
  have hL := fresh_retained_charge160 (n := 12983) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12983) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12983 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12983) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12983 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12983) (hw : WINDOW (paperDesignP 12983) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12983))
    (hW : ∫ a in K, ((12983 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12983 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12983 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12983 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12983) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12983 : ℝ)) * eR c * 12983 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12983

/-! Exact rational parameters for the dimension-12984 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12984
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
noncomputable def biasRootCap : ℝ := (289409 / 50000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12984 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12984 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12984 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12984.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12984] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12984 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12984 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12984.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12984

namespace BstLean.Part266.Row12984
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

theorem energy_allowance_row : energyAllowance 12984 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12984 : ℝ)) ≤ ((54459857 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12984 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12984)
  change 0 ≤ agentLayerAllowance 12984 at ha0
  have he : energyWeightAllowance 12984 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12984)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12984)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12984).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12984).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12984)) :
    ∫ a in K, fbR c a ^ k ∂muI 12984 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12984])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12984

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12984
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12984 / 12984 ≤ chi := by
  have hs : √((12984 : ℝ) * 12) ≤ (394725221 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12984}
    (hc : c ∈ outputCentreEvent (paperCentres 12984)) :
    normSq c.2.1.2 ≤ (2 / (12984 : ℝ)) * eR c * 12984 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12984 : ℝ) * normSq (bR c) * chiUp 12984 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12984)).real (outputCentreEvent (paperCentres 12984))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12984

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12984
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12984) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 164) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12984) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12984)]
  norm_num [varianceMax]

end BstLean.Part266.Row12984

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12984
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12984) (hc : A1 c ∈ Eop 12984) : OpB (A1 c) 164 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12984 : ℝ)) ≤ (12411113419 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12984 : ℝ) ≤ (113947357 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12984 : ℝ) + 2 * √12984 ≤ (6605947357 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12984) (hc : c ∈ BstLean.Part164.Eop2 12984) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12984 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12984) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12984 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12984) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12984).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12984) (FirstMatrix 12984))
    (h2 : c ∈ BstLean.Part164.Eop2 12984) (a : BstLean.Part161.Ix 12984) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12984

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12984
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12984) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12984) c ∈ BstLean.Part212.latitudeEvent 12984
      (ENNReal.ofReal (C / 12984))) (K : Set (Ix 12984)) :
    ∫ a in K, ((12984 : ℝ) * VR c a) ^ 2 ∂muI 12984 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12984

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12984
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12984 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12984 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12984 - 1 - 1) 80 ≤ (13140 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12984 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13140 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12984) ≤ (78 * 10 ^ 6 * ((12984 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12984 : ℝ) / 2 + 160) ≤ (9181083161 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12984 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12984 : ℝ) ^ 2 / 2 + 320 = 168584896 / 2 by norm_num,
    show (12984 : ℝ) ^ 2 / 2 + 160 = 168584576 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12984 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12984 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12984 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12984 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12984)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12984) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12984 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12984)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12984 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12984 ≤ (164 : ℝ) := by
  have hs : √(2 / (12984 : ℝ)) ≤ (12411113419 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12984 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12984 : ℝ) = 12984 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12984 : ℝ) + √12984 + gaussMomConst 80 ≤ 13107 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12984 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12984 : ℝ)) ≤ (54459857 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12984 4 +
      2 / (mA 12984 : ℝ) * frobEnvelopeSquared160 12984 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12984 4 +
      2 / (mA 12984 : ℝ) * frobEnvelopeSquared160 12984) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12984 : ℝ)) *
      operatorEnvelope160 12984 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12984 4 +
      2 / (mA 12984 : ℝ) * frobEnvelopeSquared160 12984) +
      transverseConstant160 * √(2 / (mA 12984 : ℝ)) * operatorEnvelope160 12984 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12984 4 +
      2 / (mA 12984 : ℝ) * frobEnvelopeSquared160 12984) +
      transverseConstant160 * √(2 / (mA 12984 : ℝ)) * operatorEnvelope160 12984 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12984 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12984 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12984 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12984 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12984

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12984
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12984) :=
  agentEv (paperDesignP 12984) (Energy32 12984) ∩
  agentEv (paperDesignP 12984) (freshRetainedEvent160 12984 4) ∩
  agentEv (paperDesignP 12984) (FirstMatrix 12984) ∩
  BstLean.Part164.Eop2 12984 ∩ outputCentreEvent (paperCentres 12984)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12984)).real
      (agentEv (paperDesignP 12984) (FirstMatrix 12984))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12984)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12984 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12984)).real (BstLean.Part164.Eop2 12984)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12984)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12984)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12984) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12984) hτ
  have hL := fresh_retained_charge160 (n := 12984) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12984) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12984 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12984) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12984 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12984) (hw : WINDOW (paperDesignP 12984) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12984))
    (hW : ∫ a in K, ((12984 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12984 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12984 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12984 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12984) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12984 : ℝ)) * eR c * 12984 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12984

/-! Exact rational parameters for the dimension-12985 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12985
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
noncomputable def biasRootCap : ℝ := (115759 / 20000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12985 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12985 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12985 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12985.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12985] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12985 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12985 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12985.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12985

namespace BstLean.Part266.Row12985
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

theorem energy_allowance_row : energyAllowance 12985 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12985 : ℝ)) ≤ ((54455663 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12985 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12985)
  change 0 ≤ agentLayerAllowance 12985 at ha0
  have he : energyWeightAllowance 12985 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12985)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12985)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12985).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12985).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12985)) :
    ∫ a in K, fbR c a ^ k ∂muI 12985 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12985])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12985

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12985
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12985 / 12985 ≤ chi := by
  have hs : √((12985 : ℝ) * 12) ≤ (197370211 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12985}
    (hc : c ∈ outputCentreEvent (paperCentres 12985)) :
    normSq c.2.1.2 ≤ (2 / (12985 : ℝ)) * eR c * 12985 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12985 : ℝ) * normSq (bR c) * chiUp 12985 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12985)).real (outputCentreEvent (paperCentres 12985))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12985

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12985
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12985) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 164) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12985) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12985)]
  norm_num [varianceMax]

end BstLean.Part266.Row12985

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12985
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12985) (hc : A1 c ∈ Eop 12985) : OpB (A1 c) 164 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12985 : ℝ)) ≤ (3102658877 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12985 : ℝ) ≤ (22790349 / 200000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12985 : ℝ) + 2 * √12985 ≤ (1321290349 / 100000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12985) (hc : c ∈ BstLean.Part164.Eop2 12985) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12985 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12985) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12985 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12985) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12985).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12985) (FirstMatrix 12985))
    (h2 : c ∈ BstLean.Part164.Eop2 12985) (a : BstLean.Part161.Ix 12985) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12985

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12985
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12985) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12985) c ∈ BstLean.Part212.latitudeEvent 12985
      (ENNReal.ofReal (C / 12985))) (K : Set (Ix 12985)) :
    ∫ a in K, ((12985 : ℝ) * VR c a) ^ 2 ∂muI 12985 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12985

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12985
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12985 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12985 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12985 - 1 - 1) 80 ≤ (13141 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12985 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13141 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12985) ≤ (78 * 10 ^ 6 * ((12985 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12985 : ℝ) / 2 + 160) ≤ (9181790267 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12985 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12985 : ℝ) ^ 2 / 2 + 320 = 168610865 / 2 by norm_num,
    show (12985 : ℝ) ^ 2 / 2 + 160 = 168610545 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12985 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12985 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12985 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12985 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12985)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12985) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12985 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12985)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12985 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12985 ≤ (164 : ℝ) := by
  have hs : √(2 / (12985 : ℝ)) ≤ (3102658877 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12985 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12985 : ℝ) = 12985 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12985 : ℝ) + √12985 + gaussMomConst 80 ≤ 13108 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12985 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12985 : ℝ)) ≤ (54455663 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12985 4 +
      2 / (mA 12985 : ℝ) * frobEnvelopeSquared160 12985 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12985 4 +
      2 / (mA 12985 : ℝ) * frobEnvelopeSquared160 12985) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12985 : ℝ)) *
      operatorEnvelope160 12985 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12985 4 +
      2 / (mA 12985 : ℝ) * frobEnvelopeSquared160 12985) +
      transverseConstant160 * √(2 / (mA 12985 : ℝ)) * operatorEnvelope160 12985 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12985 4 +
      2 / (mA 12985 : ℝ) * frobEnvelopeSquared160 12985) +
      transverseConstant160 * √(2 / (mA 12985 : ℝ)) * operatorEnvelope160 12985 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12985 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12985 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12985 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12985 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12985

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12985
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12985) :=
  agentEv (paperDesignP 12985) (Energy32 12985) ∩
  agentEv (paperDesignP 12985) (freshRetainedEvent160 12985 4) ∩
  agentEv (paperDesignP 12985) (FirstMatrix 12985) ∩
  BstLean.Part164.Eop2 12985 ∩ outputCentreEvent (paperCentres 12985)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12985)).real
      (agentEv (paperDesignP 12985) (FirstMatrix 12985))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12985)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12985 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12985)).real (BstLean.Part164.Eop2 12985)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12985)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12985)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12985) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12985) hτ
  have hL := fresh_retained_charge160 (n := 12985) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12985) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12985 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12985) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12985 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12985) (hw : WINDOW (paperDesignP 12985) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12985))
    (hW : ∫ a in K, ((12985 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12985 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12985 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12985 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12985) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12985 : ℝ)) * eR c * 12985 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12985

/-! Exact rational parameters for the dimension-12986 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12986
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
noncomputable def biasRootCap : ℝ := (578773 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12986 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12986 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12986 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12986.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12986] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12986 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12986 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12986.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12986

namespace BstLean.Part266.Row12986
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

theorem energy_allowance_row : energyAllowance 12986 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12986 : ℝ)) ≤ ((108902939 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12986 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12986)
  change 0 ≤ agentLayerAllowance 12986 at ha0
  have he : energyWeightAllowance 12986 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12986)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12986)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12986).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12986).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12986)) :
    ∫ a in K, fbR c a ^ k ∂muI 12986 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12986])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12986

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12986
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12986 / 12986 ≤ chi := by
  have hs : √((12986 : ℝ) * 12) ≤ (394755621 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12986}
    (hc : c ∈ outputCentreEvent (paperCentres 12986)) :
    normSq c.2.1.2 ≤ (2 / (12986 : ℝ)) * eR c * 12986 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12986 : ℝ) * normSq (bR c) * chiUp 12986 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12986)).real (outputCentreEvent (paperCentres 12986))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12986

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12986
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12986) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 164) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12986) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12986)]
  norm_num [varianceMax]

end BstLean.Part266.Row12986

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12986
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12986) (hc : A1 c ∈ Eop 12986) : OpB (A1 c) 164 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12986 : ℝ)) ≤ (3102539413 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12986 : ℝ) ≤ (28489033 / 250000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12986 : ℝ) + 2 * √12986 ≤ (1651739033 / 125000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12986) (hc : c ∈ BstLean.Part164.Eop2 12986) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12986 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12986) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12986 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12986) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12986).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12986) (FirstMatrix 12986))
    (h2 : c ∈ BstLean.Part164.Eop2 12986) (a : BstLean.Part161.Ix 12986) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12986

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12986
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12986) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12986) c ∈ BstLean.Part212.latitudeEvent 12986
      (ENNReal.ofReal (C / 12986))) (K : Set (Ix 12986)) :
    ∫ a in K, ((12986 : ℝ) * VR c a) ^ 2 ∂muI 12986 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12986

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12986
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12986 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12986 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12986 - 1 - 1) 80 ≤ (13142 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12986 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13142 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12986) ≤ (78 * 10 ^ 6 * ((12986 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12986 : ℝ) / 2 + 160) ≤ (9182497373 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12986 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12986 : ℝ) ^ 2 / 2 + 320 = 168636836 / 2 by norm_num,
    show (12986 : ℝ) ^ 2 / 2 + 160 = 168636516 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12986 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12986 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12986 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12986 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12986)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12986) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12986 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12986)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12986 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12986 ≤ (164 : ℝ) := by
  have hs : √(2 / (12986 : ℝ)) ≤ (3102539413 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12986 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12986 : ℝ) = 12986 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12986 : ℝ) + √12986 + gaussMomConst 80 ≤ 13109 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12986 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12986 : ℝ)) ≤ (108902939 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12986 4 +
      2 / (mA 12986 : ℝ) * frobEnvelopeSquared160 12986 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12986 4 +
      2 / (mA 12986 : ℝ) * frobEnvelopeSquared160 12986) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12986 : ℝ)) *
      operatorEnvelope160 12986 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12986 4 +
      2 / (mA 12986 : ℝ) * frobEnvelopeSquared160 12986) +
      transverseConstant160 * √(2 / (mA 12986 : ℝ)) * operatorEnvelope160 12986 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12986 4 +
      2 / (mA 12986 : ℝ) * frobEnvelopeSquared160 12986) +
      transverseConstant160 * √(2 / (mA 12986 : ℝ)) * operatorEnvelope160 12986 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12986 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12986 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12986 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12986 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12986

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12986
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12986) :=
  agentEv (paperDesignP 12986) (Energy32 12986) ∩
  agentEv (paperDesignP 12986) (freshRetainedEvent160 12986 4) ∩
  agentEv (paperDesignP 12986) (FirstMatrix 12986) ∩
  BstLean.Part164.Eop2 12986 ∩ outputCentreEvent (paperCentres 12986)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12986)).real
      (agentEv (paperDesignP 12986) (FirstMatrix 12986))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12986)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12986 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12986)).real (BstLean.Part164.Eop2 12986)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12986)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12986)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12986) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12986) hτ
  have hL := fresh_retained_charge160 (n := 12986) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12986) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12986 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12986) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12986 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12986) (hw : WINDOW (paperDesignP 12986) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12986))
    (hW : ∫ a in K, ((12986 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12986 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12986 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12986 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12986) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12986 : ℝ)) * eR c * 12986 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12986

/-! Exact rational parameters for the dimension-12987 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12987
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
noncomputable def biasRootCap : ℝ := (578751 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12987 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12987 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12987 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12987.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12987] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12987 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12987 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12987.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12987

namespace BstLean.Part266.Row12987
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

theorem energy_allowance_row : energyAllowance 12987 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12987 : ℝ)) ≤ ((54447277 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12987 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12987)
  change 0 ≤ agentLayerAllowance 12987 at ha0
  have he : energyWeightAllowance 12987 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12987)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12987)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12987).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12987).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12987)) :
    ∫ a in K, fbR c a ^ k ∂muI 12987 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12987])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12987

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12987
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12987 / 12987 ≤ chi := by
  have hs : √((12987 : ℝ) * 12) ≤ (19738541 / 50000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12987}
    (hc : c ∈ outputCentreEvent (paperCentres 12987)) :
    normSq c.2.1.2 ≤ (2 / (12987 : ℝ)) * eR c * 12987 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12987 : ℝ) * normSq (bR c) * chiUp 12987 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12987)).real (outputCentreEvent (paperCentres 12987))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12987

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12987
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12987) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 164) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12987) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12987)]
  norm_num [varianceMax]

end BstLean.Part266.Row12987

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12987
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12987) (hc : A1 c ∈ Eop 12987) : OpB (A1 c) 164 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12987 : ℝ)) ≤ (12409679851 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12987 : ℝ) ≤ (2849013 / 25000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12987 : ℝ) + 2 * √12987 ≤ (165186513 / 12500) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12987) (hc : c ∈ BstLean.Part164.Eop2 12987) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12987 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12987) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12987 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12987) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12987).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12987) (FirstMatrix 12987))
    (h2 : c ∈ BstLean.Part164.Eop2 12987) (a : BstLean.Part161.Ix 12987) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12987

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12987
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12987) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12987) c ∈ BstLean.Part212.latitudeEvent 12987
      (ENNReal.ofReal (C / 12987))) (K : Set (Ix 12987)) :
    ∫ a in K, ((12987 : ℝ) * VR c a) ^ 2 ∂muI 12987 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12987

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12987
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12987 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12987 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12987 - 1 - 1) 80 ≤ (13143 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12987 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13143 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12987) ≤ (78 * 10 ^ 6 * ((12987 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12987 : ℝ) / 2 + 160) ≤ (9183204479 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12987 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12987 : ℝ) ^ 2 / 2 + 320 = 168662809 / 2 by norm_num,
    show (12987 : ℝ) ^ 2 / 2 + 160 = 168662489 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12987 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12987 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12987 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12987 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12987)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12987) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12987 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12987)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12987 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12987 ≤ (164 : ℝ) := by
  have hs : √(2 / (12987 : ℝ)) ≤ (12409679851 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12987 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12987 : ℝ) = 12987 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12987 : ℝ) + √12987 + gaussMomConst 80 ≤ 13110 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12987 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12987 : ℝ)) ≤ (54447277 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12987 4 +
      2 / (mA 12987 : ℝ) * frobEnvelopeSquared160 12987 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12987 4 +
      2 / (mA 12987 : ℝ) * frobEnvelopeSquared160 12987) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12987 : ℝ)) *
      operatorEnvelope160 12987 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12987 4 +
      2 / (mA 12987 : ℝ) * frobEnvelopeSquared160 12987) +
      transverseConstant160 * √(2 / (mA 12987 : ℝ)) * operatorEnvelope160 12987 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12987 4 +
      2 / (mA 12987 : ℝ) * frobEnvelopeSquared160 12987) +
      transverseConstant160 * √(2 / (mA 12987 : ℝ)) * operatorEnvelope160 12987 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12987 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12987 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12987 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12987 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12987

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12987
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12987) :=
  agentEv (paperDesignP 12987) (Energy32 12987) ∩
  agentEv (paperDesignP 12987) (freshRetainedEvent160 12987 4) ∩
  agentEv (paperDesignP 12987) (FirstMatrix 12987) ∩
  BstLean.Part164.Eop2 12987 ∩ outputCentreEvent (paperCentres 12987)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12987)).real
      (agentEv (paperDesignP 12987) (FirstMatrix 12987))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12987)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12987 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12987)).real (BstLean.Part164.Eop2 12987)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12987)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12987)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12987) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12987) hτ
  have hL := fresh_retained_charge160 (n := 12987) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12987) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12987 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12987) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12987 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12987) (hw : WINDOW (paperDesignP 12987) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12987))
    (hW : ∫ a in K, ((12987 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12987 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12987 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12987 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12987) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12987 : ℝ)) * eR c * 12987 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12987

/-! Exact rational parameters for the dimension-12988 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12988
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
noncomputable def biasRootCap : ℝ := (72341 / 12500000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12988 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12988 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12988 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12988.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12988] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12988 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12988 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12988.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12988

namespace BstLean.Part266.Row12988
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

theorem energy_allowance_row : energyAllowance 12988 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12988 : ℝ)) ≤ ((108886169 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12988 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12988)
  change 0 ≤ agentLayerAllowance 12988 at ha0
  have he : energyWeightAllowance 12988 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12988)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12988)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12988).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12988).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12988)) :
    ∫ a in K, fbR c a ^ k ∂muI 12988 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12988])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12988

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12988
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12988 / 12988 ≤ chi := by
  have hs : √((12988 : ℝ) * 12) ≤ (197393009 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12988}
    (hc : c ∈ outputCentreEvent (paperCentres 12988)) :
    normSq c.2.1.2 ≤ (2 / (12988 : ℝ)) * eR c * 12988 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12988 : ℝ) * normSq (bR c) * chiUp 12988 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12988)).real (outputCentreEvent (paperCentres 12988))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12988

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12988
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12988) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 164) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12988) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12988)]
  norm_num [varianceMax]

end BstLean.Part266.Row12988

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12988
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12988) (hc : A1 c ∈ Eop 12988) : OpB (A1 c) 164 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12988 : ℝ)) ≤ (6204601053 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12988 : ℝ) ≤ (113964907 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12988 : ℝ) + 2 * √12988 ≤ (6607964907 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12988) (hc : c ∈ BstLean.Part164.Eop2 12988) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12988 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12988) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12988 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12988) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12988).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12988) (FirstMatrix 12988))
    (h2 : c ∈ BstLean.Part164.Eop2 12988) (a : BstLean.Part161.Ix 12988) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12988

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12988
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12988) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12988) c ∈ BstLean.Part212.latitudeEvent 12988
      (ENNReal.ofReal (C / 12988))) (K : Set (Ix 12988)) :
    ∫ a in K, ((12988 : ℝ) * VR c a) ^ 2 ∂muI 12988 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12988

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12988
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12988 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12988 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12988 - 1 - 1) 80 ≤ (13144 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12988 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13144 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12988) ≤ (78 * 10 ^ 6 * ((12988 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12988 : ℝ) / 2 + 160) ≤ (1836782317 / 200000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12988 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12988 : ℝ) ^ 2 / 2 + 320 = 168688784 / 2 by norm_num,
    show (12988 : ℝ) ^ 2 / 2 + 160 = 168688464 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12988 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12988 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12988 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12988 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12988)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12988) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12988 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12988)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12988 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12988 ≤ (164 : ℝ) := by
  have hs : √(2 / (12988 : ℝ)) ≤ (6204601053 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12988 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12988 : ℝ) = 12988 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12988 : ℝ) + √12988 + gaussMomConst 80 ≤ 13111 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12988 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12988 : ℝ)) ≤ (108886169 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12988 4 +
      2 / (mA 12988 : ℝ) * frobEnvelopeSquared160 12988 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12988 4 +
      2 / (mA 12988 : ℝ) * frobEnvelopeSquared160 12988) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12988 : ℝ)) *
      operatorEnvelope160 12988 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12988 4 +
      2 / (mA 12988 : ℝ) * frobEnvelopeSquared160 12988) +
      transverseConstant160 * √(2 / (mA 12988 : ℝ)) * operatorEnvelope160 12988 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12988 4 +
      2 / (mA 12988 : ℝ) * frobEnvelopeSquared160 12988) +
      transverseConstant160 * √(2 / (mA 12988 : ℝ)) * operatorEnvelope160 12988 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12988 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12988 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12988 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12988 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12988

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12988
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12988) :=
  agentEv (paperDesignP 12988) (Energy32 12988) ∩
  agentEv (paperDesignP 12988) (freshRetainedEvent160 12988 4) ∩
  agentEv (paperDesignP 12988) (FirstMatrix 12988) ∩
  BstLean.Part164.Eop2 12988 ∩ outputCentreEvent (paperCentres 12988)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12988)).real
      (agentEv (paperDesignP 12988) (FirstMatrix 12988))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12988)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12988 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12988)).real (BstLean.Part164.Eop2 12988)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12988)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12988)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12988) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12988) hτ
  have hL := fresh_retained_charge160 (n := 12988) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12988) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12988 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12988) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12988 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12988) (hw : WINDOW (paperDesignP 12988) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12988))
    (hW : ∫ a in K, ((12988 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12988 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12988 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12988 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12988) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12988 : ℝ)) * eR c * 12988 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12988

/-! Exact rational parameters for the dimension-12989 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12989
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
noncomputable def biasRootCap : ℝ := (289353 / 50000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12989 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12989 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12989 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12989.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12989] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12989 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12989 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12989.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12989

namespace BstLean.Part266.Row12989
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

theorem energy_allowance_row : energyAllowance 12989 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12989 : ℝ)) ≤ ((108877787 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12989 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12989)
  change 0 ≤ agentLayerAllowance 12989 at ha0
  have he : energyWeightAllowance 12989 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12989)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12989)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12989).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12989).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12989)) :
    ∫ a in K, fbR c a ^ k ∂muI 12989 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12989])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12989

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12989
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12989 / 12989 ≤ chi := by
  have hs : √((12989 : ℝ) * 12) ≤ (6168769 / 15625) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12989}
    (hc : c ∈ outputCentreEvent (paperCentres 12989)) :
    normSq c.2.1.2 ≤ (2 / (12989 : ℝ)) * eR c * 12989 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12989 : ℝ) * normSq (bR c) * chiUp 12989 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12989)).real (outputCentreEvent (paperCentres 12989))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12989

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12989
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12989) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 165) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12989) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12989)]
  norm_num [varianceMax]

end BstLean.Part266.Row12989

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12989
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12989) (hc : A1 c ∈ Eop 12989) : OpB (A1 c) 165 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12989 : ℝ)) ≤ (2481744883 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12989 : ℝ) ≤ (22793859 / 200000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12989 : ℝ) + 2 * √12989 ≤ (1321693859 / 100000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12989) (hc : c ∈ BstLean.Part164.Eop2 12989) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12989 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12989) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12989 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12989) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12989).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12989) (FirstMatrix 12989))
    (h2 : c ∈ BstLean.Part164.Eop2 12989) (a : BstLean.Part161.Ix 12989) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12989

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12989
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12989) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12989) c ∈ BstLean.Part212.latitudeEvent 12989
      (ENNReal.ofReal (C / 12989))) (K : Set (Ix 12989)) :
    ∫ a in K, ((12989 : ℝ) * VR c a) ^ 2 ∂muI 12989 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12989

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12989
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12989 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12989 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12989 - 1 - 1) 80 ≤ (13145 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12989 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13145 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12989) ≤ (78 * 10 ^ 6 * ((12989 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12989 : ℝ) / 2 + 160) ≤ (2296154673 / 250000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12989 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12989 : ℝ) ^ 2 / 2 + 320 = 168714761 / 2 by norm_num,
    show (12989 : ℝ) ^ 2 / 2 + 160 = 168714441 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12989 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12989 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12989 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12989 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12989)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12989) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12989 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12989)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12989 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12989 ≤ (165 : ℝ) := by
  have hs : √(2 / (12989 : ℝ)) ≤ (2481744883 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12989 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12989 : ℝ) = 12989 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12989 : ℝ) + √12989 + gaussMomConst 80 ≤ 13112 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12989 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12989 : ℝ)) ≤ (108877787 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12989 4 +
      2 / (mA 12989 : ℝ) * frobEnvelopeSquared160 12989 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12989 4 +
      2 / (mA 12989 : ℝ) * frobEnvelopeSquared160 12989) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12989 : ℝ)) *
      operatorEnvelope160 12989 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12989 4 +
      2 / (mA 12989 : ℝ) * frobEnvelopeSquared160 12989) +
      transverseConstant160 * √(2 / (mA 12989 : ℝ)) * operatorEnvelope160 12989 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12989 4 +
      2 / (mA 12989 : ℝ) * frobEnvelopeSquared160 12989) +
      transverseConstant160 * √(2 / (mA 12989 : ℝ)) * operatorEnvelope160 12989 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12989 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12989 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12989 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12989 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12989

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12989
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12989) :=
  agentEv (paperDesignP 12989) (Energy32 12989) ∩
  agentEv (paperDesignP 12989) (freshRetainedEvent160 12989 4) ∩
  agentEv (paperDesignP 12989) (FirstMatrix 12989) ∩
  BstLean.Part164.Eop2 12989 ∩ outputCentreEvent (paperCentres 12989)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12989)).real
      (agentEv (paperDesignP 12989) (FirstMatrix 12989))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12989)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12989 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12989)).real (BstLean.Part164.Eop2 12989)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12989)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12989)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12989) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12989) hτ
  have hL := fresh_retained_charge160 (n := 12989) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12989) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12989 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12989) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12989 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12989) (hw : WINDOW (paperDesignP 12989) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12989))
    (hW : ∫ a in K, ((12989 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12989 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12989 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12989 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12989) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12989 : ℝ)) * eR c * 12989 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12989

/-! Exact rational parameters for the dimension-12990 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12990
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
noncomputable def biasRootCap : ℝ := (144671 / 25000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12990 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12990 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12990 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12990.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12990] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12990 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12990 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12990.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12990

namespace BstLean.Part266.Row12990
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

theorem energy_allowance_row : energyAllowance 12990 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12990 : ℝ)) ≤ ((21773881 / 200000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12990 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12990)
  change 0 ≤ agentLayerAllowance 12990 at ha0
  have he : energyWeightAllowance 12990 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12990)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12990)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12990).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12990).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12990)) :
    ∫ a in K, fbR c a ^ k ∂muI 12990 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12990])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12990

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12990
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12990 / 12990 ≤ chi := by
  have hs : √((12990 : ℝ) * 12) ≤ (197408207 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12990}
    (hc : c ∈ outputCentreEvent (paperCentres 12990)) :
    normSq c.2.1.2 ≤ (2 / (12990 : ℝ)) * eR c * 12990 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12990 : ℝ) * normSq (bR c) * chiUp 12990 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12990)).real (outputCentreEvent (paperCentres 12990))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12990

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12990
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12990) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 165) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12990) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12990)]
  norm_num [varianceMax]

end BstLean.Part266.Row12990

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12990
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12990) (hc : A1 c ∈ Eop 12990) : OpB (A1 c) 165 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12990 : ℝ)) ≤ (620412339 / 50000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12990 : ℝ) ≤ (56986841 / 500000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12990 : ℝ) + 2 * √12990 ≤ (3304486841 / 250000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12990) (hc : c ∈ BstLean.Part164.Eop2 12990) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12990 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12990) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12990 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12990) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12990).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12990) (FirstMatrix 12990))
    (h2 : c ∈ BstLean.Part164.Eop2 12990) (a : BstLean.Part161.Ix 12990) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12990

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12990
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12990) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12990) c ∈ BstLean.Part212.latitudeEvent 12990
      (ENNReal.ofReal (C / 12990))) (K : Set (Ix 12990)) :
    ∫ a in K, ((12990 : ℝ) * VR c a) ^ 2 ∂muI 12990 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12990

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12990
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12990 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12990 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12990 - 1 - 1) 80 ≤ (13146 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12990 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13146 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12990) ≤ (78 * 10 ^ 6 * ((12990 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12990 : ℝ) / 2 + 160) ≤ (4592662899 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12990 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12990 : ℝ) ^ 2 / 2 + 320 = 168740740 / 2 by norm_num,
    show (12990 : ℝ) ^ 2 / 2 + 160 = 168740420 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12990 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12990 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12990 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12990 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12990)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12990) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12990 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12990)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12990 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12990 ≤ (165 : ℝ) := by
  have hs : √(2 / (12990 : ℝ)) ≤ (620412339 / 50000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12990 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12990 : ℝ) = 12990 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12990 : ℝ) + √12990 + gaussMomConst 80 ≤ 13113 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12990 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12990 : ℝ)) ≤ (21773881 / 200000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12990 4 +
      2 / (mA 12990 : ℝ) * frobEnvelopeSquared160 12990 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12990 4 +
      2 / (mA 12990 : ℝ) * frobEnvelopeSquared160 12990) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12990 : ℝ)) *
      operatorEnvelope160 12990 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12990 4 +
      2 / (mA 12990 : ℝ) * frobEnvelopeSquared160 12990) +
      transverseConstant160 * √(2 / (mA 12990 : ℝ)) * operatorEnvelope160 12990 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12990 4 +
      2 / (mA 12990 : ℝ) * frobEnvelopeSquared160 12990) +
      transverseConstant160 * √(2 / (mA 12990 : ℝ)) * operatorEnvelope160 12990 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12990 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12990 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12990 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12990 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12990

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12990
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12990) :=
  agentEv (paperDesignP 12990) (Energy32 12990) ∩
  agentEv (paperDesignP 12990) (freshRetainedEvent160 12990 4) ∩
  agentEv (paperDesignP 12990) (FirstMatrix 12990) ∩
  BstLean.Part164.Eop2 12990 ∩ outputCentreEvent (paperCentres 12990)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12990)).real
      (agentEv (paperDesignP 12990) (FirstMatrix 12990))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12990)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12990 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12990)).real (BstLean.Part164.Eop2 12990)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12990)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12990)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12990) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12990) hτ
  have hL := fresh_retained_charge160 (n := 12990) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12990) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12990 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12990) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12990 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12990) (hw : WINDOW (paperDesignP 12990) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12990))
    (hW : ∫ a in K, ((12990 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12990 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12990 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12990 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12990) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12990 : ℝ)) * eR c * 12990 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12990

/-! Exact rational parameters for the dimension-12991 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12991
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
noncomputable def biasRootCap : ℝ := (289331 / 50000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12991 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12991 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12991 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12991.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12991] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12991 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12991 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12991.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12991

namespace BstLean.Part266.Row12991
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

theorem energy_allowance_row : energyAllowance 12991 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12991 : ℝ)) ≤ ((3401907 / 31250000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12991 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12991)
  change 0 ≤ agentLayerAllowance 12991 at ha0
  have he : energyWeightAllowance 12991 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12991)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12991)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12991).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12991).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12991)) :
    ∫ a in K, fbR c a ^ k ∂muI 12991 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12991])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12991

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12991
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12991 / 12991 ≤ chi := by
  have hs : √((12991 : ℝ) * 12) ≤ (39483161 / 100000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12991}
    (hc : c ∈ outputCentreEvent (paperCentres 12991)) :
    normSq c.2.1.2 ≤ (2 / (12991 : ℝ)) * eR c * 12991 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12991 : ℝ) * normSq (bR c) * chiUp 12991 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12991)).real (outputCentreEvent (paperCentres 12991))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12991

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12991
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12991) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 165) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12991) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12991)]
  norm_num [varianceMax]

end BstLean.Part266.Row12991

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12991
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12991) (hc : A1 c ∈ Eop 12991) : OpB (A1 c) 165 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12991 : ℝ)) ≤ (31019423 / 2500000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12991 : ℝ) ≤ (113978069 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12991 : ℝ) + 2 * √12991 ≤ (6609478069 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12991) (hc : c ∈ BstLean.Part164.Eop2 12991) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12991 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12991) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12991 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12991) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12991).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12991) (FirstMatrix 12991))
    (h2 : c ∈ BstLean.Part164.Eop2 12991) (a : BstLean.Part161.Ix 12991) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12991

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12991
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12991) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12991) c ∈ BstLean.Part212.latitudeEvent 12991
      (ENNReal.ofReal (C / 12991))) (K : Set (Ix 12991)) :
    ∫ a in K, ((12991 : ℝ) * VR c a) ^ 2 ∂muI 12991 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12991

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12991
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12991 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12991 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12991 - 1 - 1) 80 ≤ (13147 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12991 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13147 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12991) ≤ (78 * 10 ^ 6 * ((12991 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12991 : ℝ) / 2 + 160) ≤ (1148254113 / 125000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12991 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12991 : ℝ) ^ 2 / 2 + 320 = 168766721 / 2 by norm_num,
    show (12991 : ℝ) ^ 2 / 2 + 160 = 168766401 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12991 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12991 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12991 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12991 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12991)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12991) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12991 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12991)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12991 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12991 ≤ (165 : ℝ) := by
  have hs : √(2 / (12991 : ℝ)) ≤ (31019423 / 2500000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12991 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12991 : ℝ) = 12991 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12991 : ℝ) + √12991 + gaussMomConst 80 ≤ 13114 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12991 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12991 : ℝ)) ≤ (3401907 / 31250000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12991 4 +
      2 / (mA 12991 : ℝ) * frobEnvelopeSquared160 12991 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12991 4 +
      2 / (mA 12991 : ℝ) * frobEnvelopeSquared160 12991) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12991 : ℝ)) *
      operatorEnvelope160 12991 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12991 4 +
      2 / (mA 12991 : ℝ) * frobEnvelopeSquared160 12991) +
      transverseConstant160 * √(2 / (mA 12991 : ℝ)) * operatorEnvelope160 12991 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12991 4 +
      2 / (mA 12991 : ℝ) * frobEnvelopeSquared160 12991) +
      transverseConstant160 * √(2 / (mA 12991 : ℝ)) * operatorEnvelope160 12991 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12991 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12991 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12991 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12991 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12991

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12991
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12991) :=
  agentEv (paperDesignP 12991) (Energy32 12991) ∩
  agentEv (paperDesignP 12991) (freshRetainedEvent160 12991 4) ∩
  agentEv (paperDesignP 12991) (FirstMatrix 12991) ∩
  BstLean.Part164.Eop2 12991 ∩ outputCentreEvent (paperCentres 12991)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12991)).real
      (agentEv (paperDesignP 12991) (FirstMatrix 12991))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12991)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12991 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12991)).real (BstLean.Part164.Eop2 12991)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12991)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12991)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12991) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12991) hτ
  have hL := fresh_retained_charge160 (n := 12991) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12991) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12991 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12991) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12991 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12991) (hw : WINDOW (paperDesignP 12991) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12991))
    (hW : ∫ a in K, ((12991 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12991 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12991 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12991 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12991) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12991 : ℝ)) * eR c * 12991 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12991

/-! Exact rational parameters for the dimension-12992 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12992
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
noncomputable def biasRootCap : ℝ := (578639 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12992 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12992 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12992 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12992.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12992] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12992 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12992 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12992.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12992

namespace BstLean.Part266.Row12992
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

theorem energy_allowance_row : energyAllowance 12992 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12992 : ℝ)) ≤ ((21770529 / 200000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12992 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12992)
  change 0 ≤ agentLayerAllowance 12992 at ha0
  have he : energyWeightAllowance 12992 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12992)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12992)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12992).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12992).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12992)) :
    ∫ a in K, fbR c a ^ k ∂muI 12992 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12992])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12992

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12992
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12992 / 12992 ≤ chi := by
  have hs : √((12992 : ℝ) * 12) ≤ (197423403 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12992}
    (hc : c ∈ outputCentreEvent (paperCentres 12992)) :
    normSq c.2.1.2 ≤ (2 / (12992 : ℝ)) * eR c * 12992 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12992 : ℝ) * normSq (bR c) * chiUp 12992 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12992)).real (outputCentreEvent (paperCentres 12992))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12992

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12992
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12992) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 165) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12992) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12992)]
  norm_num [varianceMax]

end BstLean.Part266.Row12992

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12992
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12992) (hc : A1 c ∈ Eop 12992) : OpB (A1 c) 165 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12992 : ℝ)) ≤ (496291667 / 40000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12992 : ℝ) ≤ (22796491 / 200000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12992 : ℝ) + 2 * √12992 ≤ (1321996491 / 100000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12992) (hc : c ∈ BstLean.Part164.Eop2 12992) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12992 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12992) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12992 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12992) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12992).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12992) (FirstMatrix 12992))
    (h2 : c ∈ BstLean.Part164.Eop2 12992) (a : BstLean.Part161.Ix 12992) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12992

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12992
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12992) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12992) c ∈ BstLean.Part212.latitudeEvent 12992
      (ENNReal.ofReal (C / 12992))) (K : Set (Ix 12992)) :
    ∫ a in K, ((12992 : ℝ) * VR c a) ^ 2 ∂muI 12992 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12992

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12992
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12992 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12992 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12992 - 1 - 1) 80 ≤ (13148 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12992 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13148 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12992) ≤ (78 * 10 ^ 6 * ((12992 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12992 : ℝ) / 2 + 160) ≤ (918674001 / 100000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12992 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12992 : ℝ) ^ 2 / 2 + 320 = 168792704 / 2 by norm_num,
    show (12992 : ℝ) ^ 2 / 2 + 160 = 168792384 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12992 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12992 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12992 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12992 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12992)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12992) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12992 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12992)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12992 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12992 ≤ (165 : ℝ) := by
  have hs : √(2 / (12992 : ℝ)) ≤ (496291667 / 40000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12992 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12992 : ℝ) = 12992 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12992 : ℝ) + √12992 + gaussMomConst 80 ≤ 13115 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12992 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12992 : ℝ)) ≤ (21770529 / 200000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12992 4 +
      2 / (mA 12992 : ℝ) * frobEnvelopeSquared160 12992 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12992 4 +
      2 / (mA 12992 : ℝ) * frobEnvelopeSquared160 12992) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12992 : ℝ)) *
      operatorEnvelope160 12992 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12992 4 +
      2 / (mA 12992 : ℝ) * frobEnvelopeSquared160 12992) +
      transverseConstant160 * √(2 / (mA 12992 : ℝ)) * operatorEnvelope160 12992 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12992 4 +
      2 / (mA 12992 : ℝ) * frobEnvelopeSquared160 12992) +
      transverseConstant160 * √(2 / (mA 12992 : ℝ)) * operatorEnvelope160 12992 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12992 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12992 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12992 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12992 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12992

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12992
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12992) :=
  agentEv (paperDesignP 12992) (Energy32 12992) ∩
  agentEv (paperDesignP 12992) (freshRetainedEvent160 12992 4) ∩
  agentEv (paperDesignP 12992) (FirstMatrix 12992) ∩
  BstLean.Part164.Eop2 12992 ∩ outputCentreEvent (paperCentres 12992)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12992)).real
      (agentEv (paperDesignP 12992) (FirstMatrix 12992))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12992)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12992 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12992)).real (BstLean.Part164.Eop2 12992)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12992)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12992)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12992) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12992) hτ
  have hL := fresh_retained_charge160 (n := 12992) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12992) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12992 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12992) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12992 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12992) (hw : WINDOW (paperDesignP 12992) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12992))
    (hW : ∫ a in K, ((12992 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12992 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12992 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12992 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12992) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12992 : ℝ)) * eR c * 12992 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12992

/-! Exact rational parameters for the dimension-12993 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12993
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
noncomputable def biasRootCap : ℝ := (578617 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12993 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12993 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12993 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12993.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12993] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12993 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12993 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12993.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12993

namespace BstLean.Part266.Row12993
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

theorem energy_allowance_row : energyAllowance 12993 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12993 : ℝ)) ≤ ((27211067 / 250000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12993 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12993)
  change 0 ≤ agentLayerAllowance 12993 at ha0
  have he : energyWeightAllowance 12993 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12993)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12993)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12993).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12993).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12993)) :
    ∫ a in K, fbR c a ^ k ∂muI 12993 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12993])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12993

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12993
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12993 / 12993 ≤ chi := by
  have hs : √((12993 : ℝ) * 12) ≤ (197431001 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12993}
    (hc : c ∈ outputCentreEvent (paperCentres 12993)) :
    normSq c.2.1.2 ≤ (2 / (12993 : ℝ)) * eR c * 12993 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12993 : ℝ) * normSq (bR c) * chiUp 12993 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12993)).real (outputCentreEvent (paperCentres 12993))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12993

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12993
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12993) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 165) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12993) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12993)]
  norm_num [varianceMax]

end BstLean.Part266.Row12993

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12993
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12993) (hc : A1 c ∈ Eop 12993) : OpB (A1 c) 165 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12993 : ℝ)) ≤ (2481362841 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12993 : ℝ) ≤ (56993421 / 500000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12993 : ℝ) + 2 * √12993 ≤ (3305243421 / 250000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12993) (hc : c ∈ BstLean.Part164.Eop2 12993) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12993 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12993) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12993 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12993) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12993).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12993) (FirstMatrix 12993))
    (h2 : c ∈ BstLean.Part164.Eop2 12993) (a : BstLean.Part161.Ix 12993) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12993

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12993
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12993) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12993) c ∈ BstLean.Part212.latitudeEvent 12993
      (ENNReal.ofReal (C / 12993))) (K : Set (Ix 12993)) :
    ∫ a in K, ((12993 : ℝ) * VR c a) ^ 2 ∂muI 12993 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12993

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12993
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12993 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12993 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12993 - 1 - 1) 80 ≤ (13149 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12993 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13149 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12993) ≤ (78 * 10 ^ 6 * ((12993 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12993 : ℝ) / 2 + 160) ≤ (2296861779 / 250000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12993 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12993 : ℝ) ^ 2 / 2 + 320 = 168818689 / 2 by norm_num,
    show (12993 : ℝ) ^ 2 / 2 + 160 = 168818369 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12993 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12993 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12993 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12993 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12993)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12993) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12993 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12993)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12993 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12993 ≤ (165 : ℝ) := by
  have hs : √(2 / (12993 : ℝ)) ≤ (2481362841 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12993 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12993 : ℝ) = 12993 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12993 : ℝ) + √12993 + gaussMomConst 80 ≤ 13116 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12993 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12993 : ℝ)) ≤ (27211067 / 250000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12993 4 +
      2 / (mA 12993 : ℝ) * frobEnvelopeSquared160 12993 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12993 4 +
      2 / (mA 12993 : ℝ) * frobEnvelopeSquared160 12993) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12993 : ℝ)) *
      operatorEnvelope160 12993 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12993 4 +
      2 / (mA 12993 : ℝ) * frobEnvelopeSquared160 12993) +
      transverseConstant160 * √(2 / (mA 12993 : ℝ)) * operatorEnvelope160 12993 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12993 4 +
      2 / (mA 12993 : ℝ) * frobEnvelopeSquared160 12993) +
      transverseConstant160 * √(2 / (mA 12993 : ℝ)) * operatorEnvelope160 12993 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12993 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12993 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12993 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12993 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12993

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12993
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12993) :=
  agentEv (paperDesignP 12993) (Energy32 12993) ∩
  agentEv (paperDesignP 12993) (freshRetainedEvent160 12993 4) ∩
  agentEv (paperDesignP 12993) (FirstMatrix 12993) ∩
  BstLean.Part164.Eop2 12993 ∩ outputCentreEvent (paperCentres 12993)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12993)).real
      (agentEv (paperDesignP 12993) (FirstMatrix 12993))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12993)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12993 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12993)).real (BstLean.Part164.Eop2 12993)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12993)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12993)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12993) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12993) hτ
  have hL := fresh_retained_charge160 (n := 12993) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12993) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12993 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12993) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12993 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12993) (hw : WINDOW (paperDesignP 12993) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12993))
    (hW : ∫ a in K, ((12993 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12993 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12993 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12993 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12993) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12993 : ℝ)) * eR c * 12993 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12993

/-! Exact rational parameters for the dimension-12994 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12994
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
noncomputable def biasRootCap : ℝ := (115719 / 20000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12994 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12994 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12994 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12994.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12994] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12994 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12994 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12994.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12994

namespace BstLean.Part266.Row12994
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

theorem energy_allowance_row : energyAllowance 12994 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12994 : ℝ)) ≤ ((108835891 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12994 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12994)
  change 0 ≤ agentLayerAllowance 12994 at ha0
  have he : energyWeightAllowance 12994 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12994)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12994)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12994).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12994).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12994)) :
    ∫ a in K, fbR c a ^ k ∂muI 12994 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12994])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12994

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12994
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12994 / 12994 ≤ chi := by
  have hs : √((12994 : ℝ) * 12) ≤ (394877197 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12994}
    (hc : c ∈ outputCentreEvent (paperCentres 12994)) :
    normSq c.2.1.2 ≤ (2 / (12994 : ℝ)) * eR c * 12994 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12994 : ℝ) * normSq (bR c) * chiUp 12994 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12994)).real (outputCentreEvent (paperCentres 12994))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12994

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12994
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12994) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 165) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12994) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12994)]
  norm_num [varianceMax]

end BstLean.Part266.Row12994

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12994
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12994) (hc : A1 c ∈ Eop 12994) : OpB (A1 c) 165 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12994 : ℝ)) ≤ (12406336791 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12994 : ℝ) ≤ (28497807 / 250000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12994 : ℝ) + 2 * √12994 ≤ (1652747807 / 125000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12994) (hc : c ∈ BstLean.Part164.Eop2 12994) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12994 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12994) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12994 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12994) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12994).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12994) (FirstMatrix 12994))
    (h2 : c ∈ BstLean.Part164.Eop2 12994) (a : BstLean.Part161.Ix 12994) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12994

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12994
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12994) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12994) c ∈ BstLean.Part212.latitudeEvent 12994
      (ENNReal.ofReal (C / 12994))) (K : Set (Ix 12994)) :
    ∫ a in K, ((12994 : ℝ) * VR c a) ^ 2 ∂muI 12994 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12994

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12994
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12994 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12994 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12994 - 1 - 1) 80 ≤ (13150 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12994 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13150 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12994) ≤ (78 * 10 ^ 6 * ((12994 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12994 : ℝ) / 2 + 160) ≤ (4594077111 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12994 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12994 : ℝ) ^ 2 / 2 + 320 = 168844676 / 2 by norm_num,
    show (12994 : ℝ) ^ 2 / 2 + 160 = 168844356 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12994 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12994 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12994 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12994 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12994)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12994) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12994 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12994)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12994 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12994 ≤ (165 : ℝ) := by
  have hs : √(2 / (12994 : ℝ)) ≤ (12406336791 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12994 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12994 : ℝ) = 12994 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12994 : ℝ) + √12994 + gaussMomConst 80 ≤ 13117 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12994 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12994 : ℝ)) ≤ (108835891 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12994 4 +
      2 / (mA 12994 : ℝ) * frobEnvelopeSquared160 12994 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12994 4 +
      2 / (mA 12994 : ℝ) * frobEnvelopeSquared160 12994) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12994 : ℝ)) *
      operatorEnvelope160 12994 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12994 4 +
      2 / (mA 12994 : ℝ) * frobEnvelopeSquared160 12994) +
      transverseConstant160 * √(2 / (mA 12994 : ℝ)) * operatorEnvelope160 12994 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12994 4 +
      2 / (mA 12994 : ℝ) * frobEnvelopeSquared160 12994) +
      transverseConstant160 * √(2 / (mA 12994 : ℝ)) * operatorEnvelope160 12994 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12994 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12994 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12994 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12994 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12994

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12994
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12994) :=
  agentEv (paperDesignP 12994) (Energy32 12994) ∩
  agentEv (paperDesignP 12994) (freshRetainedEvent160 12994 4) ∩
  agentEv (paperDesignP 12994) (FirstMatrix 12994) ∩
  BstLean.Part164.Eop2 12994 ∩ outputCentreEvent (paperCentres 12994)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12994)).real
      (agentEv (paperDesignP 12994) (FirstMatrix 12994))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12994)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12994 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12994)).real (BstLean.Part164.Eop2 12994)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12994)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12994)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12994) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12994) hτ
  have hL := fresh_retained_charge160 (n := 12994) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12994) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12994 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12994) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12994 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12994) (hw : WINDOW (paperDesignP 12994) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12994))
    (hW : ∫ a in K, ((12994 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12994 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12994 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12994 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12994) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12994 : ℝ)) * eR c * 12994 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12994

/-! Exact rational parameters for the dimension-12995 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12995
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
noncomputable def biasRootCap : ℝ := (144643 / 25000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12995 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12995 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12995 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12995.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12995] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12995 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12995 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12995.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12995

namespace BstLean.Part266.Row12995
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

theorem energy_allowance_row : energyAllowance 12995 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12995 : ℝ)) ≤ ((27206879 / 250000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12995 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12995)
  change 0 ≤ agentLayerAllowance 12995 at ha0
  have he : energyWeightAllowance 12995 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12995)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12995)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12995).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12995).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12995)) :
    ∫ a in K, fbR c a ^ k ∂muI 12995 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12995])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12995

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12995
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12995 / 12995 ≤ chi := by
  have hs : √((12995 : ℝ) * 12) ≤ (394892391 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12995}
    (hc : c ∈ outputCentreEvent (paperCentres 12995)) :
    normSq c.2.1.2 ≤ (2 / (12995 : ℝ)) * eR c * 12995 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12995 : ℝ) * normSq (bR c) * chiUp 12995 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12995)).real (outputCentreEvent (paperCentres 12995))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12995

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12995
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12995) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 165) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12995) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12995)]
  norm_num [varianceMax]

end BstLean.Part266.Row12995

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12995
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12995) (hc : A1 c ∈ Eop 12995) : OpB (A1 c) 165 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12995 : ℝ)) ≤ (12405859431 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12995 : ℝ) ≤ (56997807 / 500000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12995 : ℝ) + 2 * √12995 ≤ (3305747807 / 250000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12995) (hc : c ∈ BstLean.Part164.Eop2 12995) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12995 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12995) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12995 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12995) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12995).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12995) (FirstMatrix 12995))
    (h2 : c ∈ BstLean.Part164.Eop2 12995) (a : BstLean.Part161.Ix 12995) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12995

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12995
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12995) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12995) c ∈ BstLean.Part212.latitudeEvent 12995
      (ENNReal.ofReal (C / 12995))) (K : Set (Ix 12995)) :
    ∫ a in K, ((12995 : ℝ) * VR c a) ^ 2 ∂muI 12995 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12995

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12995
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12995 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12995 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12995 - 1 - 1) 80 ≤ (13151 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12995 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13151 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12995) ≤ (78 * 10 ^ 6 * ((12995 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12995 : ℝ) / 2 + 160) ≤ (574303833 / 62500) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12995 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12995 : ℝ) ^ 2 / 2 + 320 = 168870665 / 2 by norm_num,
    show (12995 : ℝ) ^ 2 / 2 + 160 = 168870345 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12995 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12995 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12995 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12995 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12995)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12995) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12995 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12995)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12995 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12995 ≤ (165 : ℝ) := by
  have hs : √(2 / (12995 : ℝ)) ≤ (12405859431 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12995 : ℝ) ≤ 114 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12995 : ℝ) = 12995 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12995 : ℝ) + √12995 + gaussMomConst 80 ≤ 13118 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12995 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12995 : ℝ)) ≤ (27206879 / 250000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12995 4 +
      2 / (mA 12995 : ℝ) * frobEnvelopeSquared160 12995 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12995 4 +
      2 / (mA 12995 : ℝ) * frobEnvelopeSquared160 12995) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12995 : ℝ)) *
      operatorEnvelope160 12995 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12995 4 +
      2 / (mA 12995 : ℝ) * frobEnvelopeSquared160 12995) +
      transverseConstant160 * √(2 / (mA 12995 : ℝ)) * operatorEnvelope160 12995 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12995 4 +
      2 / (mA 12995 : ℝ) * frobEnvelopeSquared160 12995) +
      transverseConstant160 * √(2 / (mA 12995 : ℝ)) * operatorEnvelope160 12995 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12995 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12995 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12995 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12995 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12995

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12995
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12995) :=
  agentEv (paperDesignP 12995) (Energy32 12995) ∩
  agentEv (paperDesignP 12995) (freshRetainedEvent160 12995 4) ∩
  agentEv (paperDesignP 12995) (FirstMatrix 12995) ∩
  BstLean.Part164.Eop2 12995 ∩ outputCentreEvent (paperCentres 12995)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12995)).real
      (agentEv (paperDesignP 12995) (FirstMatrix 12995))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12995)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12995 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12995)).real (BstLean.Part164.Eop2 12995)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12995)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12995)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12995) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12995) hτ
  have hL := fresh_retained_charge160 (n := 12995) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12995) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12995 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12995) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12995 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12995) (hw : WINDOW (paperDesignP 12995) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12995))
    (hW : ∫ a in K, ((12995 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12995 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12995 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12995 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12995) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12995 : ℝ)) * eR c * 12995 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12995

/-! Exact rational parameters for the dimension-12996 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12996
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
noncomputable def biasRootCap : ℝ := (11571 / 2000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12996 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12996 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12996 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12996.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12996] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12996 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12996 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12996.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12996

namespace BstLean.Part266.Row12996
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

theorem energy_allowance_row : energyAllowance 12996 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12996 : ℝ)) ≤ ((54409571 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12996 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12996)
  change 0 ≤ agentLayerAllowance 12996 at ha0
  have he : energyWeightAllowance 12996 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12996)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12996)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12996).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12996).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12996)) :
    ∫ a in K, fbR c a ^ k ∂muI 12996 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12996])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12996

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12996
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12996 / 12996 ≤ chi := by
  have hs : √((12996 : ℝ) * 12) ≤ (78981517 / 200000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12996}
    (hc : c ∈ outputCentreEvent (paperCentres 12996)) :
    normSq c.2.1.2 ≤ (2 / (12996 : ℝ)) * eR c * 12996 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12996 : ℝ) * normSq (bR c) * chiUp 12996 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12996)).real (outputCentreEvent (paperCentres 12996))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12996

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12996
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12996) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 165) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12996) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  norm_num [varianceMax]

end BstLean.Part266.Row12996

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12996
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12996) (hc : A1 c ∈ Eop 12996) : OpB (A1 c) 165 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12996 : ℝ)) ≤ (12405382127 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12996 : ℝ) ≤ (114000001 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12996 : ℝ) + 2 * √12996 ≤ (6612000001 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12996) (hc : c ∈ BstLean.Part164.Eop2 12996) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12996 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12996) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12996 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12996) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12996).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12996) (FirstMatrix 12996))
    (h2 : c ∈ BstLean.Part164.Eop2 12996) (a : BstLean.Part161.Ix 12996) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12996

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12996
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12996) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12996) c ∈ BstLean.Part212.latitudeEvent 12996
      (ENNReal.ofReal (C / 12996))) (K : Set (Ix 12996)) :
    ∫ a in K, ((12996 : ℝ) * VR c a) ^ 2 ∂muI 12996 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12996

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12996
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12996 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12996 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12996 - 1 - 1) 80 ≤ (13152 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12996 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13152 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12996) ≤ (78 * 10 ^ 6 * ((12996 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12996 : ℝ) / 2 + 160) ≤ (4594784217 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12996 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12996 : ℝ) ^ 2 / 2 + 320 = 168896656 / 2 by norm_num,
    show (12996 : ℝ) ^ 2 / 2 + 160 = 168896336 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12996 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12996 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12996 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12996 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12996)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12996) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12996 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12996)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12996 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12996 ≤ (165 : ℝ) := by
  have hs : √(2 / (12996 : ℝ)) ≤ (12405382127 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12996 : ℝ) ≤ 115 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12996 : ℝ) = 12996 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12996 : ℝ) + √12996 + gaussMomConst 80 ≤ 13120 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12996 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12996 : ℝ)) ≤ (54409571 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12996 4 +
      2 / (mA 12996 : ℝ) * frobEnvelopeSquared160 12996 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12996 4 +
      2 / (mA 12996 : ℝ) * frobEnvelopeSquared160 12996) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12996 : ℝ)) *
      operatorEnvelope160 12996 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12996 4 +
      2 / (mA 12996 : ℝ) * frobEnvelopeSquared160 12996) +
      transverseConstant160 * √(2 / (mA 12996 : ℝ)) * operatorEnvelope160 12996 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12996 4 +
      2 / (mA 12996 : ℝ) * frobEnvelopeSquared160 12996) +
      transverseConstant160 * √(2 / (mA 12996 : ℝ)) * operatorEnvelope160 12996 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12996 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12996 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12996 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12996 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12996

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12996
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12996) :=
  agentEv (paperDesignP 12996) (Energy32 12996) ∩
  agentEv (paperDesignP 12996) (freshRetainedEvent160 12996 4) ∩
  agentEv (paperDesignP 12996) (FirstMatrix 12996) ∩
  BstLean.Part164.Eop2 12996 ∩ outputCentreEvent (paperCentres 12996)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12996)).real
      (agentEv (paperDesignP 12996) (FirstMatrix 12996))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12996)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12996 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12996)).real (BstLean.Part164.Eop2 12996)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12996)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12996)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12996) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12996) hτ
  have hL := fresh_retained_charge160 (n := 12996) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12996) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12996 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12996) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12996 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12996) (hw : WINDOW (paperDesignP 12996) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12996))
    (hW : ∫ a in K, ((12996 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12996 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12996 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12996 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12996) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12996 : ℝ)) * eR c * 12996 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12996

/-! Exact rational parameters for the dimension-12997 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12997
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
noncomputable def biasRootCap : ℝ := (18079 / 3125000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12997 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12997 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12997 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12997.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12997] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12997 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12997 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12997.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12997

namespace BstLean.Part266.Row12997
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

theorem energy_allowance_row : energyAllowance 12997 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12997 : ℝ)) ≤ ((108810769 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12997 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12997)
  change 0 ≤ agentLayerAllowance 12997 at ha0
  have he : energyWeightAllowance 12997 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12997)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12997)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12997).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12997).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12997)) :
    ∫ a in K, fbR c a ^ k ∂muI 12997 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12997])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12997

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12997
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12997 / 12997 ≤ chi := by
  have hs : √((12997 : ℝ) * 12) ≤ (197461389 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12997}
    (hc : c ∈ outputCentreEvent (paperCentres 12997)) :
    normSq c.2.1.2 ≤ (2 / (12997 : ℝ)) * eR c * 12997 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12997 : ℝ) * normSq (bR c) * chiUp 12997 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12997)).real (outputCentreEvent (paperCentres 12997))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12997

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12997
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12997) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 165) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12997) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12997)]
  norm_num [varianceMax]

end BstLean.Part266.Row12997

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12997
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12997) (hc : A1 c ∈ Eop 12997) : OpB (A1 c) 165 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12997 : ℝ)) ≤ (12404904877 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12997 : ℝ) ≤ (57002193 / 500000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12997 : ℝ) + 2 * √12997 ≤ (3306252193 / 250000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12997) (hc : c ∈ BstLean.Part164.Eop2 12997) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12997 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12997) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12997 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12997) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12997).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12997) (FirstMatrix 12997))
    (h2 : c ∈ BstLean.Part164.Eop2 12997) (a : BstLean.Part161.Ix 12997) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12997

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12997
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12997) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12997) c ∈ BstLean.Part212.latitudeEvent 12997
      (ENNReal.ofReal (C / 12997))) (K : Set (Ix 12997)) :
    ∫ a in K, ((12997 : ℝ) * VR c a) ^ 2 ∂muI 12997 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12997

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12997
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12997 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12997 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12997 - 1 - 1) 80 ≤ (13153 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12997 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13153 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12997) ≤ (78 * 10 ^ 6 * ((12997 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12997 : ℝ) / 2 + 160) ≤ (459513777 / 50000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12997 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12997 : ℝ) ^ 2 / 2 + 320 = 168922649 / 2 by norm_num,
    show (12997 : ℝ) ^ 2 / 2 + 160 = 168922329 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12997 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12997 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12997 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12997 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12997)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12997) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12997 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12997)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12997 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12997 ≤ (165 : ℝ) := by
  have hs : √(2 / (12997 : ℝ)) ≤ (12404904877 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12997 : ℝ) ≤ 115 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12997 : ℝ) = 12997 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12997 : ℝ) + √12997 + gaussMomConst 80 ≤ 13121 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12997 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12997 : ℝ)) ≤ (108810769 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12997 4 +
      2 / (mA 12997 : ℝ) * frobEnvelopeSquared160 12997 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12997 4 +
      2 / (mA 12997 : ℝ) * frobEnvelopeSquared160 12997) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12997 : ℝ)) *
      operatorEnvelope160 12997 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12997 4 +
      2 / (mA 12997 : ℝ) * frobEnvelopeSquared160 12997) +
      transverseConstant160 * √(2 / (mA 12997 : ℝ)) * operatorEnvelope160 12997 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12997 4 +
      2 / (mA 12997 : ℝ) * frobEnvelopeSquared160 12997) +
      transverseConstant160 * √(2 / (mA 12997 : ℝ)) * operatorEnvelope160 12997 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12997 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12997 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12997 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12997 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12997

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12997
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12997) :=
  agentEv (paperDesignP 12997) (Energy32 12997) ∩
  agentEv (paperDesignP 12997) (freshRetainedEvent160 12997 4) ∩
  agentEv (paperDesignP 12997) (FirstMatrix 12997) ∩
  BstLean.Part164.Eop2 12997 ∩ outputCentreEvent (paperCentres 12997)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12997)).real
      (agentEv (paperDesignP 12997) (FirstMatrix 12997))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12997)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12997 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12997)).real (BstLean.Part164.Eop2 12997)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12997)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12997)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12997) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12997) hτ
  have hL := fresh_retained_charge160 (n := 12997) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12997) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12997 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12997) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12997 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12997) (hw : WINDOW (paperDesignP 12997) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12997))
    (hW : ∫ a in K, ((12997 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12997 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12997 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12997 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12997) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12997 : ℝ)) * eR c * 12997 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12997

/-! Exact rational parameters for the dimension-12998 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12998
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
noncomputable def biasRootCap : ℝ := (289253 / 50000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12998 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12998 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12998 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12998.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12998] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12998 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12998 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12998.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12998

namespace BstLean.Part266.Row12998
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

theorem energy_allowance_row : energyAllowance 12998 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12998 : ℝ)) ≤ ((54401199 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12998 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12998)
  change 0 ≤ agentLayerAllowance 12998 at ha0
  have he : energyWeightAllowance 12998 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12998)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12998)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12998).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12998).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12998)) :
    ∫ a in K, fbR c a ^ k ∂muI 12998 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12998])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12998

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12998
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12998 / 12998 ≤ chi := by
  have hs : √((12998 : ℝ) * 12) ≤ (39493797 / 100000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12998}
    (hc : c ∈ outputCentreEvent (paperCentres 12998)) :
    normSq c.2.1.2 ≤ (2 / (12998 : ℝ)) * eR c * 12998 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12998 : ℝ) * normSq (bR c) * chiUp 12998 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12998)).real (outputCentreEvent (paperCentres 12998))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12998

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12998
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12998) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 165) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12998) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12998)]
  norm_num [varianceMax]

end BstLean.Part266.Row12998

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12998
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12998) (hc : A1 c ∈ Eop 12998) : OpB (A1 c) 165 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12998 : ℝ)) ≤ (12404427683 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12998 : ℝ) ≤ (28502193 / 250000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12998 : ℝ) + 2 * √12998 ≤ (1653252193 / 125000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12998) (hc : c ∈ BstLean.Part164.Eop2 12998) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12998 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12998) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12998 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12998) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12998).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12998) (FirstMatrix 12998))
    (h2 : c ∈ BstLean.Part164.Eop2 12998) (a : BstLean.Part161.Ix 12998) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12998

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12998
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12998) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12998) c ∈ BstLean.Part212.latitudeEvent 12998
      (ENNReal.ofReal (C / 12998))) (K : Set (Ix 12998)) :
    ∫ a in K, ((12998 : ℝ) * VR c a) ^ 2 ∂muI 12998 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12998

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12998
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12998 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12998 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12998 - 1 - 1) 80 ≤ (13154 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12998 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13154 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12998) ≤ (78 * 10 ^ 6 * ((12998 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12998 : ℝ) / 2 + 160) ≤ (9190982647 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12998 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12998 : ℝ) ^ 2 / 2 + 320 = 168948644 / 2 by norm_num,
    show (12998 : ℝ) ^ 2 / 2 + 160 = 168948324 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12998 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12998 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12998 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12998 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12998)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12998) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12998 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12998)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12998 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12998 ≤ (165 : ℝ) := by
  have hs : √(2 / (12998 : ℝ)) ≤ (12404427683 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12998 : ℝ) ≤ 115 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12998 : ℝ) = 12998 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12998 : ℝ) + √12998 + gaussMomConst 80 ≤ 13122 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12998 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12998 : ℝ)) ≤ (54401199 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12998 4 +
      2 / (mA 12998 : ℝ) * frobEnvelopeSquared160 12998 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12998 4 +
      2 / (mA 12998 : ℝ) * frobEnvelopeSquared160 12998) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12998 : ℝ)) *
      operatorEnvelope160 12998 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12998 4 +
      2 / (mA 12998 : ℝ) * frobEnvelopeSquared160 12998) +
      transverseConstant160 * √(2 / (mA 12998 : ℝ)) * operatorEnvelope160 12998 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12998 4 +
      2 / (mA 12998 : ℝ) * frobEnvelopeSquared160 12998) +
      transverseConstant160 * √(2 / (mA 12998 : ℝ)) * operatorEnvelope160 12998 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12998 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12998 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12998 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12998 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12998

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12998
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12998) :=
  agentEv (paperDesignP 12998) (Energy32 12998) ∩
  agentEv (paperDesignP 12998) (freshRetainedEvent160 12998 4) ∩
  agentEv (paperDesignP 12998) (FirstMatrix 12998) ∩
  BstLean.Part164.Eop2 12998 ∩ outputCentreEvent (paperCentres 12998)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12998)).real
      (agentEv (paperDesignP 12998) (FirstMatrix 12998))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12998)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12998 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12998)).real (BstLean.Part164.Eop2 12998)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12998)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12998)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12998) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12998) hτ
  have hL := fresh_retained_charge160 (n := 12998) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12998) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12998 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12998) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12998 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12998) (hw : WINDOW (paperDesignP 12998) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12998))
    (hW : ∫ a in K, ((12998 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12998 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12998 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12998 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12998) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12998 : ℝ)) * eR c * 12998 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12998

/-! Exact rational parameters for the dimension-12999 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12999
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
noncomputable def biasRootCap : ℝ := (578483 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12999 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12999 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12999 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12999.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12999] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12999 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12999 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12999.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12999

namespace BstLean.Part266.Row12999
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

theorem energy_allowance_row : energyAllowance 12999 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12999 : ℝ)) ≤ ((27198507 / 250000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12999 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12999)
  change 0 ≤ agentLayerAllowance 12999 at ha0
  have he : energyWeightAllowance 12999 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12999)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12999)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12999).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12999).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12999)) :
    ∫ a in K, fbR c a ^ k ∂muI 12999 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12999])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12999

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12999
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12999 / 12999 ≤ chi := by
  have hs : √((12999 : ℝ) * 12) ≤ (197476581 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12999}
    (hc : c ∈ outputCentreEvent (paperCentres 12999)) :
    normSq c.2.1.2 ≤ (2 / (12999 : ℝ)) * eR c * 12999 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12999 : ℝ) * normSq (bR c) * chiUp 12999 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12999)).real (outputCentreEvent (paperCentres 12999))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12999

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12999
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12999) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 165) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12999) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12999)]
  norm_num [varianceMax]

end BstLean.Part266.Row12999

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12999
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12999) (hc : A1 c ∈ Eop 12999) : OpB (A1 c) 165 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12999 : ℝ)) ≤ (775246909 / 62500000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12999 : ℝ) ≤ (57006579 / 500000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12999 : ℝ) + 2 * √12999 ≤ (3306756579 / 250000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12999) (hc : c ∈ BstLean.Part164.Eop2 12999) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12999 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12999) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12999 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12999) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12999).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12999) (FirstMatrix 12999))
    (h2 : c ∈ BstLean.Part164.Eop2 12999) (a : BstLean.Part161.Ix 12999) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12999

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12999
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12999) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12999) c ∈ BstLean.Part212.latitudeEvent 12999
      (ENNReal.ofReal (C / 12999))) (K : Set (Ix 12999)) :
    ∫ a in K, ((12999 : ℝ) * VR c a) ^ 2 ∂muI 12999 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12999

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12999
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12999 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12999 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12999 - 1 - 1) 80 ≤ (13155 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12999 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13155 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12999) ≤ (78 * 10 ^ 6 * ((12999 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12999 : ℝ) / 2 + 160) ≤ (9191689753 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12999 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12999 : ℝ) ^ 2 / 2 + 320 = 168974641 / 2 by norm_num,
    show (12999 : ℝ) ^ 2 / 2 + 160 = 168974321 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12999 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12999 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12999 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12999 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12999)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12999) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12999 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12999)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12999 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12999 ≤ (165 : ℝ) := by
  have hs : √(2 / (12999 : ℝ)) ≤ (775246909 / 62500000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12999 : ℝ) ≤ 115 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12999 : ℝ) = 12999 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12999 : ℝ) + √12999 + gaussMomConst 80 ≤ 13123 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12999 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12999 : ℝ)) ≤ (27198507 / 250000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12999 4 +
      2 / (mA 12999 : ℝ) * frobEnvelopeSquared160 12999 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12999 4 +
      2 / (mA 12999 : ℝ) * frobEnvelopeSquared160 12999) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12999 : ℝ)) *
      operatorEnvelope160 12999 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12999 4 +
      2 / (mA 12999 : ℝ) * frobEnvelopeSquared160 12999) +
      transverseConstant160 * √(2 / (mA 12999 : ℝ)) * operatorEnvelope160 12999 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12999 4 +
      2 / (mA 12999 : ℝ) * frobEnvelopeSquared160 12999) +
      transverseConstant160 * √(2 / (mA 12999 : ℝ)) * operatorEnvelope160 12999 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12999 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12999 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12999 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12999 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12999

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12999
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12999) :=
  agentEv (paperDesignP 12999) (Energy32 12999) ∩
  agentEv (paperDesignP 12999) (freshRetainedEvent160 12999 4) ∩
  agentEv (paperDesignP 12999) (FirstMatrix 12999) ∩
  BstLean.Part164.Eop2 12999 ∩ outputCentreEvent (paperCentres 12999)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12999)).real
      (agentEv (paperDesignP 12999) (FirstMatrix 12999))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12999)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12999 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12999)).real (BstLean.Part164.Eop2 12999)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12999)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12999)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12999) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12999) hτ
  have hL := fresh_retained_charge160 (n := 12999) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12999) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12999 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12999) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12999 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12999) (hw : WINDOW (paperDesignP 12999) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12999))
    (hW : ∫ a in K, ((12999 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12999 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12999 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12999 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12999) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12999 : ℝ)) * eR c * 12999 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12999
