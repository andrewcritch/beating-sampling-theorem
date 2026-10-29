import BstLean.Part252All
import BstLean.Part262ActualInterface
import BstLean.Part266Parameters


/-! Exact rational parameters for the dimension-12525 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12525
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
noncomputable def biasRootCap : ℝ := (36833 / 6250000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12525 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12525 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12525 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12525.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12525] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12525 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12525 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12525.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12525

namespace BstLean.Part266.Row12525
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

theorem energy_allowance_row : energyAllowance 12525 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12525 : ℝ)) ≤ ((112911263 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12525 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12525)
  change 0 ≤ agentLayerAllowance 12525 at ha0
  have he : energyWeightAllowance 12525 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12525)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12525)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12525).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12525).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12525)) :
    ∫ a in K, fbR c a ^ k ∂muI 12525 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12525])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12525

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12525
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12525 / 12525 ≤ chi := by
  have hs : √((12525 : ℝ) * 12) ≤ (1211517 / 3125) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12525}
    (hc : c ∈ outputCentreEvent (paperCentres 12525)) :
    normSq c.2.1.2 ≤ (2 / (12525 : ℝ)) * eR c * 12525 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12525 : ℝ) * normSq (bR c) * chiUp 12525 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12525)).real (outputCentreEvent (paperCentres 12525))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12525

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12525
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12525) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12525) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12525)]
  norm_num [varianceMax]

end BstLean.Part266.Row12525

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12525
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12525) (hc : A1 c ∈ Eop 12525) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12525 : ℝ)) ≤ (12636480473 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12525 : ℝ) ≤ (111915147 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12525 : ℝ) + 2 * √12525 ≤ (6374415147 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12525) (hc : c ∈ BstLean.Part164.Eop2 12525) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12525 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12525) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12525 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12525) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12525).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12525) (FirstMatrix 12525))
    (h2 : c ∈ BstLean.Part164.Eop2 12525) (a : BstLean.Part161.Ix 12525) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12525

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12525
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12525) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12525) c ∈ BstLean.Part212.latitudeEvent 12525
      (ENNReal.ofReal (C / 12525))) (K : Set (Ix 12525)) :
    ∫ a in K, ((12525 : ℝ) * VR c a) ^ 2 ∂muI 12525 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12525

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12525
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12525 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12525 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12525 - 1 - 1) 80 ≤ (12681 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12525 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12681 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12525) ≤ (78 * 10 ^ 6 * ((12525 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12525 : ℝ) / 2 + 160) ≤ (2214130367 / 250000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12525 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12525 : ℝ) ^ 2 / 2 + 320 = 156876265 / 2 by norm_num,
    show (12525 : ℝ) ^ 2 / 2 + 160 = 156875945 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12525 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12525 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12525 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12525 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12525)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12525) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12525 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12525)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12525 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12525 ≤ (162 : ℝ) := by
  have hs : √(2 / (12525 : ℝ)) ≤ (12636480473 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12525 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12525 : ℝ) = 12525 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12525 : ℝ) + √12525 + gaussMomConst 80 ≤ 12646 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12525 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12525 : ℝ)) ≤ (112911263 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12525 4 +
      2 / (mA 12525 : ℝ) * frobEnvelopeSquared160 12525 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12525 4 +
      2 / (mA 12525 : ℝ) * frobEnvelopeSquared160 12525) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12525 : ℝ)) *
      operatorEnvelope160 12525 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12525 4 +
      2 / (mA 12525 : ℝ) * frobEnvelopeSquared160 12525) +
      transverseConstant160 * √(2 / (mA 12525 : ℝ)) * operatorEnvelope160 12525 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12525 4 +
      2 / (mA 12525 : ℝ) * frobEnvelopeSquared160 12525) +
      transverseConstant160 * √(2 / (mA 12525 : ℝ)) * operatorEnvelope160 12525 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12525 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12525 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12525 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12525 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12525

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12525
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12525) :=
  agentEv (paperDesignP 12525) (Energy32 12525) ∩
  agentEv (paperDesignP 12525) (freshRetainedEvent160 12525 4) ∩
  agentEv (paperDesignP 12525) (FirstMatrix 12525) ∩
  BstLean.Part164.Eop2 12525 ∩ outputCentreEvent (paperCentres 12525)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12525)).real
      (agentEv (paperDesignP 12525) (FirstMatrix 12525))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12525)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12525 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12525)).real (BstLean.Part164.Eop2 12525)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12525)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12525)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12525) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12525) hτ
  have hL := fresh_retained_charge160 (n := 12525) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12525) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12525 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12525) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12525 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12525) (hw : WINDOW (paperDesignP 12525) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12525))
    (hW : ∫ a in K, ((12525 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12525 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12525 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12525 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12525) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12525 : ℝ)) * eR c * 12525 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12525

/-! Exact rational parameters for the dimension-12526 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12526
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
noncomputable def biasRootCap : ℝ := (117861 / 20000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12526 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12526 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12526 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12526.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12526] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12526 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12526 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12526.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12526

namespace BstLean.Part266.Row12526
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

theorem energy_allowance_row : energyAllowance 12526 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12526 : ℝ)) ≤ ((112902249 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12526 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12526)
  change 0 ≤ agentLayerAllowance 12526 at ha0
  have he : energyWeightAllowance 12526 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12526)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12526)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12526).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12526).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12526)) :
    ∫ a in K, fbR c a ^ k ∂muI 12526 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12526])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12526

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12526
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12526 / 12526 ≤ chi := by
  have hs : √((12526 : ℝ) * 12) ≤ (96925229 / 250000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12526}
    (hc : c ∈ outputCentreEvent (paperCentres 12526)) :
    normSq c.2.1.2 ≤ (2 / (12526 : ℝ)) * eR c * 12526 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12526 : ℝ) * normSq (bR c) * chiUp 12526 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12526)).real (outputCentreEvent (paperCentres 12526))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12526

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12526
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12526) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12526) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12526)]
  norm_num [varianceMax]

end BstLean.Part266.Row12526

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12526
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12526) (hc : A1 c ∈ Eop 12526) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12526 : ℝ)) ≤ (12635976053 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12526 : ℝ) ≤ (22383923 / 200000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12526 : ℝ) + 2 * √12526 ≤ (1274983923 / 100000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12526) (hc : c ∈ BstLean.Part164.Eop2 12526) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12526 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12526) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12526 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12526) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12526).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12526) (FirstMatrix 12526))
    (h2 : c ∈ BstLean.Part164.Eop2 12526) (a : BstLean.Part161.Ix 12526) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12526

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12526
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12526) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12526) c ∈ BstLean.Part212.latitudeEvent 12526
      (ENNReal.ofReal (C / 12526))) (K : Set (Ix 12526)) :
    ∫ a in K, ((12526 : ℝ) * VR c a) ^ 2 ∂muI 12526 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12526

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12526
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12526 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12526 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12526 - 1 - 1) 80 ≤ (12682 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12526 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12682 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12526) ≤ (78 * 10 ^ 6 * ((12526 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12526 : ℝ) / 2 + 160) ≤ (4428614287 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12526 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12526 : ℝ) ^ 2 / 2 + 320 = 156901316 / 2 by norm_num,
    show (12526 : ℝ) ^ 2 / 2 + 160 = 156900996 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12526 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12526 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12526 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12526 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12526)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12526) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12526 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12526)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12526 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12526 ≤ (162 : ℝ) := by
  have hs : √(2 / (12526 : ℝ)) ≤ (12635976053 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12526 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12526 : ℝ) = 12526 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12526 : ℝ) + √12526 + gaussMomConst 80 ≤ 12647 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12526 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12526 : ℝ)) ≤ (112902249 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12526 4 +
      2 / (mA 12526 : ℝ) * frobEnvelopeSquared160 12526 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12526 4 +
      2 / (mA 12526 : ℝ) * frobEnvelopeSquared160 12526) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12526 : ℝ)) *
      operatorEnvelope160 12526 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12526 4 +
      2 / (mA 12526 : ℝ) * frobEnvelopeSquared160 12526) +
      transverseConstant160 * √(2 / (mA 12526 : ℝ)) * operatorEnvelope160 12526 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12526 4 +
      2 / (mA 12526 : ℝ) * frobEnvelopeSquared160 12526) +
      transverseConstant160 * √(2 / (mA 12526 : ℝ)) * operatorEnvelope160 12526 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12526 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12526 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12526 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12526 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12526

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12526
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12526) :=
  agentEv (paperDesignP 12526) (Energy32 12526) ∩
  agentEv (paperDesignP 12526) (freshRetainedEvent160 12526 4) ∩
  agentEv (paperDesignP 12526) (FirstMatrix 12526) ∩
  BstLean.Part164.Eop2 12526 ∩ outputCentreEvent (paperCentres 12526)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12526)).real
      (agentEv (paperDesignP 12526) (FirstMatrix 12526))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12526)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12526 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12526)).real (BstLean.Part164.Eop2 12526)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12526)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12526)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12526) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12526) hτ
  have hL := fresh_retained_charge160 (n := 12526) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12526) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12526 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12526) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12526 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12526) (hw : WINDOW (paperDesignP 12526) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12526))
    (hW : ∫ a in K, ((12526 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12526 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12526 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12526 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12526) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12526 : ℝ)) * eR c * 12526 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12526

/-! Exact rational parameters for the dimension-12527 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12527
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
noncomputable def biasRootCap : ℝ := (589281 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12527 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12527 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12527 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12527.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12527] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12527 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12527 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12527.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12527

namespace BstLean.Part266.Row12527
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

theorem energy_allowance_row : energyAllowance 12527 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12527 : ℝ)) ≤ ((28223309 / 250000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12527 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12527)
  change 0 ≤ agentLayerAllowance 12527 at ha0
  have he : energyWeightAllowance 12527 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12527)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12527)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12527).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12527).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12527)) :
    ∫ a in K, fbR c a ^ k ∂muI 12527 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12527])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12527

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12527
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12527 / 12527 ≤ chi := by
  have hs : √((12527 : ℝ) * 12) ≤ (48464549 / 125000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12527}
    (hc : c ∈ outputCentreEvent (paperCentres 12527)) :
    normSq c.2.1.2 ≤ (2 / (12527 : ℝ)) * eR c * 12527 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12527 : ℝ) * normSq (bR c) * chiUp 12527 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12527)).real (outputCentreEvent (paperCentres 12527))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12527

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12527
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12527) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12527) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12527)]
  norm_num [varianceMax]

end BstLean.Part266.Row12527

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12527
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12527) (hc : A1 c ∈ Eop 12527) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12527 : ℝ)) ≤ (12635471693 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12527 : ℝ) ≤ (55962041 / 500000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12527 : ℝ) + 2 * √12527 ≤ (3187712041 / 250000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12527) (hc : c ∈ BstLean.Part164.Eop2 12527) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12527 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12527) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12527 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12527) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12527).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12527) (FirstMatrix 12527))
    (h2 : c ∈ BstLean.Part164.Eop2 12527) (a : BstLean.Part161.Ix 12527) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12527

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12527
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12527) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12527) c ∈ BstLean.Part212.latitudeEvent 12527
      (ENNReal.ofReal (C / 12527))) (K : Set (Ix 12527)) :
    ∫ a in K, ((12527 : ℝ) * VR c a) ^ 2 ∂muI 12527 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12527

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12527
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12527 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12527 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12527 - 1 - 1) 80 ≤ (12683 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12527 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12683 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12527) ≤ (78 * 10 ^ 6 * ((12527 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12527 : ℝ) / 2 + 160) ≤ (27681049 / 3125) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12527 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12527 : ℝ) ^ 2 / 2 + 320 = 156926369 / 2 by norm_num,
    show (12527 : ℝ) ^ 2 / 2 + 160 = 156926049 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12527 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12527 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12527 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12527 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12527)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12527) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12527 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12527)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12527 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12527 ≤ (162 : ℝ) := by
  have hs : √(2 / (12527 : ℝ)) ≤ (12635471693 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12527 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12527 : ℝ) = 12527 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12527 : ℝ) + √12527 + gaussMomConst 80 ≤ 12648 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12527 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12527 : ℝ)) ≤ (28223309 / 250000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12527 4 +
      2 / (mA 12527 : ℝ) * frobEnvelopeSquared160 12527 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12527 4 +
      2 / (mA 12527 : ℝ) * frobEnvelopeSquared160 12527) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12527 : ℝ)) *
      operatorEnvelope160 12527 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12527 4 +
      2 / (mA 12527 : ℝ) * frobEnvelopeSquared160 12527) +
      transverseConstant160 * √(2 / (mA 12527 : ℝ)) * operatorEnvelope160 12527 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12527 4 +
      2 / (mA 12527 : ℝ) * frobEnvelopeSquared160 12527) +
      transverseConstant160 * √(2 / (mA 12527 : ℝ)) * operatorEnvelope160 12527 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12527 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12527 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12527 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12527 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12527

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12527
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12527) :=
  agentEv (paperDesignP 12527) (Energy32 12527) ∩
  agentEv (paperDesignP 12527) (freshRetainedEvent160 12527 4) ∩
  agentEv (paperDesignP 12527) (FirstMatrix 12527) ∩
  BstLean.Part164.Eop2 12527 ∩ outputCentreEvent (paperCentres 12527)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12527)).real
      (agentEv (paperDesignP 12527) (FirstMatrix 12527))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12527)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12527 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12527)).real (BstLean.Part164.Eop2 12527)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12527)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12527)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12527) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12527) hτ
  have hL := fresh_retained_charge160 (n := 12527) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12527) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12527 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12527) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12527 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12527) (hw : WINDOW (paperDesignP 12527) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12527))
    (hW : ∫ a in K, ((12527 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12527 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12527 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12527 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12527) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12527 : ℝ)) * eR c * 12527 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12527

/-! Exact rational parameters for the dimension-12528 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12528
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
noncomputable def biasRootCap : ℝ := (294629 / 50000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12528 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12528 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12528 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12528.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12528] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12528 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12528 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12528.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12528

namespace BstLean.Part266.Row12528
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

theorem energy_allowance_row : energyAllowance 12528 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12528 : ℝ)) ≤ ((4515369 / 40000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12528 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12528)
  change 0 ≤ agentLayerAllowance 12528 at ha0
  have he : energyWeightAllowance 12528 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12528)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12528)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12528).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12528).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12528)) :
    ∫ a in K, fbR c a ^ k ∂muI 12528 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12528])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12528

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12528
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12528 / 12528 ≤ chi := by
  have hs : √((12528 : ℝ) * 12) ≤ (387731867 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12528}
    (hc : c ∈ outputCentreEvent (paperCentres 12528)) :
    normSq c.2.1.2 ≤ (2 / (12528 : ℝ)) * eR c * 12528 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12528 : ℝ) * normSq (bR c) * chiUp 12528 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12528)).real (outputCentreEvent (paperCentres 12528))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12528

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12528
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12528) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12528) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12528)]
  norm_num [varianceMax]

end BstLean.Part266.Row12528

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12528
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12528) (hc : A1 c ∈ Eop 12528) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12528 : ℝ)) ≤ (12634967393 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12528 : ℝ) ≤ (111928549 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12528 : ℝ) + 2 * √12528 ≤ (6375928549 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12528) (hc : c ∈ BstLean.Part164.Eop2 12528) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12528 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12528) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12528 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12528) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12528).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12528) (FirstMatrix 12528))
    (h2 : c ∈ BstLean.Part164.Eop2 12528) (a : BstLean.Part161.Ix 12528) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12528

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12528
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12528) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12528) c ∈ BstLean.Part212.latitudeEvent 12528
      (ENNReal.ofReal (C / 12528))) (K : Set (Ix 12528)) :
    ∫ a in K, ((12528 : ℝ) * VR c a) ^ 2 ∂muI 12528 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12528

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12528
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12528 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12528 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12528 - 1 - 1) 80 ≤ (12684 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12528 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12684 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12528) ≤ (78 * 10 ^ 6 * ((12528 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12528 : ℝ) / 2 + 160) ≤ (4429321393 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12528 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12528 : ℝ) ^ 2 / 2 + 320 = 156951424 / 2 by norm_num,
    show (12528 : ℝ) ^ 2 / 2 + 160 = 156951104 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12528 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12528 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12528 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12528 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12528)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12528) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12528 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12528)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12528 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12528 ≤ (162 : ℝ) := by
  have hs : √(2 / (12528 : ℝ)) ≤ (12634967393 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12528 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12528 : ℝ) = 12528 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12528 : ℝ) + √12528 + gaussMomConst 80 ≤ 12649 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12528 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12528 : ℝ)) ≤ (4515369 / 40000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12528 4 +
      2 / (mA 12528 : ℝ) * frobEnvelopeSquared160 12528 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12528 4 +
      2 / (mA 12528 : ℝ) * frobEnvelopeSquared160 12528) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12528 : ℝ)) *
      operatorEnvelope160 12528 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12528 4 +
      2 / (mA 12528 : ℝ) * frobEnvelopeSquared160 12528) +
      transverseConstant160 * √(2 / (mA 12528 : ℝ)) * operatorEnvelope160 12528 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12528 4 +
      2 / (mA 12528 : ℝ) * frobEnvelopeSquared160 12528) +
      transverseConstant160 * √(2 / (mA 12528 : ℝ)) * operatorEnvelope160 12528 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12528 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12528 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12528 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12528 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12528

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12528
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12528) :=
  agentEv (paperDesignP 12528) (Energy32 12528) ∩
  agentEv (paperDesignP 12528) (freshRetainedEvent160 12528 4) ∩
  agentEv (paperDesignP 12528) (FirstMatrix 12528) ∩
  BstLean.Part164.Eop2 12528 ∩ outputCentreEvent (paperCentres 12528)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12528)).real
      (agentEv (paperDesignP 12528) (FirstMatrix 12528))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12528)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12528 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12528)).real (BstLean.Part164.Eop2 12528)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12528)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12528)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12528) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12528) hτ
  have hL := fresh_retained_charge160 (n := 12528) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12528) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12528 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12528) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12528 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12528) (hw : WINDOW (paperDesignP 12528) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12528))
    (hW : ∫ a in K, ((12528 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12528 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12528 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12528 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12528) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12528 : ℝ)) * eR c * 12528 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12528

/-! Exact rational parameters for the dimension-12529 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12529
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
noncomputable def biasRootCap : ℝ := (294617 / 50000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12529 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12529 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12529 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12529.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12529] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12529 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12529 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12529.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12529

namespace BstLean.Part266.Row12529
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

theorem energy_allowance_row : energyAllowance 12529 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12529 : ℝ)) ≤ ((22575043 / 200000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12529 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12529)
  change 0 ≤ agentLayerAllowance 12529 at ha0
  have he : energyWeightAllowance 12529 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12529)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12529)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12529).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12529).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12529)) :
    ∫ a in K, fbR c a ^ k ∂muI 12529 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12529])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12529

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12529
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12529 / 12529 ≤ chi := by
  have hs : √((12529 : ℝ) * 12) ≤ (387747341 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12529}
    (hc : c ∈ outputCentreEvent (paperCentres 12529)) :
    normSq c.2.1.2 ≤ (2 / (12529 : ℝ)) * eR c * 12529 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12529 : ℝ) * normSq (bR c) * chiUp 12529 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12529)).real (outputCentreEvent (paperCentres 12529))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12529

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12529
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12529) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12529) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12529)]
  norm_num [varianceMax]

end BstLean.Part266.Row12529

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12529
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12529) (hc : A1 c ∈ Eop 12529) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12529 : ℝ)) ≤ (2526892631 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12529 : ℝ) ≤ (13991627 / 125000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12529 : ℝ) + 2 * √12529 ≤ (797054127 / 62500) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12529) (hc : c ∈ BstLean.Part164.Eop2 12529) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12529 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12529) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12529 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12529) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12529).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12529) (FirstMatrix 12529))
    (h2 : c ∈ BstLean.Part164.Eop2 12529) (a : BstLean.Part161.Ix 12529) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12529

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12529
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12529) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12529) c ∈ BstLean.Part212.latitudeEvent 12529
      (ENNReal.ofReal (C / 12529))) (K : Set (Ix 12529)) :
    ∫ a in K, ((12529 : ℝ) * VR c a) ^ 2 ∂muI 12529 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12529

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12529
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12529 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12529 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12529 - 1 - 1) 80 ≤ (12685 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12529 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12685 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12529) ≤ (78 * 10 ^ 6 * ((12529 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12529 : ℝ) / 2 + 160) ≤ (2214837473 / 250000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12529 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12529 : ℝ) ^ 2 / 2 + 320 = 156976481 / 2 by norm_num,
    show (12529 : ℝ) ^ 2 / 2 + 160 = 156976161 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12529 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12529 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12529 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12529 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12529)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12529) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12529 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12529)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12529 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12529 ≤ (162 : ℝ) := by
  have hs : √(2 / (12529 : ℝ)) ≤ (2526892631 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12529 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12529 : ℝ) = 12529 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12529 : ℝ) + √12529 + gaussMomConst 80 ≤ 12650 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12529 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12529 : ℝ)) ≤ (22575043 / 200000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12529 4 +
      2 / (mA 12529 : ℝ) * frobEnvelopeSquared160 12529 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12529 4 +
      2 / (mA 12529 : ℝ) * frobEnvelopeSquared160 12529) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12529 : ℝ)) *
      operatorEnvelope160 12529 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12529 4 +
      2 / (mA 12529 : ℝ) * frobEnvelopeSquared160 12529) +
      transverseConstant160 * √(2 / (mA 12529 : ℝ)) * operatorEnvelope160 12529 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12529 4 +
      2 / (mA 12529 : ℝ) * frobEnvelopeSquared160 12529) +
      transverseConstant160 * √(2 / (mA 12529 : ℝ)) * operatorEnvelope160 12529 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12529 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12529 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12529 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12529 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12529

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12529
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12529) :=
  agentEv (paperDesignP 12529) (Energy32 12529) ∩
  agentEv (paperDesignP 12529) (freshRetainedEvent160 12529 4) ∩
  agentEv (paperDesignP 12529) (FirstMatrix 12529) ∩
  BstLean.Part164.Eop2 12529 ∩ outputCentreEvent (paperCentres 12529)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12529)).real
      (agentEv (paperDesignP 12529) (FirstMatrix 12529))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12529)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12529 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12529)).real (BstLean.Part164.Eop2 12529)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12529)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12529)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12529) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12529) hτ
  have hL := fresh_retained_charge160 (n := 12529) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12529) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12529 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12529) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12529 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12529) (hw : WINDOW (paperDesignP 12529) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12529))
    (hW : ∫ a in K, ((12529 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12529 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12529 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12529 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12529) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12529 : ℝ)) * eR c * 12529 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12529

/-! Exact rational parameters for the dimension-12530 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12530
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
noncomputable def biasRootCap : ℝ := (589211 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12530 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12530 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12530 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12530.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12530] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12530 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12530 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12530.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12530

namespace BstLean.Part266.Row12530
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

theorem energy_allowance_row : energyAllowance 12530 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12530 : ℝ)) ≤ ((112866207 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12530 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12530)
  change 0 ≤ agentLayerAllowance 12530 at ha0
  have he : energyWeightAllowance 12530 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12530)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12530)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12530).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12530).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12530)) :
    ∫ a in K, fbR c a ^ k ∂muI 12530 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12530])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12530

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12530
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12530 / 12530 ≤ chi := by
  have hs : √((12530 : ℝ) * 12) ≤ (77552563 / 200000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12530}
    (hc : c ∈ outputCentreEvent (paperCentres 12530)) :
    normSq c.2.1.2 ≤ (2 / (12530 : ℝ)) * eR c * 12530 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12530 : ℝ) * normSq (bR c) * chiUp 12530 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12530)).real (outputCentreEvent (paperCentres 12530))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12530

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12530
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12530) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12530) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12530)]
  norm_num [varianceMax]

end BstLean.Part266.Row12530

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12530
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12530) (hc : A1 c ∈ Eop 12530) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12530 : ℝ)) ≤ (197405609 / 15625000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12530 : ℝ) ≤ (111937483 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12530 : ℝ) + 2 * √12530 ≤ (6376937483 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12530) (hc : c ∈ BstLean.Part164.Eop2 12530) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12530 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12530) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12530 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12530) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12530).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12530) (FirstMatrix 12530))
    (h2 : c ∈ BstLean.Part164.Eop2 12530) (a : BstLean.Part161.Ix 12530) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12530

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12530
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12530) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12530) c ∈ BstLean.Part212.latitudeEvent 12530
      (ENNReal.ofReal (C / 12530))) (K : Set (Ix 12530)) :
    ∫ a in K, ((12530 : ℝ) * VR c a) ^ 2 ∂muI 12530 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12530

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12530
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12530 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12530 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12530 - 1 - 1) 80 ≤ (12686 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12530 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12686 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12530) ≤ (78 * 10 ^ 6 * ((12530 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12530 : ℝ) / 2 + 160) ≤ (4430028499 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12530 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12530 : ℝ) ^ 2 / 2 + 320 = 157001540 / 2 by norm_num,
    show (12530 : ℝ) ^ 2 / 2 + 160 = 157001220 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12530 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12530 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12530 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12530 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12530)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12530) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12530 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12530)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12530 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12530 ≤ (162 : ℝ) := by
  have hs : √(2 / (12530 : ℝ)) ≤ (197405609 / 15625000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12530 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12530 : ℝ) = 12530 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12530 : ℝ) + √12530 + gaussMomConst 80 ≤ 12651 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12530 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12530 : ℝ)) ≤ (112866207 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12530 4 +
      2 / (mA 12530 : ℝ) * frobEnvelopeSquared160 12530 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12530 4 +
      2 / (mA 12530 : ℝ) * frobEnvelopeSquared160 12530) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12530 : ℝ)) *
      operatorEnvelope160 12530 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12530 4 +
      2 / (mA 12530 : ℝ) * frobEnvelopeSquared160 12530) +
      transverseConstant160 * √(2 / (mA 12530 : ℝ)) * operatorEnvelope160 12530 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12530 4 +
      2 / (mA 12530 : ℝ) * frobEnvelopeSquared160 12530) +
      transverseConstant160 * √(2 / (mA 12530 : ℝ)) * operatorEnvelope160 12530 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12530 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12530 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12530 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12530 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12530

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12530
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12530) :=
  agentEv (paperDesignP 12530) (Energy32 12530) ∩
  agentEv (paperDesignP 12530) (freshRetainedEvent160 12530 4) ∩
  agentEv (paperDesignP 12530) (FirstMatrix 12530) ∩
  BstLean.Part164.Eop2 12530 ∩ outputCentreEvent (paperCentres 12530)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12530)).real
      (agentEv (paperDesignP 12530) (FirstMatrix 12530))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12530)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12530 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12530)).real (BstLean.Part164.Eop2 12530)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12530)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12530)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12530) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12530) hτ
  have hL := fresh_retained_charge160 (n := 12530) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12530) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12530 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12530) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12530 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12530) (hw : WINDOW (paperDesignP 12530) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12530))
    (hW : ∫ a in K, ((12530 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12530 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12530 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12530 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12530) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12530 : ℝ)) * eR c * 12530 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12530

/-! Exact rational parameters for the dimension-12531 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12531
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
noncomputable def biasRootCap : ℝ := (589187 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12531 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12531 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12531 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12531.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12531] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12531 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12531 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12531.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12531

namespace BstLean.Part266.Row12531
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

theorem energy_allowance_row : energyAllowance 12531 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12531 : ℝ)) ≤ ((282143 / 2500000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12531 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12531)
  change 0 ≤ agentLayerAllowance 12531 at ha0
  have he : energyWeightAllowance 12531 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12531)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12531)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12531).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12531).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12531)) :
    ∫ a in K, fbR c a ^ k ∂muI 12531 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12531])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12531

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12531
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12531 / 12531 ≤ chi := by
  have hs : √((12531 : ℝ) * 12) ≤ (24236143 / 62500) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12531}
    (hc : c ∈ outputCentreEvent (paperCentres 12531)) :
    normSq c.2.1.2 ≤ (2 / (12531 : ℝ)) * eR c * 12531 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12531 : ℝ) * normSq (bR c) * chiUp 12531 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12531)).real (outputCentreEvent (paperCentres 12531))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12531

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12531
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12531) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12531) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12531)]
  norm_num [varianceMax]

end BstLean.Part266.Row12531

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12531
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12531) (hc : A1 c ∈ Eop 12531) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12531 : ℝ)) ≤ (6316727429 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12531 : ℝ) ≤ (2238839 / 20000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12531 : ℝ) + 2 * √12531 ≤ (127548839 / 10000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12531) (hc : c ∈ BstLean.Part164.Eop2 12531) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12531 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12531) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12531 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12531) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12531).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12531) (FirstMatrix 12531))
    (h2 : c ∈ BstLean.Part164.Eop2 12531) (a : BstLean.Part161.Ix 12531) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12531

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12531
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12531) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12531) c ∈ BstLean.Part212.latitudeEvent 12531
      (ENNReal.ofReal (C / 12531))) (K : Set (Ix 12531)) :
    ∫ a in K, ((12531 : ℝ) * VR c a) ^ 2 ∂muI 12531 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12531

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12531
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12531 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12531 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12531 - 1 - 1) 80 ≤ (12687 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12531 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12687 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12531) ≤ (78 * 10 ^ 6 * ((12531 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12531 : ℝ) / 2 + 160) ≤ (1107595513 / 125000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12531 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12531 : ℝ) ^ 2 / 2 + 320 = 157026601 / 2 by norm_num,
    show (12531 : ℝ) ^ 2 / 2 + 160 = 157026281 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12531 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12531 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12531 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12531 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12531)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12531) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12531 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12531)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12531 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12531 ≤ (162 : ℝ) := by
  have hs : √(2 / (12531 : ℝ)) ≤ (6316727429 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12531 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12531 : ℝ) = 12531 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12531 : ℝ) + √12531 + gaussMomConst 80 ≤ 12652 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12531 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12531 : ℝ)) ≤ (282143 / 2500000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12531 4 +
      2 / (mA 12531 : ℝ) * frobEnvelopeSquared160 12531 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12531 4 +
      2 / (mA 12531 : ℝ) * frobEnvelopeSquared160 12531) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12531 : ℝ)) *
      operatorEnvelope160 12531 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12531 4 +
      2 / (mA 12531 : ℝ) * frobEnvelopeSquared160 12531) +
      transverseConstant160 * √(2 / (mA 12531 : ℝ)) * operatorEnvelope160 12531 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12531 4 +
      2 / (mA 12531 : ℝ) * frobEnvelopeSquared160 12531) +
      transverseConstant160 * √(2 / (mA 12531 : ℝ)) * operatorEnvelope160 12531 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12531 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12531 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12531 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12531 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12531

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12531
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12531) :=
  agentEv (paperDesignP 12531) (Energy32 12531) ∩
  agentEv (paperDesignP 12531) (freshRetainedEvent160 12531 4) ∩
  agentEv (paperDesignP 12531) (FirstMatrix 12531) ∩
  BstLean.Part164.Eop2 12531 ∩ outputCentreEvent (paperCentres 12531)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12531)).real
      (agentEv (paperDesignP 12531) (FirstMatrix 12531))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12531)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12531 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12531)).real (BstLean.Part164.Eop2 12531)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12531)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12531)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12531) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12531) hτ
  have hL := fresh_retained_charge160 (n := 12531) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12531) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12531 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12531) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12531 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12531) (hw : WINDOW (paperDesignP 12531) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12531))
    (hW : ∫ a in K, ((12531 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12531 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12531 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12531 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12531) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12531 : ℝ)) * eR c * 12531 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12531

/-! Exact rational parameters for the dimension-12532 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12532
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
noncomputable def biasRootCap : ℝ := (147291 / 25000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12532 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12532 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12532 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12532.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12532] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12532 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12532 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12532.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12532

namespace BstLean.Part266.Row12532
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

theorem energy_allowance_row : energyAllowance 12532 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12532 : ℝ)) ≤ ((56424097 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12532 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12532)
  change 0 ≤ agentLayerAllowance 12532 at ha0
  have he : energyWeightAllowance 12532 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12532)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12532)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12532).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12532).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12532)) :
    ∫ a in K, fbR c a ^ k ∂muI 12532 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12532])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12532

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12532
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12532 / 12532 ≤ chi := by
  have hs : √((12532 : ℝ) * 12) ≤ (2423711 / 6250) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12532}
    (hc : c ∈ outputCentreEvent (paperCentres 12532)) :
    normSq c.2.1.2 ≤ (2 / (12532 : ℝ)) * eR c * 12532 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12532 : ℝ) * normSq (bR c) * chiUp 12532 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12532)).real (outputCentreEvent (paperCentres 12532))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12532

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12532
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12532) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12532) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12532)]
  norm_num [varianceMax]

end BstLean.Part266.Row12532

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12532
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12532) (hc : A1 c ∈ Eop 12532) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12532 : ℝ)) ≤ (31582377 / 2500000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12532 : ℝ) ≤ (6996651 / 62500) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12532 : ℝ) + 2 * √12532 ≤ (398621651 / 31250) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12532) (hc : c ∈ BstLean.Part164.Eop2 12532) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12532 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12532) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12532 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12532) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12532).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12532) (FirstMatrix 12532))
    (h2 : c ∈ BstLean.Part164.Eop2 12532) (a : BstLean.Part161.Ix 12532) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12532

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12532
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12532) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12532) c ∈ BstLean.Part212.latitudeEvent 12532
      (ENNReal.ofReal (C / 12532))) (K : Set (Ix 12532)) :
    ∫ a in K, ((12532 : ℝ) * VR c a) ^ 2 ∂muI 12532 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12532

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12532
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12532 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12532 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12532 - 1 - 1) 80 ≤ (12688 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12532 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12688 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12532) ≤ (78 * 10 ^ 6 * ((12532 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12532 : ℝ) / 2 + 160) ≤ (886147121 / 100000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12532 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12532 : ℝ) ^ 2 / 2 + 320 = 157051664 / 2 by norm_num,
    show (12532 : ℝ) ^ 2 / 2 + 160 = 157051344 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12532 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12532 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12532 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12532 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12532)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12532) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12532 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12532)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12532 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12532 ≤ (162 : ℝ) := by
  have hs : √(2 / (12532 : ℝ)) ≤ (31582377 / 2500000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12532 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12532 : ℝ) = 12532 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12532 : ℝ) + √12532 + gaussMomConst 80 ≤ 12653 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12532 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12532 : ℝ)) ≤ (56424097 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12532 4 +
      2 / (mA 12532 : ℝ) * frobEnvelopeSquared160 12532 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12532 4 +
      2 / (mA 12532 : ℝ) * frobEnvelopeSquared160 12532) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12532 : ℝ)) *
      operatorEnvelope160 12532 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12532 4 +
      2 / (mA 12532 : ℝ) * frobEnvelopeSquared160 12532) +
      transverseConstant160 * √(2 / (mA 12532 : ℝ)) * operatorEnvelope160 12532 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12532 4 +
      2 / (mA 12532 : ℝ) * frobEnvelopeSquared160 12532) +
      transverseConstant160 * √(2 / (mA 12532 : ℝ)) * operatorEnvelope160 12532 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12532 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12532 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12532 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12532 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12532

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12532
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12532) :=
  agentEv (paperDesignP 12532) (Energy32 12532) ∩
  agentEv (paperDesignP 12532) (freshRetainedEvent160 12532 4) ∩
  agentEv (paperDesignP 12532) (FirstMatrix 12532) ∩
  BstLean.Part164.Eop2 12532 ∩ outputCentreEvent (paperCentres 12532)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12532)).real
      (agentEv (paperDesignP 12532) (FirstMatrix 12532))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12532)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12532 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12532)).real (BstLean.Part164.Eop2 12532)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12532)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12532)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12532) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12532) hτ
  have hL := fresh_retained_charge160 (n := 12532) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12532) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12532 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12532) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12532 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12532) (hw : WINDOW (paperDesignP 12532) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12532))
    (hW : ∫ a in K, ((12532 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12532 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12532 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12532 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12532) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12532 : ℝ)) * eR c * 12532 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12532

/-! Exact rational parameters for the dimension-12533 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12533
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
noncomputable def biasRootCap : ℝ := (29457 / 5000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12533 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12533 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12533 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12533.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12533] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12533 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12533 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12533.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12533

namespace BstLean.Part266.Row12533
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

theorem energy_allowance_row : energyAllowance 12533 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12533 : ℝ)) ≤ ((11283919 / 100000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12533 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12533)
  change 0 ≤ agentLayerAllowance 12533 at ha0
  have he : energyWeightAllowance 12533 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12533)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12533)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12533).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12533).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12533)) :
    ∫ a in K, fbR c a ^ k ∂muI 12533 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12533])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12533

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12533
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12533 / 12533 ≤ chi := by
  have hs : √((12533 : ℝ) * 12) ≤ (24238077 / 62500) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12533}
    (hc : c ∈ outputCentreEvent (paperCentres 12533)) :
    normSq c.2.1.2 ≤ (2 / (12533 : ℝ)) * eR c * 12533 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12533 : ℝ) * normSq (bR c) * chiUp 12533 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12533)).real (outputCentreEvent (paperCentres 12533))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12533

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12533
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12533) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12533) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12533)]
  norm_num [varianceMax]

end BstLean.Part266.Row12533

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12533
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12533) (hc : A1 c ∈ Eop 12533) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12533 : ℝ)) ≤ (6316223401 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12533 : ℝ) ≤ (111950883 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12533 : ℝ) + 2 * √12533 ≤ (6378450883 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12533) (hc : c ∈ BstLean.Part164.Eop2 12533) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12533 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12533) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12533 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12533) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12533).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12533) (FirstMatrix 12533))
    (h2 : c ∈ BstLean.Part164.Eop2 12533) (a : BstLean.Part161.Ix 12533) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12533

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12533
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12533) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12533) c ∈ BstLean.Part212.latitudeEvent 12533
      (ENNReal.ofReal (C / 12533))) (K : Set (Ix 12533)) :
    ∫ a in K, ((12533 : ℝ) * VR c a) ^ 2 ∂muI 12533 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12533

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12533
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12533 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12533 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12533 - 1 - 1) 80 ≤ (12689 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12533 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12689 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12533) ≤ (78 * 10 ^ 6 * ((12533 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12533 : ℝ) / 2 + 160) ≤ (2215544579 / 250000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12533 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12533 : ℝ) ^ 2 / 2 + 320 = 157076729 / 2 by norm_num,
    show (12533 : ℝ) ^ 2 / 2 + 160 = 157076409 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12533 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12533 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12533 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12533 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12533)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12533) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12533 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12533)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12533 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12533 ≤ (162 : ℝ) := by
  have hs : √(2 / (12533 : ℝ)) ≤ (6316223401 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12533 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12533 : ℝ) = 12533 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12533 : ℝ) + √12533 + gaussMomConst 80 ≤ 12654 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12533 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12533 : ℝ)) ≤ (11283919 / 100000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12533 4 +
      2 / (mA 12533 : ℝ) * frobEnvelopeSquared160 12533 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12533 4 +
      2 / (mA 12533 : ℝ) * frobEnvelopeSquared160 12533) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12533 : ℝ)) *
      operatorEnvelope160 12533 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12533 4 +
      2 / (mA 12533 : ℝ) * frobEnvelopeSquared160 12533) +
      transverseConstant160 * √(2 / (mA 12533 : ℝ)) * operatorEnvelope160 12533 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12533 4 +
      2 / (mA 12533 : ℝ) * frobEnvelopeSquared160 12533) +
      transverseConstant160 * √(2 / (mA 12533 : ℝ)) * operatorEnvelope160 12533 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12533 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12533 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12533 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12533 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12533

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12533
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12533) :=
  agentEv (paperDesignP 12533) (Energy32 12533) ∩
  agentEv (paperDesignP 12533) (freshRetainedEvent160 12533 4) ∩
  agentEv (paperDesignP 12533) (FirstMatrix 12533) ∩
  BstLean.Part164.Eop2 12533 ∩ outputCentreEvent (paperCentres 12533)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12533)).real
      (agentEv (paperDesignP 12533) (FirstMatrix 12533))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12533)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12533 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12533)).real (BstLean.Part164.Eop2 12533)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12533)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12533)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12533) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12533) hτ
  have hL := fresh_retained_charge160 (n := 12533) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12533) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12533 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12533) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12533 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12533) (hw : WINDOW (paperDesignP 12533) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12533))
    (hW : ∫ a in K, ((12533 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12533 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12533 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12533 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12533) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12533 : ℝ)) * eR c * 12533 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12533

/-! Exact rational parameters for the dimension-12534 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12534
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
noncomputable def biasRootCap : ℝ := (589117 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12534 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12534 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12534 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12534.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12534] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12534 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12534 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12534.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12534

namespace BstLean.Part266.Row12534
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

theorem energy_allowance_row : energyAllowance 12534 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12534 : ℝ)) ≤ ((112830187 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12534 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12534)
  change 0 ≤ agentLayerAllowance 12534 at ha0
  have he : energyWeightAllowance 12534 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12534)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12534)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12534).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12534).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12534)) :
    ∫ a in K, fbR c a ^ k ∂muI 12534 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12534])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12534

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12534
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12534 / 12534 ≤ chi := by
  have hs : √((12534 : ℝ) * 12) ≤ (387824703 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12534}
    (hc : c ∈ outputCentreEvent (paperCentres 12534)) :
    normSq c.2.1.2 ≤ (2 / (12534 : ℝ)) * eR c * 12534 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12534 : ℝ) * normSq (bR c) * chiUp 12534 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12534)).real (outputCentreEvent (paperCentres 12534))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12534

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12534
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12534) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12534) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12534)]
  norm_num [varianceMax]

end BstLean.Part266.Row12534

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12534
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12534) (hc : A1 c ∈ Eop 12534) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12534 : ℝ)) ≤ (2526388573 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12534 : ℝ) ≤ (111955349 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12534 : ℝ) + 2 * √12534 ≤ (6378955349 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12534) (hc : c ∈ BstLean.Part164.Eop2 12534) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12534 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12534) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12534 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12534) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12534).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12534) (FirstMatrix 12534))
    (h2 : c ∈ BstLean.Part164.Eop2 12534) (a : BstLean.Part161.Ix 12534) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12534

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12534
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12534) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12534) c ∈ BstLean.Part212.latitudeEvent 12534
      (ENNReal.ofReal (C / 12534))) (K : Set (Ix 12534)) :
    ∫ a in K, ((12534 : ℝ) * VR c a) ^ 2 ∂muI 12534 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12534

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12534
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12534 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12534 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12534 - 1 - 1) 80 ≤ (12690 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12534 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12690 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12534) ≤ (78 * 10 ^ 6 * ((12534 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12534 : ℝ) / 2 + 160) ≤ (4431442711 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12534 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12534 : ℝ) ^ 2 / 2 + 320 = 157101796 / 2 by norm_num,
    show (12534 : ℝ) ^ 2 / 2 + 160 = 157101476 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12534 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12534 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12534 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12534 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12534)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12534) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12534 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12534)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12534 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12534 ≤ (162 : ℝ) := by
  have hs : √(2 / (12534 : ℝ)) ≤ (2526388573 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12534 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12534 : ℝ) = 12534 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12534 : ℝ) + √12534 + gaussMomConst 80 ≤ 12655 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12534 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12534 : ℝ)) ≤ (112830187 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12534 4 +
      2 / (mA 12534 : ℝ) * frobEnvelopeSquared160 12534 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12534 4 +
      2 / (mA 12534 : ℝ) * frobEnvelopeSquared160 12534) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12534 : ℝ)) *
      operatorEnvelope160 12534 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12534 4 +
      2 / (mA 12534 : ℝ) * frobEnvelopeSquared160 12534) +
      transverseConstant160 * √(2 / (mA 12534 : ℝ)) * operatorEnvelope160 12534 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12534 4 +
      2 / (mA 12534 : ℝ) * frobEnvelopeSquared160 12534) +
      transverseConstant160 * √(2 / (mA 12534 : ℝ)) * operatorEnvelope160 12534 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12534 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12534 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12534 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12534 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12534

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12534
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12534) :=
  agentEv (paperDesignP 12534) (Energy32 12534) ∩
  agentEv (paperDesignP 12534) (freshRetainedEvent160 12534 4) ∩
  agentEv (paperDesignP 12534) (FirstMatrix 12534) ∩
  BstLean.Part164.Eop2 12534 ∩ outputCentreEvent (paperCentres 12534)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12534)).real
      (agentEv (paperDesignP 12534) (FirstMatrix 12534))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12534)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12534 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12534)).real (BstLean.Part164.Eop2 12534)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12534)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12534)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12534) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12534) hτ
  have hL := fresh_retained_charge160 (n := 12534) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12534) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12534 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12534) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12534 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12534) (hw : WINDOW (paperDesignP 12534) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12534))
    (hW : ∫ a in K, ((12534 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12534 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12534 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12534 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12534) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12534 : ℝ)) * eR c * 12534 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12534

/-! Exact rational parameters for the dimension-12535 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12535
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
noncomputable def biasRootCap : ℝ := (589093 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12535 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12535 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12535 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12535.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12535] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12535 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12535 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12535.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12535

namespace BstLean.Part266.Row12535
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

theorem energy_allowance_row : energyAllowance 12535 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12535 : ℝ)) ≤ ((56410593 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12535 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12535)
  change 0 ≤ agentLayerAllowance 12535 at ha0
  have he : energyWeightAllowance 12535 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12535)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12535)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12535).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12535).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12535)) :
    ∫ a in K, fbR c a ^ k ∂muI 12535 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12535])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12535

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12535
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12535 / 12535 ≤ chi := by
  have hs : √((12535 : ℝ) * 12) ≤ (193920087 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12535}
    (hc : c ∈ outputCentreEvent (paperCentres 12535)) :
    normSq c.2.1.2 ≤ (2 / (12535 : ℝ)) * eR c * 12535 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12535 : ℝ) * normSq (bR c) * chiUp 12535 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12535)).real (outputCentreEvent (paperCentres 12535))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12535

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12535
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12535) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12535) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12535)]
  norm_num [varianceMax]

end BstLean.Part266.Row12535

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12535
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12535) (hc : A1 c ∈ Eop 12535) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12535 : ℝ)) ≤ (3157859747 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12535 : ℝ) ≤ (22391963 / 200000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12535 : ℝ) + 2 * √12535 ≤ (1275891963 / 100000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12535) (hc : c ∈ BstLean.Part164.Eop2 12535) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12535 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12535) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12535 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12535) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12535).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12535) (FirstMatrix 12535))
    (h2 : c ∈ BstLean.Part164.Eop2 12535) (a : BstLean.Part161.Ix 12535) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12535

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12535
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12535) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12535) c ∈ BstLean.Part212.latitudeEvent 12535
      (ENNReal.ofReal (C / 12535))) (K : Set (Ix 12535)) :
    ∫ a in K, ((12535 : ℝ) * VR c a) ^ 2 ∂muI 12535 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12535

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12535
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12535 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12535 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12535 - 1 - 1) 80 ≤ (12691 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12535 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12691 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12535) ≤ (78 * 10 ^ 6 * ((12535 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12535 : ℝ) / 2 + 160) ≤ (553974533 / 62500) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12535 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12535 : ℝ) ^ 2 / 2 + 320 = 157126865 / 2 by norm_num,
    show (12535 : ℝ) ^ 2 / 2 + 160 = 157126545 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12535 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12535 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12535 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12535 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12535)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12535) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12535 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12535)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12535 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12535 ≤ (162 : ℝ) := by
  have hs : √(2 / (12535 : ℝ)) ≤ (3157859747 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12535 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12535 : ℝ) = 12535 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12535 : ℝ) + √12535 + gaussMomConst 80 ≤ 12656 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12535 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12535 : ℝ)) ≤ (56410593 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12535 4 +
      2 / (mA 12535 : ℝ) * frobEnvelopeSquared160 12535 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12535 4 +
      2 / (mA 12535 : ℝ) * frobEnvelopeSquared160 12535) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12535 : ℝ)) *
      operatorEnvelope160 12535 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12535 4 +
      2 / (mA 12535 : ℝ) * frobEnvelopeSquared160 12535) +
      transverseConstant160 * √(2 / (mA 12535 : ℝ)) * operatorEnvelope160 12535 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12535 4 +
      2 / (mA 12535 : ℝ) * frobEnvelopeSquared160 12535) +
      transverseConstant160 * √(2 / (mA 12535 : ℝ)) * operatorEnvelope160 12535 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12535 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12535 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12535 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12535 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12535

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12535
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12535) :=
  agentEv (paperDesignP 12535) (Energy32 12535) ∩
  agentEv (paperDesignP 12535) (freshRetainedEvent160 12535 4) ∩
  agentEv (paperDesignP 12535) (FirstMatrix 12535) ∩
  BstLean.Part164.Eop2 12535 ∩ outputCentreEvent (paperCentres 12535)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12535)).real
      (agentEv (paperDesignP 12535) (FirstMatrix 12535))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12535)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12535 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12535)).real (BstLean.Part164.Eop2 12535)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12535)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12535)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12535) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12535) hτ
  have hL := fresh_retained_charge160 (n := 12535) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12535) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12535 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12535) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12535 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12535) (hw : WINDOW (paperDesignP 12535) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12535))
    (hW : ∫ a in K, ((12535 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12535 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12535 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12535 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12535) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12535 : ℝ)) * eR c * 12535 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12535

/-! Exact rational parameters for the dimension-12536 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12536
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
noncomputable def biasRootCap : ℝ := (58907 / 10000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12536 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12536 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12536 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12536.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12536] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12536 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12536 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12536.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12536

namespace BstLean.Part266.Row12536
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

theorem energy_allowance_row : energyAllowance 12536 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12536 : ℝ)) ≤ ((56406093 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12536 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12536)
  change 0 ≤ agentLayerAllowance 12536 at ha0
  have he : energyWeightAllowance 12536 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12536)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12536)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12536).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12536).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12536)) :
    ∫ a in K, fbR c a ^ k ∂muI 12536 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12536])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12536

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12536
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12536 / 12536 ≤ chi := by
  have hs : √((12536 : ℝ) * 12) ≤ (96963911 / 250000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12536}
    (hc : c ∈ outputCentreEvent (paperCentres 12536)) :
    normSq c.2.1.2 ≤ (2 / (12536 : ℝ)) * eR c * 12536 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12536 : ℝ) * normSq (bR c) * chiUp 12536 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12536)).real (outputCentreEvent (paperCentres 12536))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12536

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12536
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12536) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12536) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12536)]
  norm_num [varianceMax]

end BstLean.Part266.Row12536

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12536
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12536) (hc : A1 c ∈ Eop 12536) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12536 : ℝ)) ≤ (12630935171 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12536 : ℝ) ≤ (111964281 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12536 : ℝ) + 2 * √12536 ≤ (6379964281 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12536) (hc : c ∈ BstLean.Part164.Eop2 12536) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12536 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12536) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12536 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12536) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12536).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12536) (FirstMatrix 12536))
    (h2 : c ∈ BstLean.Part164.Eop2 12536) (a : BstLean.Part161.Ix 12536) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12536

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12536
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12536) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12536) c ∈ BstLean.Part212.latitudeEvent 12536
      (ENNReal.ofReal (C / 12536))) (K : Set (Ix 12536)) :
    ∫ a in K, ((12536 : ℝ) * VR c a) ^ 2 ∂muI 12536 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12536

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12536
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12536 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12536 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12536 - 1 - 1) 80 ≤ (12692 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12536 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12692 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12536) ≤ (78 * 10 ^ 6 * ((12536 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12536 : ℝ) / 2 + 160) ≤ (4432149817 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12536 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12536 : ℝ) ^ 2 / 2 + 320 = 157151936 / 2 by norm_num,
    show (12536 : ℝ) ^ 2 / 2 + 160 = 157151616 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12536 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12536 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12536 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12536 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12536)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12536) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12536 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12536)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12536 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12536 ≤ (162 : ℝ) := by
  have hs : √(2 / (12536 : ℝ)) ≤ (12630935171 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12536 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12536 : ℝ) = 12536 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12536 : ℝ) + √12536 + gaussMomConst 80 ≤ 12657 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12536 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12536 : ℝ)) ≤ (56406093 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12536 4 +
      2 / (mA 12536 : ℝ) * frobEnvelopeSquared160 12536 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12536 4 +
      2 / (mA 12536 : ℝ) * frobEnvelopeSquared160 12536) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12536 : ℝ)) *
      operatorEnvelope160 12536 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12536 4 +
      2 / (mA 12536 : ℝ) * frobEnvelopeSquared160 12536) +
      transverseConstant160 * √(2 / (mA 12536 : ℝ)) * operatorEnvelope160 12536 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12536 4 +
      2 / (mA 12536 : ℝ) * frobEnvelopeSquared160 12536) +
      transverseConstant160 * √(2 / (mA 12536 : ℝ)) * operatorEnvelope160 12536 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12536 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12536 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12536 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12536 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12536

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12536
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12536) :=
  agentEv (paperDesignP 12536) (Energy32 12536) ∩
  agentEv (paperDesignP 12536) (freshRetainedEvent160 12536 4) ∩
  agentEv (paperDesignP 12536) (FirstMatrix 12536) ∩
  BstLean.Part164.Eop2 12536 ∩ outputCentreEvent (paperCentres 12536)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12536)).real
      (agentEv (paperDesignP 12536) (FirstMatrix 12536))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12536)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12536 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12536)).real (BstLean.Part164.Eop2 12536)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12536)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12536)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12536) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12536) hτ
  have hL := fresh_retained_charge160 (n := 12536) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12536) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12536 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12536) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12536 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12536) (hw : WINDOW (paperDesignP 12536) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12536))
    (hW : ∫ a in K, ((12536 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12536 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12536 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12536 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12536) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12536 : ℝ)) * eR c * 12536 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12536

/-! Exact rational parameters for the dimension-12537 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12537
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
noncomputable def biasRootCap : ℝ := (294523 / 50000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12537 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12537 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12537 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12537.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12537] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12537 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12537 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12537.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12537

namespace BstLean.Part266.Row12537
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

theorem energy_allowance_row : energyAllowance 12537 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12537 : ℝ)) ≤ ((28200797 / 250000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12537 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12537)
  change 0 ≤ agentLayerAllowance 12537 at ha0
  have he : energyWeightAllowance 12537 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12537)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12537)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12537).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12537).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12537)) :
    ∫ a in K, fbR c a ^ k ∂muI 12537 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12537])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12537

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12537
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12537 / 12537 ≤ chi := by
  have hs : √((12537 : ℝ) * 12) ≤ (387871113 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12537}
    (hc : c ∈ outputCentreEvent (paperCentres 12537)) :
    normSq c.2.1.2 ≤ (2 / (12537 : ℝ)) * eR c * 12537 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12537 : ℝ) * normSq (bR c) * chiUp 12537 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12537)).real (outputCentreEvent (paperCentres 12537))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12537

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12537
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12537) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12537) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12537)]
  norm_num [varianceMax]

end BstLean.Part266.Row12537

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12537
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12537) (hc : A1 c ∈ Eop 12537) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12537 : ℝ)) ≤ (2526086283 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12537 : ℝ) ≤ (55984373 / 500000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12537 : ℝ) + 2 * √12537 ≤ (3190234373 / 250000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12537) (hc : c ∈ BstLean.Part164.Eop2 12537) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12537 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12537) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12537 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12537) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12537).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12537) (FirstMatrix 12537))
    (h2 : c ∈ BstLean.Part164.Eop2 12537) (a : BstLean.Part161.Ix 12537) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12537

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12537
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12537) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12537) c ∈ BstLean.Part212.latitudeEvent 12537
      (ENNReal.ofReal (C / 12537))) (K : Set (Ix 12537)) :
    ∫ a in K, ((12537 : ℝ) * VR c a) ^ 2 ∂muI 12537 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12537

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12537
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12537 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12537 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12537 - 1 - 1) 80 ≤ (12693 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12537 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12693 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12537) ≤ (78 * 10 ^ 6 * ((12537 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12537 : ℝ) / 2 + 160) ≤ (443250337 / 50000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12537 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12537 : ℝ) ^ 2 / 2 + 320 = 157177009 / 2 by norm_num,
    show (12537 : ℝ) ^ 2 / 2 + 160 = 157176689 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12537 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12537 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12537 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12537 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12537)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12537) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12537 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12537)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12537 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12537 ≤ (162 : ℝ) := by
  have hs : √(2 / (12537 : ℝ)) ≤ (2526086283 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12537 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12537 : ℝ) = 12537 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12537 : ℝ) + √12537 + gaussMomConst 80 ≤ 12658 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12537 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12537 : ℝ)) ≤ (28200797 / 250000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12537 4 +
      2 / (mA 12537 : ℝ) * frobEnvelopeSquared160 12537 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12537 4 +
      2 / (mA 12537 : ℝ) * frobEnvelopeSquared160 12537) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12537 : ℝ)) *
      operatorEnvelope160 12537 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12537 4 +
      2 / (mA 12537 : ℝ) * frobEnvelopeSquared160 12537) +
      transverseConstant160 * √(2 / (mA 12537 : ℝ)) * operatorEnvelope160 12537 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12537 4 +
      2 / (mA 12537 : ℝ) * frobEnvelopeSquared160 12537) +
      transverseConstant160 * √(2 / (mA 12537 : ℝ)) * operatorEnvelope160 12537 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12537 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12537 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12537 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12537 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12537

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12537
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12537) :=
  agentEv (paperDesignP 12537) (Energy32 12537) ∩
  agentEv (paperDesignP 12537) (freshRetainedEvent160 12537 4) ∩
  agentEv (paperDesignP 12537) (FirstMatrix 12537) ∩
  BstLean.Part164.Eop2 12537 ∩ outputCentreEvent (paperCentres 12537)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12537)).real
      (agentEv (paperDesignP 12537) (FirstMatrix 12537))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12537)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12537 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12537)).real (BstLean.Part164.Eop2 12537)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12537)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12537)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12537) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12537) hτ
  have hL := fresh_retained_charge160 (n := 12537) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12537) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12537 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12537) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12537 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12537) (hw : WINDOW (paperDesignP 12537) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12537))
    (hW : ∫ a in K, ((12537 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12537 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12537 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12537 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12537) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12537 : ℝ)) * eR c * 12537 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12537

/-! Exact rational parameters for the dimension-12538 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12538
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
noncomputable def biasRootCap : ℝ := (589023 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12538 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12538 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12538 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12538.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12538] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12538 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12538 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12538.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12538

namespace BstLean.Part266.Row12538
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

theorem energy_allowance_row : energyAllowance 12538 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12538 : ℝ)) ≤ ((112794191 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12538 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12538)
  change 0 ≤ agentLayerAllowance 12538 at ha0
  have he : energyWeightAllowance 12538 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12538)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12538)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12538).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12538).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12538)) :
    ∫ a in K, fbR c a ^ k ∂muI 12538 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12538])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12538

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12538
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12538 / 12538 ≤ chi := by
  have hs : √((12538 : ℝ) * 12) ≤ (193943291 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12538}
    (hc : c ∈ outputCentreEvent (paperCentres 12538)) :
    normSq c.2.1.2 ≤ (2 / (12538 : ℝ)) * eR c * 12538 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12538 : ℝ) * normSq (bR c) * chiUp 12538 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12538)).real (outputCentreEvent (paperCentres 12538))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12538

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12538
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12538) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12538) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12538)]
  norm_num [varianceMax]

end BstLean.Part266.Row12538

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12538
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12538) (hc : A1 c ∈ Eop 12538) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12538 : ℝ)) ≤ (12629927719 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12538 : ℝ) ≤ (27993303 / 250000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12538 : ℝ) + 2 * √12538 ≤ (1595243303 / 125000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12538) (hc : c ∈ BstLean.Part164.Eop2 12538) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12538 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12538) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12538 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12538) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12538).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12538) (FirstMatrix 12538))
    (h2 : c ∈ BstLean.Part164.Eop2 12538) (a : BstLean.Part161.Ix 12538) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12538

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12538
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12538) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12538) c ∈ BstLean.Part212.latitudeEvent 12538
      (ENNReal.ofReal (C / 12538))) (K : Set (Ix 12538)) :
    ∫ a in K, ((12538 : ℝ) * VR c a) ^ 2 ∂muI 12538 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12538

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12538
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12538 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12538 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12538 - 1 - 1) 80 ≤ (12694 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12538 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12694 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12538) ≤ (78 * 10 ^ 6 * ((12538 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12538 : ℝ) / 2 + 160) ≤ (8865713847 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12538 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12538 : ℝ) ^ 2 / 2 + 320 = 157202084 / 2 by norm_num,
    show (12538 : ℝ) ^ 2 / 2 + 160 = 157201764 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12538 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12538 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12538 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12538 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12538)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12538) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12538 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12538)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12538 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12538 ≤ (162 : ℝ) := by
  have hs : √(2 / (12538 : ℝ)) ≤ (12629927719 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12538 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12538 : ℝ) = 12538 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12538 : ℝ) + √12538 + gaussMomConst 80 ≤ 12659 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12538 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12538 : ℝ)) ≤ (112794191 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12538 4 +
      2 / (mA 12538 : ℝ) * frobEnvelopeSquared160 12538 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12538 4 +
      2 / (mA 12538 : ℝ) * frobEnvelopeSquared160 12538) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12538 : ℝ)) *
      operatorEnvelope160 12538 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12538 4 +
      2 / (mA 12538 : ℝ) * frobEnvelopeSquared160 12538) +
      transverseConstant160 * √(2 / (mA 12538 : ℝ)) * operatorEnvelope160 12538 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12538 4 +
      2 / (mA 12538 : ℝ) * frobEnvelopeSquared160 12538) +
      transverseConstant160 * √(2 / (mA 12538 : ℝ)) * operatorEnvelope160 12538 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12538 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12538 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12538 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12538 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12538

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12538
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12538) :=
  agentEv (paperDesignP 12538) (Energy32 12538) ∩
  agentEv (paperDesignP 12538) (freshRetainedEvent160 12538 4) ∩
  agentEv (paperDesignP 12538) (FirstMatrix 12538) ∩
  BstLean.Part164.Eop2 12538 ∩ outputCentreEvent (paperCentres 12538)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12538)).real
      (agentEv (paperDesignP 12538) (FirstMatrix 12538))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12538)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12538 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12538)).real (BstLean.Part164.Eop2 12538)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12538)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12538)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12538) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12538) hτ
  have hL := fresh_retained_charge160 (n := 12538) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12538) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12538 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12538) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12538 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12538) (hw : WINDOW (paperDesignP 12538) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12538))
    (hW : ∫ a in K, ((12538 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12538 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12538 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12538 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12538) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12538 : ℝ)) * eR c * 12538 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12538

/-! Exact rational parameters for the dimension-12539 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12539
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
noncomputable def biasRootCap : ℝ := (588999 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12539 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12539 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12539 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12539.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12539] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12539 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12539 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12539.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12539

namespace BstLean.Part266.Row12539
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

theorem energy_allowance_row : energyAllowance 12539 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12539 : ℝ)) ≤ ((28196299 / 250000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12539 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12539)
  change 0 ≤ agentLayerAllowance 12539 at ha0
  have he : energyWeightAllowance 12539 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12539)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12539)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12539).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12539).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12539)) :
    ∫ a in K, fbR c a ^ k ∂muI 12539 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12539])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12539

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12539
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12539 / 12539 ≤ chi := by
  have hs : √((12539 : ℝ) * 12) ≤ (7758041 / 20000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12539}
    (hc : c ∈ outputCentreEvent (paperCentres 12539)) :
    normSq c.2.1.2 ≤ (2 / (12539 : ℝ)) * eR c * 12539 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12539 : ℝ) * normSq (bR c) * chiUp 12539 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12539)).real (outputCentreEvent (paperCentres 12539))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12539

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12539
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12539) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12539) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12539)]
  norm_num [varianceMax]

end BstLean.Part266.Row12539

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12539
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12539) (hc : A1 c ∈ Eop 12539) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12539 : ℝ)) ≤ (12629424083 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12539 : ℝ) ≤ (111977677 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12539 : ℝ) + 2 * √12539 ≤ (6381477677 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12539) (hc : c ∈ BstLean.Part164.Eop2 12539) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12539 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12539) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12539 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12539) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12539).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12539) (FirstMatrix 12539))
    (h2 : c ∈ BstLean.Part164.Eop2 12539) (a : BstLean.Part161.Ix 12539) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12539

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12539
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12539) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12539) c ∈ BstLean.Part212.latitudeEvent 12539
      (ENNReal.ofReal (C / 12539))) (K : Set (Ix 12539)) :
    ∫ a in K, ((12539 : ℝ) * VR c a) ^ 2 ∂muI 12539 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12539

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12539
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12539 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12539 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12539 - 1 - 1) 80 ≤ (12695 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12539 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12695 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12539) ≤ (78 * 10 ^ 6 * ((12539 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12539 : ℝ) / 2 + 160) ≤ (8866420953 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12539 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12539 : ℝ) ^ 2 / 2 + 320 = 157227161 / 2 by norm_num,
    show (12539 : ℝ) ^ 2 / 2 + 160 = 157226841 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12539 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12539 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12539 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12539 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12539)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12539) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12539 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12539)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12539 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12539 ≤ (162 : ℝ) := by
  have hs : √(2 / (12539 : ℝ)) ≤ (12629424083 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12539 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12539 : ℝ) = 12539 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12539 : ℝ) + √12539 + gaussMomConst 80 ≤ 12660 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12539 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12539 : ℝ)) ≤ (28196299 / 250000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12539 4 +
      2 / (mA 12539 : ℝ) * frobEnvelopeSquared160 12539 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12539 4 +
      2 / (mA 12539 : ℝ) * frobEnvelopeSquared160 12539) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12539 : ℝ)) *
      operatorEnvelope160 12539 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12539 4 +
      2 / (mA 12539 : ℝ) * frobEnvelopeSquared160 12539) +
      transverseConstant160 * √(2 / (mA 12539 : ℝ)) * operatorEnvelope160 12539 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12539 4 +
      2 / (mA 12539 : ℝ) * frobEnvelopeSquared160 12539) +
      transverseConstant160 * √(2 / (mA 12539 : ℝ)) * operatorEnvelope160 12539 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12539 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12539 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12539 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12539 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12539

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12539
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12539) :=
  agentEv (paperDesignP 12539) (Energy32 12539) ∩
  agentEv (paperDesignP 12539) (freshRetainedEvent160 12539 4) ∩
  agentEv (paperDesignP 12539) (FirstMatrix 12539) ∩
  BstLean.Part164.Eop2 12539 ∩ outputCentreEvent (paperCentres 12539)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12539)).real
      (agentEv (paperDesignP 12539) (FirstMatrix 12539))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12539)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12539 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12539)).real (BstLean.Part164.Eop2 12539)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12539)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12539)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12539) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12539) hτ
  have hL := fresh_retained_charge160 (n := 12539) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12539) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12539 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12539) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12539 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12539) (hw : WINDOW (paperDesignP 12539) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12539))
    (hW : ∫ a in K, ((12539 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12539 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12539 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12539 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12539) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12539 : ℝ)) * eR c * 12539 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12539

/-! Exact rational parameters for the dimension-12540 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12540
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
noncomputable def biasRootCap : ℝ := (36811 / 6250000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12540 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12540 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12540 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12540.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12540] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12540 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12540 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12540.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12540

namespace BstLean.Part266.Row12540
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

theorem energy_allowance_row : energyAllowance 12540 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12540 : ℝ)) ≤ ((56388101 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12540 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12540)
  change 0 ≤ agentLayerAllowance 12540 at ha0
  have he : energyWeightAllowance 12540 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12540)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12540)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12540).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12540).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12540)) :
    ∫ a in K, fbR c a ^ k ∂muI 12540 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12540])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12540

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12540
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12540 / 12540 ≤ chi := by
  have hs : √((12540 : ℝ) * 12) ≤ (193958759 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12540}
    (hc : c ∈ outputCentreEvent (paperCentres 12540)) :
    normSq c.2.1.2 ≤ (2 / (12540 : ℝ)) * eR c * 12540 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12540 : ℝ) * normSq (bR c) * chiUp 12540 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12540)).real (outputCentreEvent (paperCentres 12540))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12540

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12540
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12540) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12540) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12540)]
  norm_num [varianceMax]

end BstLean.Part266.Row12540

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12540
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12540) (hc : A1 c ∈ Eop 12540) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12540 : ℝ)) ≤ (3157230127 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12540 : ℝ) ≤ (55991071 / 500000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12540 : ℝ) + 2 * √12540 ≤ (3190991071 / 250000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12540) (hc : c ∈ BstLean.Part164.Eop2 12540) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12540 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12540) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12540 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12540) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12540).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12540) (FirstMatrix 12540))
    (h2 : c ∈ BstLean.Part164.Eop2 12540) (a : BstLean.Part161.Ix 12540) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12540

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12540
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12540) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12540) c ∈ BstLean.Part212.latitudeEvent 12540
      (ENNReal.ofReal (C / 12540))) (K : Set (Ix 12540)) :
    ∫ a in K, ((12540 : ℝ) * VR c a) ^ 2 ∂muI 12540 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12540

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12540
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12540 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12540 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12540 - 1 - 1) 80 ≤ (12696 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12540 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12696 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12540) ≤ (78 * 10 ^ 6 * ((12540 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12540 : ℝ) / 2 + 160) ≤ (8867128059 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12540 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12540 : ℝ) ^ 2 / 2 + 320 = 157252240 / 2 by norm_num,
    show (12540 : ℝ) ^ 2 / 2 + 160 = 157251920 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12540 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12540 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12540 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12540 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12540)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12540) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12540 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12540)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12540 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12540 ≤ (162 : ℝ) := by
  have hs : √(2 / (12540 : ℝ)) ≤ (3157230127 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12540 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12540 : ℝ) = 12540 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12540 : ℝ) + √12540 + gaussMomConst 80 ≤ 12661 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12540 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12540 : ℝ)) ≤ (56388101 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12540 4 +
      2 / (mA 12540 : ℝ) * frobEnvelopeSquared160 12540 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12540 4 +
      2 / (mA 12540 : ℝ) * frobEnvelopeSquared160 12540) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12540 : ℝ)) *
      operatorEnvelope160 12540 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12540 4 +
      2 / (mA 12540 : ℝ) * frobEnvelopeSquared160 12540) +
      transverseConstant160 * √(2 / (mA 12540 : ℝ)) * operatorEnvelope160 12540 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12540 4 +
      2 / (mA 12540 : ℝ) * frobEnvelopeSquared160 12540) +
      transverseConstant160 * √(2 / (mA 12540 : ℝ)) * operatorEnvelope160 12540 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12540 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12540 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12540 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12540 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12540

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12540
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12540) :=
  agentEv (paperDesignP 12540) (Energy32 12540) ∩
  agentEv (paperDesignP 12540) (freshRetainedEvent160 12540 4) ∩
  agentEv (paperDesignP 12540) (FirstMatrix 12540) ∩
  BstLean.Part164.Eop2 12540 ∩ outputCentreEvent (paperCentres 12540)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12540)).real
      (agentEv (paperDesignP 12540) (FirstMatrix 12540))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12540)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12540 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12540)).real (BstLean.Part164.Eop2 12540)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12540)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12540)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12540) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12540) hτ
  have hL := fresh_retained_charge160 (n := 12540) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12540) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12540 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12540) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12540 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12540) (hw : WINDOW (paperDesignP 12540) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12540))
    (hW : ∫ a in K, ((12540 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12540 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12540 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12540 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12540) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12540 : ℝ)) * eR c * 12540 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12540

/-! Exact rational parameters for the dimension-12541 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12541
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
noncomputable def biasRootCap : ℝ := (73619 / 12500000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12541 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12541 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12541 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12541.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12541] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12541 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12541 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12541.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12541

namespace BstLean.Part266.Row12541
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

theorem energy_allowance_row : energyAllowance 12541 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12541 : ℝ)) ≤ ((112767209 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12541 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12541)
  change 0 ≤ agentLayerAllowance 12541 at ha0
  have he : energyWeightAllowance 12541 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12541)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12541)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12541).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12541).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12541)) :
    ∫ a in K, fbR c a ^ k ∂muI 12541 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12541])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12541

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12541
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12541 / 12541 ≤ chi := by
  have hs : √((12541 : ℝ) * 12) ≤ (48491623 / 125000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12541}
    (hc : c ∈ outputCentreEvent (paperCentres 12541)) :
    normSq c.2.1.2 ≤ (2 / (12541 : ℝ)) * eR c * 12541 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12541 : ℝ) * normSq (bR c) * chiUp 12541 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12541)).real (outputCentreEvent (paperCentres 12541))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12541

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12541
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12541) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12541) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12541)]
  norm_num [varianceMax]

end BstLean.Part266.Row12541

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12541
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12541) (hc : A1 c ∈ Eop 12541) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12541 : ℝ)) ≤ (394638031 / 31250000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12541 : ℝ) ≤ (111986607 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12541 : ℝ) + 2 * √12541 ≤ (6382486607 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12541) (hc : c ∈ BstLean.Part164.Eop2 12541) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12541 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12541) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12541 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12541) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12541).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12541) (FirstMatrix 12541))
    (h2 : c ∈ BstLean.Part164.Eop2 12541) (a : BstLean.Part161.Ix 12541) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12541

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12541
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12541) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12541) c ∈ BstLean.Part212.latitudeEvent 12541
      (ENNReal.ofReal (C / 12541))) (K : Set (Ix 12541)) :
    ∫ a in K, ((12541 : ℝ) * VR c a) ^ 2 ∂muI 12541 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12541

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12541
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12541 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12541 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12541 - 1 - 1) 80 ≤ (12697 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12541 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12697 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12541) ≤ (78 * 10 ^ 6 * ((12541 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12541 : ℝ) / 2 + 160) ≤ (1773567033 / 200000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12541 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12541 : ℝ) ^ 2 / 2 + 320 = 157277321 / 2 by norm_num,
    show (12541 : ℝ) ^ 2 / 2 + 160 = 157277001 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12541 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12541 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12541 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12541 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12541)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12541) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12541 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12541)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12541 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12541 ≤ (162 : ℝ) := by
  have hs : √(2 / (12541 : ℝ)) ≤ (394638031 / 31250000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12541 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12541 : ℝ) = 12541 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12541 : ℝ) + √12541 + gaussMomConst 80 ≤ 12662 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12541 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12541 : ℝ)) ≤ (112767209 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12541 4 +
      2 / (mA 12541 : ℝ) * frobEnvelopeSquared160 12541 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12541 4 +
      2 / (mA 12541 : ℝ) * frobEnvelopeSquared160 12541) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12541 : ℝ)) *
      operatorEnvelope160 12541 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12541 4 +
      2 / (mA 12541 : ℝ) * frobEnvelopeSquared160 12541) +
      transverseConstant160 * √(2 / (mA 12541 : ℝ)) * operatorEnvelope160 12541 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12541 4 +
      2 / (mA 12541 : ℝ) * frobEnvelopeSquared160 12541) +
      transverseConstant160 * √(2 / (mA 12541 : ℝ)) * operatorEnvelope160 12541 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12541 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12541 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12541 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12541 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12541

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12541
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12541) :=
  agentEv (paperDesignP 12541) (Energy32 12541) ∩
  agentEv (paperDesignP 12541) (freshRetainedEvent160 12541 4) ∩
  agentEv (paperDesignP 12541) (FirstMatrix 12541) ∩
  BstLean.Part164.Eop2 12541 ∩ outputCentreEvent (paperCentres 12541)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12541)).real
      (agentEv (paperDesignP 12541) (FirstMatrix 12541))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12541)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12541 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12541)).real (BstLean.Part164.Eop2 12541)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12541)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12541)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12541) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12541) hτ
  have hL := fresh_retained_charge160 (n := 12541) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12541) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12541 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12541) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12541 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12541) (hw : WINDOW (paperDesignP 12541) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12541))
    (hW : ∫ a in K, ((12541 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12541 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12541 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12541 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12541) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12541 : ℝ)) * eR c * 12541 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12541

/-! Exact rational parameters for the dimension-12542 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12542
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
noncomputable def biasRootCap : ℝ := (588929 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12542 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12542 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12542 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12542.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12542] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12542 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12542 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12542.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12542

namespace BstLean.Part266.Row12542
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

theorem energy_allowance_row : energyAllowance 12542 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12542 : ℝ)) ≤ ((56379109 / 500000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12542 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12542)
  change 0 ≤ agentLayerAllowance 12542 at ha0
  have he : energyWeightAllowance 12542 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12542)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12542)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12542).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12542).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12542)) :
    ∫ a in K, fbR c a ^ k ∂muI 12542 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12542])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12542

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12542
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12542 / 12542 ≤ chi := by
  have hs : √((12542 : ℝ) * 12) ≤ (387948451 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12542}
    (hc : c ∈ outputCentreEvent (paperCentres 12542)) :
    normSq c.2.1.2 ≤ (2 / (12542 : ℝ)) * eR c * 12542 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12542 : ℝ) * normSq (bR c) * chiUp 12542 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12542)).real (outputCentreEvent (paperCentres 12542))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12542

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12542
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12542) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12542) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12542)]
  norm_num [varianceMax]

end BstLean.Part266.Row12542

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12542
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12542) (hc : A1 c ∈ Eop 12542) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12542 : ℝ)) ≤ (12627913537 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12542 : ℝ) ≤ (3499721 / 31250) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12542 : ℝ) + 2 * √12542 ≤ (199468471 / 15625) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12542) (hc : c ∈ BstLean.Part164.Eop2 12542) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12542 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12542) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12542 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12542) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12542).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12542) (FirstMatrix 12542))
    (h2 : c ∈ BstLean.Part164.Eop2 12542) (a : BstLean.Part161.Ix 12542) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12542

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12542
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12542) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12542) c ∈ BstLean.Part212.latitudeEvent 12542
      (ENNReal.ofReal (C / 12542))) (K : Set (Ix 12542)) :
    ∫ a in K, ((12542 : ℝ) * VR c a) ^ 2 ∂muI 12542 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12542

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12542
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12542 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12542 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12542 - 1 - 1) 80 ≤ (12698 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12542 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12698 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12542) ≤ (78 * 10 ^ 6 * ((12542 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12542 : ℝ) / 2 + 160) ≤ (8868542271 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12542 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12542 : ℝ) ^ 2 / 2 + 320 = 157302404 / 2 by norm_num,
    show (12542 : ℝ) ^ 2 / 2 + 160 = 157302084 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12542 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12542 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12542 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12542 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12542)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12542) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12542 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12542)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12542 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12542 ≤ (162 : ℝ) := by
  have hs : √(2 / (12542 : ℝ)) ≤ (12627913537 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12542 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12542 : ℝ) = 12542 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12542 : ℝ) + √12542 + gaussMomConst 80 ≤ 12663 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12542 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12542 : ℝ)) ≤ (56379109 / 500000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12542 4 +
      2 / (mA 12542 : ℝ) * frobEnvelopeSquared160 12542 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12542 4 +
      2 / (mA 12542 : ℝ) * frobEnvelopeSquared160 12542) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12542 : ℝ)) *
      operatorEnvelope160 12542 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12542 4 +
      2 / (mA 12542 : ℝ) * frobEnvelopeSquared160 12542) +
      transverseConstant160 * √(2 / (mA 12542 : ℝ)) * operatorEnvelope160 12542 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12542 4 +
      2 / (mA 12542 : ℝ) * frobEnvelopeSquared160 12542) +
      transverseConstant160 * √(2 / (mA 12542 : ℝ)) * operatorEnvelope160 12542 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12542 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12542 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12542 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12542 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12542

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12542
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12542) :=
  agentEv (paperDesignP 12542) (Energy32 12542) ∩
  agentEv (paperDesignP 12542) (freshRetainedEvent160 12542 4) ∩
  agentEv (paperDesignP 12542) (FirstMatrix 12542) ∩
  BstLean.Part164.Eop2 12542 ∩ outputCentreEvent (paperCentres 12542)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12542)).real
      (agentEv (paperDesignP 12542) (FirstMatrix 12542))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12542)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12542 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12542)).real (BstLean.Part164.Eop2 12542)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12542)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12542)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12542) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12542) hτ
  have hL := fresh_retained_charge160 (n := 12542) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12542) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12542 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12542) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12542 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12542) (hw : WINDOW (paperDesignP 12542) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12542))
    (hW : ∫ a in K, ((12542 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12542 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12542 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12542 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12542) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12542 : ℝ)) * eR c * 12542 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12542

/-! Exact rational parameters for the dimension-12543 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12543
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
noncomputable def biasRootCap : ℝ := (117781 / 20000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12543 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12543 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12543 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12543.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12543] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12543 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12543 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12543.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12543

namespace BstLean.Part266.Row12543
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

theorem energy_allowance_row : energyAllowance 12543 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12543 : ℝ)) ≤ ((28187307 / 250000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12543 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12543)
  change 0 ≤ agentLayerAllowance 12543 at ha0
  have he : energyWeightAllowance 12543 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12543)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12543)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12543).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12543).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12543)) :
    ∫ a in K, fbR c a ^ k ∂muI 12543 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12543])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12543

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12543
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12543 / 12543 ≤ chi := by
  have hs : √((12543 : ℝ) * 12) ≤ (96990979 / 250000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12543}
    (hc : c ∈ outputCentreEvent (paperCentres 12543)) :
    normSq c.2.1.2 ≤ (2 / (12543 : ℝ)) * eR c * 12543 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12543 : ℝ) * normSq (bR c) * chiUp 12543 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12543)).real (outputCentreEvent (paperCentres 12543))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12543

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12543
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12543) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12543) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12543)]
  norm_num [varianceMax]

end BstLean.Part266.Row12543

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12543
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12543) (hc : A1 c ∈ Eop 12543) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12543 : ℝ)) ≤ (6313705071 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12543 : ℝ) ≤ (6999721 / 62500) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12543 : ℝ) + 2 * √12543 ≤ (398968471 / 31250) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12543) (hc : c ∈ BstLean.Part164.Eop2 12543) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12543 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12543) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12543 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12543) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12543).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12543) (FirstMatrix 12543))
    (h2 : c ∈ BstLean.Part164.Eop2 12543) (a : BstLean.Part161.Ix 12543) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12543

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12543
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12543) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12543) c ∈ BstLean.Part212.latitudeEvent 12543
      (ENNReal.ofReal (C / 12543))) (K : Set (Ix 12543)) :
    ∫ a in K, ((12543 : ℝ) * VR c a) ^ 2 ∂muI 12543 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12543

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12543
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12543 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12543 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12543 - 1 - 1) 80 ≤ (12699 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12543 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12699 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12543) ≤ (78 * 10 ^ 6 * ((12543 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12543 : ℝ) / 2 + 160) ≤ (8869249377 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12543 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12543 : ℝ) ^ 2 / 2 + 320 = 157327489 / 2 by norm_num,
    show (12543 : ℝ) ^ 2 / 2 + 160 = 157327169 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12543 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12543 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12543 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12543 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12543)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12543) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12543 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12543)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12543 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12543 ≤ (162 : ℝ) := by
  have hs : √(2 / (12543 : ℝ)) ≤ (6313705071 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12543 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12543 : ℝ) = 12543 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12543 : ℝ) + √12543 + gaussMomConst 80 ≤ 12664 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12543 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12543 : ℝ)) ≤ (28187307 / 250000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12543 4 +
      2 / (mA 12543 : ℝ) * frobEnvelopeSquared160 12543 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12543 4 +
      2 / (mA 12543 : ℝ) * frobEnvelopeSquared160 12543) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12543 : ℝ)) *
      operatorEnvelope160 12543 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12543 4 +
      2 / (mA 12543 : ℝ) * frobEnvelopeSquared160 12543) +
      transverseConstant160 * √(2 / (mA 12543 : ℝ)) * operatorEnvelope160 12543 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12543 4 +
      2 / (mA 12543 : ℝ) * frobEnvelopeSquared160 12543) +
      transverseConstant160 * √(2 / (mA 12543 : ℝ)) * operatorEnvelope160 12543 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12543 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12543 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12543 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12543 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12543

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12543
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12543) :=
  agentEv (paperDesignP 12543) (Energy32 12543) ∩
  agentEv (paperDesignP 12543) (freshRetainedEvent160 12543 4) ∩
  agentEv (paperDesignP 12543) (FirstMatrix 12543) ∩
  BstLean.Part164.Eop2 12543 ∩ outputCentreEvent (paperCentres 12543)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12543)).real
      (agentEv (paperDesignP 12543) (FirstMatrix 12543))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12543)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12543 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12543)).real (BstLean.Part164.Eop2 12543)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12543)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12543)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12543) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12543) hτ
  have hL := fresh_retained_charge160 (n := 12543) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12543) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12543 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12543) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12543 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12543) (hw : WINDOW (paperDesignP 12543) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12543))
    (hW : ∫ a in K, ((12543 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12543 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12543 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12543 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12543) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12543 : ℝ)) * eR c * 12543 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12543

/-! Exact rational parameters for the dimension-12544 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12544
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
noncomputable def biasRootCap : ℝ := (294441 / 50000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12544 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12544 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12544 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12544.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12544] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12544 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12544 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12544.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12544

namespace BstLean.Part266.Row12544
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

theorem energy_allowance_row : energyAllowance 12544 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12544 : ℝ)) ≤ ((1409253 / 12500000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12544 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12544)
  change 0 ≤ agentLayerAllowance 12544 at ha0
  have he : energyWeightAllowance 12544 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12544)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12544)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12544).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12544).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12544)) :
    ∫ a in K, fbR c a ^ k ∂muI 12544 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12544])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12544

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12544
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12544 / 12544 ≤ chi := by
  have hs : √((12544 : ℝ) * 12) ≤ (387979381 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12544}
    (hc : c ∈ outputCentreEvent (paperCentres 12544)) :
    normSq c.2.1.2 ≤ (2 / (12544 : ℝ)) * eR c * 12544 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12544 : ℝ) * normSq (bR c) * chiUp 12544 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12544)).real (outputCentreEvent (paperCentres 12544))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12544

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12544
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12544) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12544) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  norm_num [varianceMax]

end BstLean.Part266.Row12544

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12544
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12544) (hc : A1 c ∈ Eop 12544) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12544 : ℝ)) ≤ (12626906807 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12544 : ℝ) ≤ (112000001 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12544 : ℝ) + 2 * √12544 ≤ (6384000001 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12544) (hc : c ∈ BstLean.Part164.Eop2 12544) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12544 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12544) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12544 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12544) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12544).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12544) (FirstMatrix 12544))
    (h2 : c ∈ BstLean.Part164.Eop2 12544) (a : BstLean.Part161.Ix 12544) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12544

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12544
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12544) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12544) c ∈ BstLean.Part212.latitudeEvent 12544
      (ENNReal.ofReal (C / 12544))) (K : Set (Ix 12544)) :
    ∫ a in K, ((12544 : ℝ) * VR c a) ^ 2 ∂muI 12544 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12544

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12544
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12544 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12544 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12544 - 1 - 1) 80 ≤ (12700 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12544 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12700 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12544) ≤ (78 * 10 ^ 6 * ((12544 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12544 : ℝ) / 2 + 160) ≤ (8869956483 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12544 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12544 : ℝ) ^ 2 / 2 + 320 = 157352576 / 2 by norm_num,
    show (12544 : ℝ) ^ 2 / 2 + 160 = 157352256 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12544 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12544 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12544 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12544 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12544)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12544) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12544 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12544)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12544 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12544 ≤ (162 : ℝ) := by
  have hs : √(2 / (12544 : ℝ)) ≤ (12626906807 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12544 : ℝ) ≤ 113 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12544 : ℝ) = 12544 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12544 : ℝ) + √12544 + gaussMomConst 80 ≤ 12666 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12544 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12544 : ℝ)) ≤ (1409253 / 12500000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12544 4 +
      2 / (mA 12544 : ℝ) * frobEnvelopeSquared160 12544 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12544 4 +
      2 / (mA 12544 : ℝ) * frobEnvelopeSquared160 12544) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12544 : ℝ)) *
      operatorEnvelope160 12544 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12544 4 +
      2 / (mA 12544 : ℝ) * frobEnvelopeSquared160 12544) +
      transverseConstant160 * √(2 / (mA 12544 : ℝ)) * operatorEnvelope160 12544 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12544 4 +
      2 / (mA 12544 : ℝ) * frobEnvelopeSquared160 12544) +
      transverseConstant160 * √(2 / (mA 12544 : ℝ)) * operatorEnvelope160 12544 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12544 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12544 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12544 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12544 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12544

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12544
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12544) :=
  agentEv (paperDesignP 12544) (Energy32 12544) ∩
  agentEv (paperDesignP 12544) (freshRetainedEvent160 12544 4) ∩
  agentEv (paperDesignP 12544) (FirstMatrix 12544) ∩
  BstLean.Part164.Eop2 12544 ∩ outputCentreEvent (paperCentres 12544)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12544)).real
      (agentEv (paperDesignP 12544) (FirstMatrix 12544))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12544)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12544 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12544)).real (BstLean.Part164.Eop2 12544)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12544)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12544)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12544) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12544) hτ
  have hL := fresh_retained_charge160 (n := 12544) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12544) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12544 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12544) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12544 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12544) (hw : WINDOW (paperDesignP 12544) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12544))
    (hW : ∫ a in K, ((12544 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12544 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12544 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12544 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12544) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12544 : ℝ)) * eR c * 12544 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12544

/-! Exact rational parameters for the dimension-12545 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12545
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
noncomputable def biasRootCap : ℝ := (294429 / 50000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12545 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12545 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12545 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12545.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12545] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12545 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12545 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12545.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12545

namespace BstLean.Part266.Row12545
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

theorem energy_allowance_row : energyAllowance 12545 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12545 : ℝ)) ≤ ((112731253 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12545 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12545)
  change 0 ≤ agentLayerAllowance 12545 at ha0
  have he : energyWeightAllowance 12545 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12545)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12545)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12545).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12545).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12545)) :
    ∫ a in K, fbR c a ^ k ∂muI 12545 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12545])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12545

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12545
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12545 / 12545 ≤ chi := by
  have hs : √((12545 : ℝ) * 12) ≤ (193997423 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12545}
    (hc : c ∈ outputCentreEvent (paperCentres 12545)) :
    normSq c.2.1.2 ≤ (2 / (12545 : ℝ)) * eR c * 12545 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12545 : ℝ) * normSq (bR c) * chiUp 12545 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12545)).real (outputCentreEvent (paperCentres 12545))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12545

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12545
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12545) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12545) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12545)]
  norm_num [varianceMax]

end BstLean.Part266.Row12545

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12545
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12545) (hc : A1 c ∈ Eop 12545) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12545 : ℝ)) ≤ (12626403533 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12545 : ℝ) ≤ (22400893 / 200000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12545 : ℝ) + 2 * √12545 ≤ (1276900893 / 100000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12545) (hc : c ∈ BstLean.Part164.Eop2 12545) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12545 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12545) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12545 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12545) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12545).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12545) (FirstMatrix 12545))
    (h2 : c ∈ BstLean.Part164.Eop2 12545) (a : BstLean.Part161.Ix 12545) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12545

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12545
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12545) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12545) c ∈ BstLean.Part212.latitudeEvent 12545
      (ENNReal.ofReal (C / 12545))) (K : Set (Ix 12545)) :
    ∫ a in K, ((12545 : ℝ) * VR c a) ^ 2 ∂muI 12545 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12545

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12545
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12545 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12545 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12545 - 1 - 1) 80 ≤ (12701 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12545 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12701 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12545) ≤ (78 * 10 ^ 6 * ((12545 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12545 : ℝ) / 2 + 160) ≤ (8870663589 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12545 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12545 : ℝ) ^ 2 / 2 + 320 = 157377665 / 2 by norm_num,
    show (12545 : ℝ) ^ 2 / 2 + 160 = 157377345 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12545 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12545 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12545 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12545 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12545)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12545) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12545 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12545)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12545 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12545 ≤ (162 : ℝ) := by
  have hs : √(2 / (12545 : ℝ)) ≤ (12626403533 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12545 : ℝ) ≤ 113 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12545 : ℝ) = 12545 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12545 : ℝ) + √12545 + gaussMomConst 80 ≤ 12667 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12545 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12545 : ℝ)) ≤ (112731253 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12545 4 +
      2 / (mA 12545 : ℝ) * frobEnvelopeSquared160 12545 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12545 4 +
      2 / (mA 12545 : ℝ) * frobEnvelopeSquared160 12545) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12545 : ℝ)) *
      operatorEnvelope160 12545 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12545 4 +
      2 / (mA 12545 : ℝ) * frobEnvelopeSquared160 12545) +
      transverseConstant160 * √(2 / (mA 12545 : ℝ)) * operatorEnvelope160 12545 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12545 4 +
      2 / (mA 12545 : ℝ) * frobEnvelopeSquared160 12545) +
      transverseConstant160 * √(2 / (mA 12545 : ℝ)) * operatorEnvelope160 12545 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12545 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12545 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12545 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12545 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12545

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12545
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12545) :=
  agentEv (paperDesignP 12545) (Energy32 12545) ∩
  agentEv (paperDesignP 12545) (freshRetainedEvent160 12545 4) ∩
  agentEv (paperDesignP 12545) (FirstMatrix 12545) ∩
  BstLean.Part164.Eop2 12545 ∩ outputCentreEvent (paperCentres 12545)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12545)).real
      (agentEv (paperDesignP 12545) (FirstMatrix 12545))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12545)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12545 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12545)).real (BstLean.Part164.Eop2 12545)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12545)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12545)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12545) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12545) hτ
  have hL := fresh_retained_charge160 (n := 12545) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12545) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12545 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12545) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12545 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12545) (hw : WINDOW (paperDesignP 12545) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12545))
    (hW : ∫ a in K, ((12545 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12545 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12545 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12545 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12545) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12545 : ℝ)) * eR c * 12545 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12545

/-! Exact rational parameters for the dimension-12546 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12546
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
noncomputable def biasRootCap : ℝ := (117767 / 20000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12546 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12546 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12546 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12546.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12546] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12546 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12546 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12546.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12546

namespace BstLean.Part266.Row12546
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

theorem energy_allowance_row : energyAllowance 12546 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12546 : ℝ)) ≤ ((28180567 / 250000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12546 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12546)
  change 0 ≤ agentLayerAllowance 12546 at ha0
  have he : energyWeightAllowance 12546 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12546)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12546)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12546).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12546).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12546)) :
    ∫ a in K, fbR c a ^ k ∂muI 12546 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12546])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12546

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12546
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12546 / 12546 ≤ chi := by
  have hs : √((12546 : ℝ) * 12) ≤ (38801031 / 100000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12546}
    (hc : c ∈ outputCentreEvent (paperCentres 12546)) :
    normSq c.2.1.2 ≤ (2 / (12546 : ℝ)) * eR c * 12546 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12546 : ℝ) * normSq (bR c) * chiUp 12546 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12546)).real (outputCentreEvent (paperCentres 12546))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12546

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12546
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12546) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12546) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12546)]
  norm_num [varianceMax]

end BstLean.Part266.Row12546

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12546
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12546) (hc : A1 c ∈ Eop 12546) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12546 : ℝ)) ≤ (6312950159 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12546 : ℝ) ≤ (112008929 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12546 : ℝ) + 2 * √12546 ≤ (6385008929 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12546) (hc : c ∈ BstLean.Part164.Eop2 12546) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12546 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12546) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12546 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12546) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12546).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12546) (FirstMatrix 12546))
    (h2 : c ∈ BstLean.Part164.Eop2 12546) (a : BstLean.Part161.Ix 12546) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12546

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12546
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12546) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12546) c ∈ BstLean.Part212.latitudeEvent 12546
      (ENNReal.ofReal (C / 12546))) (K : Set (Ix 12546)) :
    ∫ a in K, ((12546 : ℝ) * VR c a) ^ 2 ∂muI 12546 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12546

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12546
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12546 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12546 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12546 - 1 - 1) 80 ≤ (12702 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12546 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12702 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12546) ≤ (78 * 10 ^ 6 * ((12546 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12546 : ℝ) / 2 + 160) ≤ (1774274139 / 200000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12546 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12546 : ℝ) ^ 2 / 2 + 320 = 157402756 / 2 by norm_num,
    show (12546 : ℝ) ^ 2 / 2 + 160 = 157402436 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12546 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12546 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12546 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12546 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12546)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12546) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12546 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12546)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12546 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12546 ≤ (162 : ℝ) := by
  have hs : √(2 / (12546 : ℝ)) ≤ (6312950159 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12546 : ℝ) ≤ 113 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12546 : ℝ) = 12546 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12546 : ℝ) + √12546 + gaussMomConst 80 ≤ 12668 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12546 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12546 : ℝ)) ≤ (28180567 / 250000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12546 4 +
      2 / (mA 12546 : ℝ) * frobEnvelopeSquared160 12546 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12546 4 +
      2 / (mA 12546 : ℝ) * frobEnvelopeSquared160 12546) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12546 : ℝ)) *
      operatorEnvelope160 12546 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12546 4 +
      2 / (mA 12546 : ℝ) * frobEnvelopeSquared160 12546) +
      transverseConstant160 * √(2 / (mA 12546 : ℝ)) * operatorEnvelope160 12546 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12546 4 +
      2 / (mA 12546 : ℝ) * frobEnvelopeSquared160 12546) +
      transverseConstant160 * √(2 / (mA 12546 : ℝ)) * operatorEnvelope160 12546 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12546 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12546 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12546 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12546 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12546

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12546
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12546) :=
  agentEv (paperDesignP 12546) (Energy32 12546) ∩
  agentEv (paperDesignP 12546) (freshRetainedEvent160 12546 4) ∩
  agentEv (paperDesignP 12546) (FirstMatrix 12546) ∩
  BstLean.Part164.Eop2 12546 ∩ outputCentreEvent (paperCentres 12546)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12546)).real
      (agentEv (paperDesignP 12546) (FirstMatrix 12546))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12546)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12546 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12546)).real (BstLean.Part164.Eop2 12546)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12546)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12546)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12546) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12546) hτ
  have hL := fresh_retained_charge160 (n := 12546) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12546) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12546 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12546) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12546 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12546) (hw : WINDOW (paperDesignP 12546) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12546))
    (hW : ∫ a in K, ((12546 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12546 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12546 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12546 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12546) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12546 : ℝ)) * eR c * 12546 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12546

/-! Exact rational parameters for the dimension-12547 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12547
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
noncomputable def biasRootCap : ℝ := (147203 / 25000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12547 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12547 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12547 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12547.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12547] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12547 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12547 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12547.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12547

namespace BstLean.Part266.Row12547
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

theorem energy_allowance_row : energyAllowance 12547 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12547 : ℝ)) ≤ ((28178321 / 250000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12547 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12547)
  change 0 ≤ agentLayerAllowance 12547 at ha0
  have he : energyWeightAllowance 12547 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12547)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12547)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12547).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12547).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12547)) :
    ∫ a in K, fbR c a ^ k ∂muI 12547 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12547])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12547

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12547
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12547 / 12547 ≤ chi := by
  have hs : √((12547 : ℝ) * 12) ≤ (388025773 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12547}
    (hc : c ∈ outputCentreEvent (paperCentres 12547)) :
    normSq c.2.1.2 ≤ (2 / (12547 : ℝ)) * eR c * 12547 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12547 : ℝ) * normSq (bR c) * chiUp 12547 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12547)).real (outputCentreEvent (paperCentres 12547))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12547

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12547
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12547) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12547) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12547)]
  norm_num [varianceMax]

end BstLean.Part266.Row12547

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12547
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12547) (hc : A1 c ∈ Eop 12547) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12547 : ℝ)) ≤ (3156349291 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12547 : ℝ) ≤ (112013393 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12547 : ℝ) + 2 * √12547 ≤ (6385513393 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12547) (hc : c ∈ BstLean.Part164.Eop2 12547) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12547 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12547) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12547 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12547) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12547).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12547) (FirstMatrix 12547))
    (h2 : c ∈ BstLean.Part164.Eop2 12547) (a : BstLean.Part161.Ix 12547) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12547

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12547
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12547) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12547) c ∈ BstLean.Part212.latitudeEvent 12547
      (ENNReal.ofReal (C / 12547))) (K : Set (Ix 12547)) :
    ∫ a in K, ((12547 : ℝ) * VR c a) ^ 2 ∂muI 12547 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12547

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12547
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12547 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12547 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12547 - 1 - 1) 80 ≤ (12703 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12547 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12703 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12547) ≤ (78 * 10 ^ 6 * ((12547 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12547 : ℝ) / 2 + 160) ≤ (8872077801 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12547 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12547 : ℝ) ^ 2 / 2 + 320 = 157427849 / 2 by norm_num,
    show (12547 : ℝ) ^ 2 / 2 + 160 = 157427529 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12547 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12547 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12547 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12547 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12547)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12547) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12547 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12547)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12547 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12547 ≤ (162 : ℝ) := by
  have hs : √(2 / (12547 : ℝ)) ≤ (3156349291 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12547 : ℝ) ≤ 113 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12547 : ℝ) = 12547 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12547 : ℝ) + √12547 + gaussMomConst 80 ≤ 12669 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12547 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12547 : ℝ)) ≤ (28178321 / 250000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12547 4 +
      2 / (mA 12547 : ℝ) * frobEnvelopeSquared160 12547 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12547 4 +
      2 / (mA 12547 : ℝ) * frobEnvelopeSquared160 12547) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12547 : ℝ)) *
      operatorEnvelope160 12547 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12547 4 +
      2 / (mA 12547 : ℝ) * frobEnvelopeSquared160 12547) +
      transverseConstant160 * √(2 / (mA 12547 : ℝ)) * operatorEnvelope160 12547 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12547 4 +
      2 / (mA 12547 : ℝ) * frobEnvelopeSquared160 12547) +
      transverseConstant160 * √(2 / (mA 12547 : ℝ)) * operatorEnvelope160 12547 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12547 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12547 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12547 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12547 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12547

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12547
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12547) :=
  agentEv (paperDesignP 12547) (Energy32 12547) ∩
  agentEv (paperDesignP 12547) (freshRetainedEvent160 12547 4) ∩
  agentEv (paperDesignP 12547) (FirstMatrix 12547) ∩
  BstLean.Part164.Eop2 12547 ∩ outputCentreEvent (paperCentres 12547)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12547)).real
      (agentEv (paperDesignP 12547) (FirstMatrix 12547))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12547)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12547 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12547)).real (BstLean.Part164.Eop2 12547)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12547)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12547)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12547) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12547) hτ
  have hL := fresh_retained_charge160 (n := 12547) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12547) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12547 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12547) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12547 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12547) (hw : WINDOW (paperDesignP 12547) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12547))
    (hW : ∫ a in K, ((12547 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12547 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12547 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12547 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12547) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12547 : ℝ)) * eR c * 12547 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12547

/-! Exact rational parameters for the dimension-12548 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12548
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
noncomputable def biasRootCap : ℝ := (147197 / 25000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12548 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12548 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12548 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12548.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12548] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12548 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12548 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12548.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12548

namespace BstLean.Part266.Row12548
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

theorem energy_allowance_row : energyAllowance 12548 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12548 : ℝ)) ≤ ((112704301 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12548 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12548)
  change 0 ≤ agentLayerAllowance 12548 at ha0
  have he : energyWeightAllowance 12548 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12548)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12548)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12548).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12548).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12548)) :
    ∫ a in K, fbR c a ^ k ∂muI 12548 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12548])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12548

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12548
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12548 / 12548 ≤ chi := by
  have hs : √((12548 : ℝ) * 12) ≤ (77608247 / 200000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12548}
    (hc : c ∈ outputCentreEvent (paperCentres 12548)) :
    normSq c.2.1.2 ≤ (2 / (12548 : ℝ)) * eR c * 12548 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12548 : ℝ) * normSq (bR c) * chiUp 12548 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12548)).real (outputCentreEvent (paperCentres 12548))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12548

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12548
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12548) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12548) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12548)]
  norm_num [varianceMax]

end BstLean.Part266.Row12548

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12548
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12548) (hc : A1 c ∈ Eop 12548) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12548 : ℝ)) ≤ (1262489407 / 100000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12548 : ℝ) ≤ (1750279 / 15625) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12548 : ℝ) + 2 * √12548 ≤ (199563058 / 15625) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12548) (hc : c ∈ BstLean.Part164.Eop2 12548) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12548 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12548) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12548 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12548) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12548).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12548) (FirstMatrix 12548))
    (h2 : c ∈ BstLean.Part164.Eop2 12548) (a : BstLean.Part161.Ix 12548) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12548

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12548
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12548) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12548) c ∈ BstLean.Part212.latitudeEvent 12548
      (ENNReal.ofReal (C / 12548))) (K : Set (Ix 12548)) :
    ∫ a in K, ((12548 : ℝ) * VR c a) ^ 2 ∂muI 12548 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12548

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12548
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12548 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12548 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12548 - 1 - 1) 80 ≤ (12704 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12548 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12704 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12548) ≤ (78 * 10 ^ 6 * ((12548 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12548 : ℝ) / 2 + 160) ≤ (8872784907 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12548 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12548 : ℝ) ^ 2 / 2 + 320 = 157452944 / 2 by norm_num,
    show (12548 : ℝ) ^ 2 / 2 + 160 = 157452624 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12548 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12548 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12548 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12548 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12548)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12548) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12548 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12548)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12548 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12548 ≤ (162 : ℝ) := by
  have hs : √(2 / (12548 : ℝ)) ≤ (1262489407 / 100000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12548 : ℝ) ≤ 113 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12548 : ℝ) = 12548 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12548 : ℝ) + √12548 + gaussMomConst 80 ≤ 12670 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12548 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12548 : ℝ)) ≤ (112704301 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12548 4 +
      2 / (mA 12548 : ℝ) * frobEnvelopeSquared160 12548 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12548 4 +
      2 / (mA 12548 : ℝ) * frobEnvelopeSquared160 12548) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12548 : ℝ)) *
      operatorEnvelope160 12548 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12548 4 +
      2 / (mA 12548 : ℝ) * frobEnvelopeSquared160 12548) +
      transverseConstant160 * √(2 / (mA 12548 : ℝ)) * operatorEnvelope160 12548 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12548 4 +
      2 / (mA 12548 : ℝ) * frobEnvelopeSquared160 12548) +
      transverseConstant160 * √(2 / (mA 12548 : ℝ)) * operatorEnvelope160 12548 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12548 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12548 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12548 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12548 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12548

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12548
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12548) :=
  agentEv (paperDesignP 12548) (Energy32 12548) ∩
  agentEv (paperDesignP 12548) (freshRetainedEvent160 12548 4) ∩
  agentEv (paperDesignP 12548) (FirstMatrix 12548) ∩
  BstLean.Part164.Eop2 12548 ∩ outputCentreEvent (paperCentres 12548)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12548)).real
      (agentEv (paperDesignP 12548) (FirstMatrix 12548))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12548)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12548 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12548)).real (BstLean.Part164.Eop2 12548)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12548)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12548)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12548) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12548) hτ
  have hL := fresh_retained_charge160 (n := 12548) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12548) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12548 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12548) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12548 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12548) (hw : WINDOW (paperDesignP 12548) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12548))
    (hW : ∫ a in K, ((12548 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12548 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12548 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12548 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12548) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12548 : ℝ)) * eR c * 12548 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12548

/-! Exact rational parameters for the dimension-12549 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row12549
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
noncomputable def biasRootCap : ℝ := (117753 / 20000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12549 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12549 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12549 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent12549.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent12549] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12549 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12549 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent12549.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row12549

namespace BstLean.Part266.Row12549
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

theorem energy_allowance_row : energyAllowance 12549 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12549 : ℝ)) ≤ ((2817383 / 25000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12549 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12549)
  change 0 ≤ agentLayerAllowance 12549 at ha0
  have he : energyWeightAllowance 12549 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12549)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12549)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12549).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12549).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12549)) :
    ∫ a in K, fbR c a ^ k ∂muI 12549 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12549])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row12549

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row12549
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

theorem chi_row : chiUp 12549 / 12549 ≤ chi := by
  have hs : √((12549 : ℝ) * 12) ≤ (388056697 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 12549}
    (hc : c ∈ outputCentreEvent (paperCentres 12549)) :
    normSq c.2.1.2 ≤ (2 / (12549 : ℝ)) * eR c * 12549 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12549 : ℝ) * normSq (bR c) * chiUp 12549 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem outputCentre_charge_row :
    (retDist (paperCentres 12549)).real (outputCentreEvent (paperCentres 12549))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row12549

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row12549
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise_row (c : Ret 12549) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 162) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12549) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12549)]
  norm_num [varianceMax]

end BstLean.Part266.Row12549

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row12549
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

theorem first_matrix_row (c : Ret 12549) (hc : A1 c ∈ Eop 12549) : OpB (A1 c) 162 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12549 : ℝ)) ≤ (3156097759 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12549 : ℝ) ≤ (1400279 / 12500) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12549 : ℝ) + 2 * √12549 ≤ (79831529 / 6250) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12549) (hc : c ∈ BstLean.Part164.Eop2 12549) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12549 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12549) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12549 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12549) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12549).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12549) (FirstMatrix 12549))
    (h2 : c ∈ BstLean.Part164.Eop2 12549) (a : BstLean.Part161.Ix 12549) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row12549

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row12549
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_moment_row (c : Ret 12549) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12549) c ∈ BstLean.Part212.latitudeEvent 12549
      (ENNReal.ofReal (C / 12549))) (K : Set (Ix 12549)) :
    ∫ a in K, ((12549 : ℝ) * VR c a) ^ 2 ∂muI 12549 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row12549

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row12549
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem exact_radius_sq_row : exactRadius (12549 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12549 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12549 - 1 - 1) 80 ≤ (12705 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12549 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12705 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12549) ≤ (78 * 10 ^ 6 * ((12549 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12549 : ℝ) / 2 + 160) ≤ (8873492013 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12549 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12549 : ℝ) ^ 2 / 2 + 320 = 157478041 / 2 by norm_num,
    show (12549 : ℝ) ^ 2 / 2 + 160 = 157477721 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12549 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12549 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12549 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12549 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12549)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12549) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12549 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12549)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12549 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12549 ≤ (162 : ℝ) := by
  have hs : √(2 / (12549 : ℝ)) ≤ (3156097759 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12549 : ℝ) ≤ 113 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12549 : ℝ) = 12549 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12549 : ℝ) + √12549 + gaussMomConst 80 ≤ 12671 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12549 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12549 : ℝ)) ≤ (2817383 / 25000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12549 4 +
      2 / (mA 12549 : ℝ) * frobEnvelopeSquared160 12549 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12549 4 +
      2 / (mA 12549 : ℝ) * frobEnvelopeSquared160 12549) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12549 : ℝ)) *
      operatorEnvelope160 12549 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12549 4 +
      2 / (mA 12549 : ℝ) * frobEnvelopeSquared160 12549) +
      transverseConstant160 * √(2 / (mA 12549 : ℝ)) * operatorEnvelope160 12549 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12549 4 +
      2 / (mA 12549 : ℝ) * frobEnvelopeSquared160 12549) +
      transverseConstant160 * √(2 / (mA 12549 : ℝ)) * operatorEnvelope160 12549 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12549 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12549 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12549 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12549 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row12549

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row12549
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12549) :=
  agentEv (paperDesignP 12549) (Energy32 12549) ∩
  agentEv (paperDesignP 12549) (freshRetainedEvent160 12549 4) ∩
  agentEv (paperDesignP 12549) (FirstMatrix 12549) ∩
  BstLean.Part164.Eop2 12549 ∩ outputCentreEvent (paperCentres 12549)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12549)).real
      (agentEv (paperDesignP 12549) (FirstMatrix 12549))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12549)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12549 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12549)).real (BstLean.Part164.Eop2 12549)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12549)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12549)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12549) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12549) hτ
  have hL := fresh_retained_charge160 (n := 12549) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12549) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12549 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12549) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12549 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12549) (hw : WINDOW (paperDesignP 12549) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12549))
    (hW : ∫ a in K, ((12549 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12549 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12549 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12549 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12549) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12549 : ℝ)) * eR c * 12549 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row12549
