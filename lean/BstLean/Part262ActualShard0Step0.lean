import BstLean.Part252All
import BstLean.Part262ActualInterface
import BstLean.Part259Data0
import BstLean.Part259Data1
import BstLean.Part259Data2
import BstLean.Part259Data3
import BstLean.Part259Data4

import BstLean.Part262Actual12226

/-! Exact rational parameters for the dimension-12225 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12225 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12225 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12225 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12225.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12225] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12225 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12225 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12225.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12225

namespace BstLean.Part262.Row12225
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

theorem energy_allowance_row : energyAllowance 12225 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12225 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12225 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12225)
  change 0 ≤ agentLayerAllowance 12225 at ha0
  have he : energyWeightAllowance 12225 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12225)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12225)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12225).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12225).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12225)) :
    ∫ a in K, fbR c a ^ k ∂muI 12225 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12225])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12225

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12225 / 12225 ≤ chi := by
  have hs : √((12225 : ℝ) * 12) ≤ (383014361 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12225}
    (hc : c ∈ outputCentreEvent (paperCentres 12225)) :
    normSq c.2.1.2 ≤ (2 / (12225 : ℝ)) * eR c * 12225 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12225 : ℝ) * normSq (bR c) * chiUp 12225 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12225)).real (outputCentreEvent (paperCentres 12225))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12225

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12225) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12225) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12225)]
  norm_num [varianceMax]

end BstLean.Part262.Row12225

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12225) (hc : A1 c ∈ Eop 12225) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12225 : ℝ)) ≤ (3197647397 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12225 : ℝ) ≤ (55283361 / 500000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12225 : ℝ) + 2 * √12225 ≤ (3111533361 / 250000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12225) (hc : c ∈ BstLean.Part164.Eop2 12225) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12225 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12225) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12225 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12225) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12225).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12225) (FirstMatrix 12225))
    (h2 : c ∈ BstLean.Part164.Eop2 12225) (a : BstLean.Part161.Ix 12225) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12225

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
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

end BstLean.Part262.Row12225

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12225 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12225 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12225 - 1 - 1) 80 ≤ (12381 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12225 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12381 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12225) ≤ (78 * 10 ^ 6 * ((12225 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12225 : ℝ) / 2 + 160) ≤ (1728877931 / 200000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12225 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12225 : ℝ) ^ 2 / 2 + 320 = 149451265 / 2 by norm_num,
    show (12225 : ℝ) ^ 2 / 2 + 160 = 149450945 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12225 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12225 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12225 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12225 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12225)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12225) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12225 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12225)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12225 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12225 ≤ (160 : ℝ) := by
  have hs : √(2 / (12225 : ℝ)) ≤ (3197647397 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12225 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12225 : ℝ) = 12225 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12225 : ℝ) + √12225 + gaussMomConst 80 ≤ 12345 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12225 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12225 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12225 4 +
      2 / (mA 12225 : ℝ) * frobEnvelopeSquared160 12225 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12225 4 +
      2 / (mA 12225 : ℝ) * frobEnvelopeSquared160 12225) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12225 : ℝ)) *
      operatorEnvelope160 12225 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12225 4 +
      2 / (mA 12225 : ℝ) * frobEnvelopeSquared160 12225) +
      transverseConstant160 * √(2 / (mA 12225 : ℝ)) * operatorEnvelope160 12225 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12225 4 +
      2 / (mA 12225 : ℝ) * frobEnvelopeSquared160 12225) +
      transverseConstant160 * √(2 / (mA 12225 : ℝ)) * operatorEnvelope160 12225 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12225 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12225 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12225 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12225 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12225

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12225) :=
  agentEv (paperDesignP 12225) (Energy32 12225) ∩
  agentEv (paperDesignP 12225) (freshRetainedEvent160 12225 4) ∩
  agentEv (paperDesignP 12225) (FirstMatrix 12225) ∩
  BstLean.Part164.Eop2 12225 ∩ outputCentreEvent (paperCentres 12225)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12225)).real
      (agentEv (paperDesignP 12225) (FirstMatrix 12225))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12225)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12225 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12225)).real (BstLean.Part164.Eop2 12225)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12225)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12225)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12225) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12225) hτ
  have hL := fresh_retained_charge160 (n := 12225) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12225) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12225 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12225) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12225 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12225) (hw : WINDOW (paperDesignP 12225) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12225))
    (hW : ∫ a in K, ((12225 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12225 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12225 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12225 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12225) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12225 : ℝ)) * eR c * 12225 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12225

/-! Exact rational parameters for the dimension-12227 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12227 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12227 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12227 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12227.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12227] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12227 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12227 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12227.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12227

namespace BstLean.Part262.Row12227
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

theorem energy_allowance_row : energyAllowance 12227 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12227 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12227 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12227)
  change 0 ≤ agentLayerAllowance 12227 at ha0
  have he : energyWeightAllowance 12227 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12227)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12227)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12227).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12227).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12227)) :
    ∫ a in K, fbR c a ^ k ∂muI 12227 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12227])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12227

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12227 / 12227 ≤ chi := by
  have hs : √((12227 : ℝ) * 12) ≤ (38304569 / 100000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12227}
    (hc : c ∈ outputCentreEvent (paperCentres 12227)) :
    normSq c.2.1.2 ≤ (2 / (12227 : ℝ)) * eR c * 12227 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12227 : ℝ) * normSq (bR c) * chiUp 12227 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12227)).real (outputCentreEvent (paperCentres 12227))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12227

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12227) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12227) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12227)]
  norm_num [varianceMax]

end BstLean.Part262.Row12227

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12227) (hc : A1 c ∈ Eop 12227) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12227 : ℝ)) ≤ (3197385863 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12227 : ℝ) ≤ (55287883 / 500000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12227 : ℝ) + 2 * √12227 ≤ (3112037883 / 250000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12227) (hc : c ∈ BstLean.Part164.Eop2 12227) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12227 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12227) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12227 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12227) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12227).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12227) (FirstMatrix 12227))
    (h2 : c ∈ BstLean.Part164.Eop2 12227) (a : BstLean.Part161.Ix 12227) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12227

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12227) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12227) c ∈ BstLean.Part212.latitudeEvent 12227
      (ENNReal.ofReal (C / 12227))) (K : Set (Ix 12227)) :
    ∫ a in K, ((12227 : ℝ) * VR c a) ^ 2 ∂muI 12227 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12227

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12227 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12227 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12227 - 1 - 1) 80 ≤ (12383 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12227 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12383 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12227) ≤ (78 * 10 ^ 6 * ((12227 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12227 : ℝ) / 2 + 160) ≤ (8645803867 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12227 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12227 : ℝ) ^ 2 / 2 + 320 = 149500169 / 2 by norm_num,
    show (12227 : ℝ) ^ 2 / 2 + 160 = 149499849 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12227 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12227 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12227 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12227 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12227)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12227) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12227 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12227)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12227 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12227 ≤ (160 : ℝ) := by
  have hs : √(2 / (12227 : ℝ)) ≤ (3197385863 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12227 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12227 : ℝ) = 12227 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12227 : ℝ) + √12227 + gaussMomConst 80 ≤ 12347 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12227 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12227 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12227 4 +
      2 / (mA 12227 : ℝ) * frobEnvelopeSquared160 12227 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12227 4 +
      2 / (mA 12227 : ℝ) * frobEnvelopeSquared160 12227) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12227 : ℝ)) *
      operatorEnvelope160 12227 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12227 4 +
      2 / (mA 12227 : ℝ) * frobEnvelopeSquared160 12227) +
      transverseConstant160 * √(2 / (mA 12227 : ℝ)) * operatorEnvelope160 12227 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12227 4 +
      2 / (mA 12227 : ℝ) * frobEnvelopeSquared160 12227) +
      transverseConstant160 * √(2 / (mA 12227 : ℝ)) * operatorEnvelope160 12227 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12227 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12227 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12227 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12227 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12227

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12227) :=
  agentEv (paperDesignP 12227) (Energy32 12227) ∩
  agentEv (paperDesignP 12227) (freshRetainedEvent160 12227 4) ∩
  agentEv (paperDesignP 12227) (FirstMatrix 12227) ∩
  BstLean.Part164.Eop2 12227 ∩ outputCentreEvent (paperCentres 12227)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12227)).real
      (agentEv (paperDesignP 12227) (FirstMatrix 12227))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12227)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12227 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12227)).real (BstLean.Part164.Eop2 12227)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12227)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12227)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12227) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12227) hτ
  have hL := fresh_retained_charge160 (n := 12227) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12227) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12227 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12227) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12227 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12227) (hw : WINDOW (paperDesignP 12227) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12227))
    (hW : ∫ a in K, ((12227 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12227 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12227 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12227 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12227) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12227 : ℝ)) * eR c * 12227 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12227

/-! Exact rational parameters for the dimension-12228 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12228 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12228 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12228 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12228.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12228] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12228 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12228 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12228.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12228

namespace BstLean.Part262.Row12228
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

theorem energy_allowance_row : energyAllowance 12228 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12228 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12228 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12228)
  change 0 ≤ agentLayerAllowance 12228 at ha0
  have he : energyWeightAllowance 12228 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12228)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12228)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12228).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12228).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12228)) :
    ∫ a in K, fbR c a ^ k ∂muI 12228 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12228])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12228

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12228 / 12228 ≤ chi := by
  have hs : √((12228 : ℝ) * 12) ≤ (383061353 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12228}
    (hc : c ∈ outputCentreEvent (paperCentres 12228)) :
    normSq c.2.1.2 ≤ (2 / (12228 : ℝ)) * eR c * 12228 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12228 : ℝ) * normSq (bR c) * chiUp 12228 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12228)).real (outputCentreEvent (paperCentres 12228))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12228

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12228) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12228) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12228)]
  norm_num [varianceMax]

end BstLean.Part262.Row12228

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12228) (hc : A1 c ∈ Eop 12228) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12228 : ℝ)) ≤ (39965689 / 3125000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12228 : ℝ) ≤ (1727817 / 15625) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12228 : ℝ) + 2 * √12228 ≤ (194518134 / 15625) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12228) (hc : c ∈ BstLean.Part164.Eop2 12228) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12228 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12228) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12228 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12228) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12228).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12228) (FirstMatrix 12228))
    (h2 : c ∈ BstLean.Part164.Eop2 12228) (a : BstLean.Part161.Ix 12228) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12228

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12228) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12228) c ∈ BstLean.Part212.latitudeEvent 12228
      (ENNReal.ofReal (C / 12228))) (K : Set (Ix 12228)) :
    ∫ a in K, ((12228 : ℝ) * VR c a) ^ 2 ∂muI 12228 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12228

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12228 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12228 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12228 - 1 - 1) 80 ≤ (12384 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12228 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12384 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12228) ≤ (78 * 10 ^ 6 * ((12228 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12228 : ℝ) / 2 + 160) ≤ (8646510973 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12228 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12228 : ℝ) ^ 2 / 2 + 320 = 149524624 / 2 by norm_num,
    show (12228 : ℝ) ^ 2 / 2 + 160 = 149524304 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12228 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12228 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12228 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12228 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12228)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12228) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12228 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12228)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12228 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12228 ≤ (160 : ℝ) := by
  have hs : √(2 / (12228 : ℝ)) ≤ (39965689 / 3125000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12228 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12228 : ℝ) = 12228 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12228 : ℝ) + √12228 + gaussMomConst 80 ≤ 12348 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12228 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12228 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12228 4 +
      2 / (mA 12228 : ℝ) * frobEnvelopeSquared160 12228 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12228 4 +
      2 / (mA 12228 : ℝ) * frobEnvelopeSquared160 12228) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12228 : ℝ)) *
      operatorEnvelope160 12228 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12228 4 +
      2 / (mA 12228 : ℝ) * frobEnvelopeSquared160 12228) +
      transverseConstant160 * √(2 / (mA 12228 : ℝ)) * operatorEnvelope160 12228 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12228 4 +
      2 / (mA 12228 : ℝ) * frobEnvelopeSquared160 12228) +
      transverseConstant160 * √(2 / (mA 12228 : ℝ)) * operatorEnvelope160 12228 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12228 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12228 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12228 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12228 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12228

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12228) :=
  agentEv (paperDesignP 12228) (Energy32 12228) ∩
  agentEv (paperDesignP 12228) (freshRetainedEvent160 12228 4) ∩
  agentEv (paperDesignP 12228) (FirstMatrix 12228) ∩
  BstLean.Part164.Eop2 12228 ∩ outputCentreEvent (paperCentres 12228)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12228)).real
      (agentEv (paperDesignP 12228) (FirstMatrix 12228))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12228)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12228 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12228)).real (BstLean.Part164.Eop2 12228)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12228)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12228)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12228) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12228) hτ
  have hL := fresh_retained_charge160 (n := 12228) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12228) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12228 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12228) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12228 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12228) (hw : WINDOW (paperDesignP 12228) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12228))
    (hW : ∫ a in K, ((12228 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12228 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12228 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12228 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12228) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12228 : ℝ)) * eR c * 12228 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12228

/-! Exact rational parameters for the dimension-12229 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12229 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12229 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12229 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12229.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12229] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12229 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12229 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12229.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12229

namespace BstLean.Part262.Row12229
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

theorem energy_allowance_row : energyAllowance 12229 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12229 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12229 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12229)
  change 0 ≤ agentLayerAllowance 12229 at ha0
  have he : energyWeightAllowance 12229 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12229)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12229)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12229).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12229).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12229)) :
    ∫ a in K, fbR c a ^ k ∂muI 12229 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12229])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12229

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12229 / 12229 ≤ chi := by
  have hs : √((12229 : ℝ) * 12) ≤ (47884627 / 125000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12229}
    (hc : c ∈ outputCentreEvent (paperCentres 12229)) :
    normSq c.2.1.2 ≤ (2 / (12229 : ℝ)) * eR c * 12229 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12229 : ℝ) * normSq (bR c) * chiUp 12229 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12229)).real (outputCentreEvent (paperCentres 12229))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12229

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12229) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12229) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12229)]
  norm_num [varianceMax]

end BstLean.Part262.Row12229

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12229) (hc : A1 c ∈ Eop 12229) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12229 : ℝ)) ≤ (3197124393 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12229 : ℝ) ≤ (11058481 / 100000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12229 : ℝ) + 2 * √12229 ≤ (622508481 / 50000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12229) (hc : c ∈ BstLean.Part164.Eop2 12229) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12229 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12229) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12229 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12229) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12229).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12229) (FirstMatrix 12229))
    (h2 : c ∈ BstLean.Part164.Eop2 12229) (a : BstLean.Part161.Ix 12229) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12229

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12229) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12229) c ∈ BstLean.Part212.latitudeEvent 12229
      (ENNReal.ofReal (C / 12229))) (K : Set (Ix 12229)) :
    ∫ a in K, ((12229 : ℝ) * VR c a) ^ 2 ∂muI 12229 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12229

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12229 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12229 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12229 - 1 - 1) 80 ≤ (12385 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12229 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12385 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12229) ≤ (78 * 10 ^ 6 * ((12229 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12229 : ℝ) / 2 + 160) ≤ (8647218079 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12229 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12229 : ℝ) ^ 2 / 2 + 320 = 149549081 / 2 by norm_num,
    show (12229 : ℝ) ^ 2 / 2 + 160 = 149548761 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12229 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12229 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12229 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12229 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12229)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12229) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12229 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12229)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12229 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12229 ≤ (160 : ℝ) := by
  have hs : √(2 / (12229 : ℝ)) ≤ (3197124393 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12229 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12229 : ℝ) = 12229 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12229 : ℝ) + √12229 + gaussMomConst 80 ≤ 12349 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12229 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12229 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12229 4 +
      2 / (mA 12229 : ℝ) * frobEnvelopeSquared160 12229 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12229 4 +
      2 / (mA 12229 : ℝ) * frobEnvelopeSquared160 12229) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12229 : ℝ)) *
      operatorEnvelope160 12229 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12229 4 +
      2 / (mA 12229 : ℝ) * frobEnvelopeSquared160 12229) +
      transverseConstant160 * √(2 / (mA 12229 : ℝ)) * operatorEnvelope160 12229 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12229 4 +
      2 / (mA 12229 : ℝ) * frobEnvelopeSquared160 12229) +
      transverseConstant160 * √(2 / (mA 12229 : ℝ)) * operatorEnvelope160 12229 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12229 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12229 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12229 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12229 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12229

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12229) :=
  agentEv (paperDesignP 12229) (Energy32 12229) ∩
  agentEv (paperDesignP 12229) (freshRetainedEvent160 12229 4) ∩
  agentEv (paperDesignP 12229) (FirstMatrix 12229) ∩
  BstLean.Part164.Eop2 12229 ∩ outputCentreEvent (paperCentres 12229)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12229)).real
      (agentEv (paperDesignP 12229) (FirstMatrix 12229))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12229)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12229 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12229)).real (BstLean.Part164.Eop2 12229)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12229)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12229)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12229) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12229) hτ
  have hL := fresh_retained_charge160 (n := 12229) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12229) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12229 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12229) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12229 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12229) (hw : WINDOW (paperDesignP 12229) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12229))
    (hW : ∫ a in K, ((12229 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12229 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12229 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12229 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12229) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12229 : ℝ)) * eR c * 12229 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12229

/-! Exact rational parameters for the dimension-12230 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12230 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12230 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12230 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12230.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12230] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12230 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12230 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12230.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12230

namespace BstLean.Part262.Row12230
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

theorem energy_allowance_row : energyAllowance 12230 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12230 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12230 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12230)
  change 0 ≤ agentLayerAllowance 12230 at ha0
  have he : energyWeightAllowance 12230 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12230)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12230)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12230).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12230).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12230)) :
    ∫ a in K, fbR c a ^ k ∂muI 12230 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12230])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12230

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12230 / 12230 ≤ chi := by
  have hs : √((12230 : ℝ) * 12) ≤ (383092679 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12230}
    (hc : c ∈ outputCentreEvent (paperCentres 12230)) :
    normSq c.2.1.2 ≤ (2 / (12230 : ℝ)) * eR c * 12230 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12230 : ℝ) * normSq (bR c) * chiUp 12230 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12230)).real (outputCentreEvent (paperCentres 12230))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12230

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12230) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12230) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12230)]
  norm_num [varianceMax]

end BstLean.Part262.Row12230

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12230) (hc : A1 c ∈ Eop 12230) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12230 : ℝ)) ≤ (1598496841 / 125000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12230 : ℝ) ≤ (110589331 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12230 : ℝ) + 2 * √12230 ≤ (6225589331 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12230) (hc : c ∈ BstLean.Part164.Eop2 12230) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12230 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12230) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12230 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12230) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12230).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12230) (FirstMatrix 12230))
    (h2 : c ∈ BstLean.Part164.Eop2 12230) (a : BstLean.Part161.Ix 12230) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12230

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12230) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12230) c ∈ BstLean.Part212.latitudeEvent 12230
      (ENNReal.ofReal (C / 12230))) (K : Set (Ix 12230)) :
    ∫ a in K, ((12230 : ℝ) * VR c a) ^ 2 ∂muI 12230 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12230

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12230 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12230 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12230 - 1 - 1) 80 ≤ (12386 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12230 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12386 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12230) ≤ (78 * 10 ^ 6 * ((12230 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12230 : ℝ) / 2 + 160) ≤ (1729585037 / 200000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12230 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12230 : ℝ) ^ 2 / 2 + 320 = 149573540 / 2 by norm_num,
    show (12230 : ℝ) ^ 2 / 2 + 160 = 149573220 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12230 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12230 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12230 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12230 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12230)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12230) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12230 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12230)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12230 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12230 ≤ (160 : ℝ) := by
  have hs : √(2 / (12230 : ℝ)) ≤ (1598496841 / 125000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12230 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12230 : ℝ) = 12230 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12230 : ℝ) + √12230 + gaussMomConst 80 ≤ 12350 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12230 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12230 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12230 4 +
      2 / (mA 12230 : ℝ) * frobEnvelopeSquared160 12230 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12230 4 +
      2 / (mA 12230 : ℝ) * frobEnvelopeSquared160 12230) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12230 : ℝ)) *
      operatorEnvelope160 12230 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12230 4 +
      2 / (mA 12230 : ℝ) * frobEnvelopeSquared160 12230) +
      transverseConstant160 * √(2 / (mA 12230 : ℝ)) * operatorEnvelope160 12230 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12230 4 +
      2 / (mA 12230 : ℝ) * frobEnvelopeSquared160 12230) +
      transverseConstant160 * √(2 / (mA 12230 : ℝ)) * operatorEnvelope160 12230 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12230 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12230 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12230 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12230 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12230

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12230) :=
  agentEv (paperDesignP 12230) (Energy32 12230) ∩
  agentEv (paperDesignP 12230) (freshRetainedEvent160 12230 4) ∩
  agentEv (paperDesignP 12230) (FirstMatrix 12230) ∩
  BstLean.Part164.Eop2 12230 ∩ outputCentreEvent (paperCentres 12230)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12230)).real
      (agentEv (paperDesignP 12230) (FirstMatrix 12230))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12230)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12230 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12230)).real (BstLean.Part164.Eop2 12230)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12230)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12230)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12230) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12230) hτ
  have hL := fresh_retained_charge160 (n := 12230) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12230) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12230 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12230) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12230 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12230) (hw : WINDOW (paperDesignP 12230) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12230))
    (hW : ∫ a in K, ((12230 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12230 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12230 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12230 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12230) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12230 : ℝ)) * eR c * 12230 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12230

/-! Exact rational parameters for the dimension-12231 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12231 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12231 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12231 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12231.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12231] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12231 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12231 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12231.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12231

namespace BstLean.Part262.Row12231
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

theorem energy_allowance_row : energyAllowance 12231 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12231 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12231 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12231)
  change 0 ≤ agentLayerAllowance 12231 at ha0
  have he : energyWeightAllowance 12231 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12231)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12231)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12231).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12231).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12231)) :
    ∫ a in K, fbR c a ^ k ∂muI 12231 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12231])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12231

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12231 / 12231 ≤ chi := by
  have hs : √((12231 : ℝ) * 12) ≤ (19155417 / 50000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12231}
    (hc : c ∈ outputCentreEvent (paperCentres 12231)) :
    normSq c.2.1.2 ≤ (2 / (12231 : ℝ)) * eR c * 12231 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12231 : ℝ) * normSq (bR c) * chiUp 12231 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12231)).real (outputCentreEvent (paperCentres 12231))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12231

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12231) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12231) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12231)]
  norm_num [varianceMax]

end BstLean.Part262.Row12231

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12231) (hc : A1 c ∈ Eop 12231) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12231 : ℝ)) ≤ (3196862987 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12231 : ℝ) ≤ (27648463 / 250000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12231 : ℝ) + 2 * √12231 ≤ (1556523463 / 125000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12231) (hc : c ∈ BstLean.Part164.Eop2 12231) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12231 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12231) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12231 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12231) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12231).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12231) (FirstMatrix 12231))
    (h2 : c ∈ BstLean.Part164.Eop2 12231) (a : BstLean.Part161.Ix 12231) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12231

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12231) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12231) c ∈ BstLean.Part212.latitudeEvent 12231
      (ENNReal.ofReal (C / 12231))) (K : Set (Ix 12231)) :
    ∫ a in K, ((12231 : ℝ) * VR c a) ^ 2 ∂muI 12231 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12231

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12231 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12231 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12231 - 1 - 1) 80 ≤ (12387 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12231 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12387 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12231) ≤ (78 * 10 ^ 6 * ((12231 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12231 : ℝ) / 2 + 160) ≤ (8648632291 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12231 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12231 : ℝ) ^ 2 / 2 + 320 = 149598001 / 2 by norm_num,
    show (12231 : ℝ) ^ 2 / 2 + 160 = 149597681 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12231 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12231 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12231 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12231 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12231)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12231) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12231 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12231)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12231 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12231 ≤ (160 : ℝ) := by
  have hs : √(2 / (12231 : ℝ)) ≤ (3196862987 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12231 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12231 : ℝ) = 12231 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12231 : ℝ) + √12231 + gaussMomConst 80 ≤ 12351 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12231 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12231 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12231 4 +
      2 / (mA 12231 : ℝ) * frobEnvelopeSquared160 12231 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12231 4 +
      2 / (mA 12231 : ℝ) * frobEnvelopeSquared160 12231) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12231 : ℝ)) *
      operatorEnvelope160 12231 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12231 4 +
      2 / (mA 12231 : ℝ) * frobEnvelopeSquared160 12231) +
      transverseConstant160 * √(2 / (mA 12231 : ℝ)) * operatorEnvelope160 12231 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12231 4 +
      2 / (mA 12231 : ℝ) * frobEnvelopeSquared160 12231) +
      transverseConstant160 * √(2 / (mA 12231 : ℝ)) * operatorEnvelope160 12231 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12231 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12231 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12231 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12231 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12231

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12231) :=
  agentEv (paperDesignP 12231) (Energy32 12231) ∩
  agentEv (paperDesignP 12231) (freshRetainedEvent160 12231 4) ∩
  agentEv (paperDesignP 12231) (FirstMatrix 12231) ∩
  BstLean.Part164.Eop2 12231 ∩ outputCentreEvent (paperCentres 12231)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12231)).real
      (agentEv (paperDesignP 12231) (FirstMatrix 12231))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12231)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12231 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12231)).real (BstLean.Part164.Eop2 12231)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12231)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12231)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12231) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12231) hτ
  have hL := fresh_retained_charge160 (n := 12231) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12231) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12231 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12231) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12231 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12231) (hw : WINDOW (paperDesignP 12231) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12231))
    (hW : ∫ a in K, ((12231 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12231 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12231 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12231 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12231) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12231 : ℝ)) * eR c * 12231 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12231

/-! Exact rational parameters for the dimension-12232 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12232 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12232 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12232 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12232.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12232] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12232 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12232 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12232.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12232

namespace BstLean.Part262.Row12232
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

theorem energy_allowance_row : energyAllowance 12232 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12232 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12232 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12232)
  change 0 ≤ agentLayerAllowance 12232 at ha0
  have he : energyWeightAllowance 12232 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12232)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12232)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12232).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12232).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12232)) :
    ∫ a in K, fbR c a ^ k ∂muI 12232 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12232])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12232

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12232 / 12232 ≤ chi := by
  have hs : √((12232 : ℝ) * 12) ≤ (383124001 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12232}
    (hc : c ∈ outputCentreEvent (paperCentres 12232)) :
    normSq c.2.1.2 ≤ (2 / (12232 : ℝ)) * eR c * 12232 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12232 : ℝ) * normSq (bR c) * chiUp 12232 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12232)).real (outputCentreEvent (paperCentres 12232))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12232

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12232) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12232) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12232)]
  norm_num [varianceMax]

end BstLean.Part262.Row12232

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12232) (hc : A1 c ∈ Eop 12232) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12232 : ℝ)) ≤ (12786929233 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12232 : ℝ) ≤ (110598373 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12232 : ℝ) + 2 * √12232 ≤ (6226598373 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12232) (hc : c ∈ BstLean.Part164.Eop2 12232) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12232 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12232) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12232 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12232) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12232).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12232) (FirstMatrix 12232))
    (h2 : c ∈ BstLean.Part164.Eop2 12232) (a : BstLean.Part161.Ix 12232) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12232

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12232) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12232) c ∈ BstLean.Part212.latitudeEvent 12232
      (ENNReal.ofReal (C / 12232))) (K : Set (Ix 12232)) :
    ∫ a in K, ((12232 : ℝ) * VR c a) ^ 2 ∂muI 12232 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12232

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12232 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12232 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12232 - 1 - 1) 80 ≤ (12388 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12232 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12388 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12232) ≤ (78 * 10 ^ 6 * ((12232 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12232 : ℝ) / 2 + 160) ≤ (8649339397 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12232 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12232 : ℝ) ^ 2 / 2 + 320 = 149622464 / 2 by norm_num,
    show (12232 : ℝ) ^ 2 / 2 + 160 = 149622144 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12232 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12232 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12232 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12232 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12232)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12232) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12232 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12232)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12232 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12232 ≤ (160 : ℝ) := by
  have hs : √(2 / (12232 : ℝ)) ≤ (12786929233 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12232 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12232 : ℝ) = 12232 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12232 : ℝ) + √12232 + gaussMomConst 80 ≤ 12352 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12232 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12232 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12232 4 +
      2 / (mA 12232 : ℝ) * frobEnvelopeSquared160 12232 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12232 4 +
      2 / (mA 12232 : ℝ) * frobEnvelopeSquared160 12232) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12232 : ℝ)) *
      operatorEnvelope160 12232 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12232 4 +
      2 / (mA 12232 : ℝ) * frobEnvelopeSquared160 12232) +
      transverseConstant160 * √(2 / (mA 12232 : ℝ)) * operatorEnvelope160 12232 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12232 4 +
      2 / (mA 12232 : ℝ) * frobEnvelopeSquared160 12232) +
      transverseConstant160 * √(2 / (mA 12232 : ℝ)) * operatorEnvelope160 12232 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12232 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12232 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12232 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12232 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12232

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12232) :=
  agentEv (paperDesignP 12232) (Energy32 12232) ∩
  agentEv (paperDesignP 12232) (freshRetainedEvent160 12232 4) ∩
  agentEv (paperDesignP 12232) (FirstMatrix 12232) ∩
  BstLean.Part164.Eop2 12232 ∩ outputCentreEvent (paperCentres 12232)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12232)).real
      (agentEv (paperDesignP 12232) (FirstMatrix 12232))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12232)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12232 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12232)).real (BstLean.Part164.Eop2 12232)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12232)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12232)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12232) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12232) hτ
  have hL := fresh_retained_charge160 (n := 12232) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12232) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12232 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12232) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12232 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12232) (hw : WINDOW (paperDesignP 12232) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12232))
    (hW : ∫ a in K, ((12232 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12232 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12232 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12232 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12232) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12232 : ℝ)) * eR c * 12232 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12232

/-! Exact rational parameters for the dimension-12233 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12233 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12233 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12233 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12233.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12233] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12233 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12233 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12233.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12233

namespace BstLean.Part262.Row12233
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

theorem energy_allowance_row : energyAllowance 12233 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12233 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12233 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12233)
  change 0 ≤ agentLayerAllowance 12233 at ha0
  have he : energyWeightAllowance 12233 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12233)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12233)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12233).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12233).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12233)) :
    ∫ a in K, fbR c a ^ k ∂muI 12233 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12233])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12233

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12233 / 12233 ≤ chi := by
  have hs : √((12233 : ℝ) * 12) ≤ (191569831 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12233}
    (hc : c ∈ outputCentreEvent (paperCentres 12233)) :
    normSq c.2.1.2 ≤ (2 / (12233 : ℝ)) * eR c * 12233 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12233 : ℝ) * normSq (bR c) * chiUp 12233 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12233)).real (outputCentreEvent (paperCentres 12233))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12233

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12233) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12233) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12233)]
  norm_num [varianceMax]

end BstLean.Part262.Row12233

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12233) (hc : A1 c ∈ Eop 12233) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12233 : ℝ)) ≤ (12786406581 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12233 : ℝ) ≤ (55301447 / 500000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12233 : ℝ) + 2 * √12233 ≤ (3113551447 / 250000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12233) (hc : c ∈ BstLean.Part164.Eop2 12233) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12233 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12233) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12233 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12233) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12233).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12233) (FirstMatrix 12233))
    (h2 : c ∈ BstLean.Part164.Eop2 12233) (a : BstLean.Part161.Ix 12233) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12233

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12233) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12233) c ∈ BstLean.Part212.latitudeEvent 12233
      (ENNReal.ofReal (C / 12233))) (K : Set (Ix 12233)) :
    ∫ a in K, ((12233 : ℝ) * VR c a) ^ 2 ∂muI 12233 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12233

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12233 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12233 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12233 - 1 - 1) 80 ≤ (12389 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12233 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12389 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12233) ≤ (78 * 10 ^ 6 * ((12233 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12233 : ℝ) / 2 + 160) ≤ (8650046503 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12233 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12233 : ℝ) ^ 2 / 2 + 320 = 149646929 / 2 by norm_num,
    show (12233 : ℝ) ^ 2 / 2 + 160 = 149646609 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12233 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12233 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12233 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12233 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12233)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12233) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12233 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12233)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12233 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12233 ≤ (160 : ℝ) := by
  have hs : √(2 / (12233 : ℝ)) ≤ (12786406581 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12233 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12233 : ℝ) = 12233 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12233 : ℝ) + √12233 + gaussMomConst 80 ≤ 12353 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12233 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12233 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12233 4 +
      2 / (mA 12233 : ℝ) * frobEnvelopeSquared160 12233 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12233 4 +
      2 / (mA 12233 : ℝ) * frobEnvelopeSquared160 12233) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12233 : ℝ)) *
      operatorEnvelope160 12233 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12233 4 +
      2 / (mA 12233 : ℝ) * frobEnvelopeSquared160 12233) +
      transverseConstant160 * √(2 / (mA 12233 : ℝ)) * operatorEnvelope160 12233 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12233 4 +
      2 / (mA 12233 : ℝ) * frobEnvelopeSquared160 12233) +
      transverseConstant160 * √(2 / (mA 12233 : ℝ)) * operatorEnvelope160 12233 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12233 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12233 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12233 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12233 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12233

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12233) :=
  agentEv (paperDesignP 12233) (Energy32 12233) ∩
  agentEv (paperDesignP 12233) (freshRetainedEvent160 12233 4) ∩
  agentEv (paperDesignP 12233) (FirstMatrix 12233) ∩
  BstLean.Part164.Eop2 12233 ∩ outputCentreEvent (paperCentres 12233)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12233)).real
      (agentEv (paperDesignP 12233) (FirstMatrix 12233))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12233)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12233 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12233)).real (BstLean.Part164.Eop2 12233)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12233)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12233)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12233) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12233) hτ
  have hL := fresh_retained_charge160 (n := 12233) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12233) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12233 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12233) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12233 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12233) (hw : WINDOW (paperDesignP 12233) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12233))
    (hW : ∫ a in K, ((12233 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12233 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12233 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12233 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12233) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12233 : ℝ)) * eR c * 12233 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12233

/-! Exact rational parameters for the dimension-12234 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12234 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12234 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12234 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12234.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12234] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12234 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12234 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12234.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12234

namespace BstLean.Part262.Row12234
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

theorem energy_allowance_row : energyAllowance 12234 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12234 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12234 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12234)
  change 0 ≤ agentLayerAllowance 12234 at ha0
  have he : energyWeightAllowance 12234 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12234)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12234)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12234).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12234).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12234)) :
    ∫ a in K, fbR c a ^ k ∂muI 12234 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12234])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12234

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12234 / 12234 ≤ chi := by
  have hs : √((12234 : ℝ) * 12) ≤ (383155321 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12234}
    (hc : c ∈ outputCentreEvent (paperCentres 12234)) :
    normSq c.2.1.2 ≤ (2 / (12234 : ℝ)) * eR c * 12234 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12234 : ℝ) * normSq (bR c) * chiUp 12234 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12234)).real (outputCentreEvent (paperCentres 12234))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12234

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12234) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12234) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12234)]
  norm_num [varianceMax]

end BstLean.Part262.Row12234

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12234) (hc : A1 c ∈ Eop 12234) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12234 : ℝ)) ≤ (6392941997 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12234 : ℝ) ≤ (55303707 / 500000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12234 : ℝ) + 2 * √12234 ≤ (3113803707 / 250000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12234) (hc : c ∈ BstLean.Part164.Eop2 12234) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12234 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12234) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12234 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12234) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12234).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12234) (FirstMatrix 12234))
    (h2 : c ∈ BstLean.Part164.Eop2 12234) (a : BstLean.Part161.Ix 12234) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12234

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12234) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12234) c ∈ BstLean.Part212.latitudeEvent 12234
      (ENNReal.ofReal (C / 12234))) (K : Set (Ix 12234)) :
    ∫ a in K, ((12234 : ℝ) * VR c a) ^ 2 ∂muI 12234 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12234

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12234 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12234 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12234 - 1 - 1) 80 ≤ (12390 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12234 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12390 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12234) ≤ (78 * 10 ^ 6 * ((12234 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12234 : ℝ) / 2 + 160) ≤ (8650753609 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12234 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12234 : ℝ) ^ 2 / 2 + 320 = 149671396 / 2 by norm_num,
    show (12234 : ℝ) ^ 2 / 2 + 160 = 149671076 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12234 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12234 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12234 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12234 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12234)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12234) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12234 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12234)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12234 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12234 ≤ (160 : ℝ) := by
  have hs : √(2 / (12234 : ℝ)) ≤ (6392941997 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12234 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12234 : ℝ) = 12234 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12234 : ℝ) + √12234 + gaussMomConst 80 ≤ 12354 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12234 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12234 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12234 4 +
      2 / (mA 12234 : ℝ) * frobEnvelopeSquared160 12234 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12234 4 +
      2 / (mA 12234 : ℝ) * frobEnvelopeSquared160 12234) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12234 : ℝ)) *
      operatorEnvelope160 12234 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12234 4 +
      2 / (mA 12234 : ℝ) * frobEnvelopeSquared160 12234) +
      transverseConstant160 * √(2 / (mA 12234 : ℝ)) * operatorEnvelope160 12234 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12234 4 +
      2 / (mA 12234 : ℝ) * frobEnvelopeSquared160 12234) +
      transverseConstant160 * √(2 / (mA 12234 : ℝ)) * operatorEnvelope160 12234 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12234 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12234 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12234 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12234 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12234

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12234) :=
  agentEv (paperDesignP 12234) (Energy32 12234) ∩
  agentEv (paperDesignP 12234) (freshRetainedEvent160 12234 4) ∩
  agentEv (paperDesignP 12234) (FirstMatrix 12234) ∩
  BstLean.Part164.Eop2 12234 ∩ outputCentreEvent (paperCentres 12234)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12234)).real
      (agentEv (paperDesignP 12234) (FirstMatrix 12234))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12234)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12234 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12234)).real (BstLean.Part164.Eop2 12234)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12234)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12234)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12234) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12234) hτ
  have hL := fresh_retained_charge160 (n := 12234) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12234) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12234 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12234) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12234 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12234) (hw : WINDOW (paperDesignP 12234) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12234))
    (hW : ∫ a in K, ((12234 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12234 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12234 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12234 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12234) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12234 : ℝ)) * eR c * 12234 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12234

/-! Exact rational parameters for the dimension-12235 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12235 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12235 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12235 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12235.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12235] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12235 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12235 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12235.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12235

namespace BstLean.Part262.Row12235
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

theorem energy_allowance_row : energyAllowance 12235 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12235 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12235 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12235)
  change 0 ≤ agentLayerAllowance 12235 at ha0
  have he : energyWeightAllowance 12235 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12235)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12235)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12235).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12235).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12235)) :
    ∫ a in K, fbR c a ^ k ∂muI 12235 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12235])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12235

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12235 / 12235 ≤ chi := by
  have hs : √((12235 : ℝ) * 12) ≤ (383170981 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12235}
    (hc : c ∈ outputCentreEvent (paperCentres 12235)) :
    normSq c.2.1.2 ≤ (2 / (12235 : ℝ)) * eR c * 12235 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12235 : ℝ) * normSq (bR c) * chiUp 12235 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12235)).real (outputCentreEvent (paperCentres 12235))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12235

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12235) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12235) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12235)]
  norm_num [varianceMax]

end BstLean.Part262.Row12235

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12235) (hc : A1 c ∈ Eop 12235) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12235 : ℝ)) ≤ (12785361471 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12235 : ℝ) ≤ (22122387 / 200000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12235 : ℝ) + 2 * √12235 ≤ (1245622387 / 100000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12235) (hc : c ∈ BstLean.Part164.Eop2 12235) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12235 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12235) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12235 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12235) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12235).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12235) (FirstMatrix 12235))
    (h2 : c ∈ BstLean.Part164.Eop2 12235) (a : BstLean.Part161.Ix 12235) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12235

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12235) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12235) c ∈ BstLean.Part212.latitudeEvent 12235
      (ENNReal.ofReal (C / 12235))) (K : Set (Ix 12235)) :
    ∫ a in K, ((12235 : ℝ) * VR c a) ^ 2 ∂muI 12235 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12235

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12235 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12235 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12235 - 1 - 1) 80 ≤ (12391 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12235 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12391 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12235) ≤ (78 * 10 ^ 6 * ((12235 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12235 : ℝ) / 2 + 160) ≤ (1730292143 / 200000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12235 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12235 : ℝ) ^ 2 / 2 + 320 = 149695865 / 2 by norm_num,
    show (12235 : ℝ) ^ 2 / 2 + 160 = 149695545 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12235 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12235 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12235 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12235 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12235)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12235) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12235 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12235)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12235 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12235 ≤ (160 : ℝ) := by
  have hs : √(2 / (12235 : ℝ)) ≤ (12785361471 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12235 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12235 : ℝ) = 12235 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12235 : ℝ) + √12235 + gaussMomConst 80 ≤ 12355 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12235 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12235 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12235 4 +
      2 / (mA 12235 : ℝ) * frobEnvelopeSquared160 12235 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12235 4 +
      2 / (mA 12235 : ℝ) * frobEnvelopeSquared160 12235) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12235 : ℝ)) *
      operatorEnvelope160 12235 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12235 4 +
      2 / (mA 12235 : ℝ) * frobEnvelopeSquared160 12235) +
      transverseConstant160 * √(2 / (mA 12235 : ℝ)) * operatorEnvelope160 12235 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12235 4 +
      2 / (mA 12235 : ℝ) * frobEnvelopeSquared160 12235) +
      transverseConstant160 * √(2 / (mA 12235 : ℝ)) * operatorEnvelope160 12235 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12235 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12235 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12235 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12235 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12235

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12235) :=
  agentEv (paperDesignP 12235) (Energy32 12235) ∩
  agentEv (paperDesignP 12235) (freshRetainedEvent160 12235 4) ∩
  agentEv (paperDesignP 12235) (FirstMatrix 12235) ∩
  BstLean.Part164.Eop2 12235 ∩ outputCentreEvent (paperCentres 12235)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12235)).real
      (agentEv (paperDesignP 12235) (FirstMatrix 12235))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12235)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12235 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12235)).real (BstLean.Part164.Eop2 12235)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12235)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12235)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12235) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12235) hτ
  have hL := fresh_retained_charge160 (n := 12235) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12235) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12235 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12235) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12235 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12235) (hw : WINDOW (paperDesignP 12235) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12235))
    (hW : ∫ a in K, ((12235 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12235 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12235 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12235 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12235) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12235 : ℝ)) * eR c * 12235 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12235

/-! Exact rational parameters for the dimension-12236 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12236 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12236 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12236 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12236.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12236] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12236 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12236 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12236.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12236

namespace BstLean.Part262.Row12236
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

theorem energy_allowance_row : energyAllowance 12236 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12236 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12236 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12236)
  change 0 ≤ agentLayerAllowance 12236 at ha0
  have he : energyWeightAllowance 12236 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12236)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12236)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12236).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12236).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12236)) :
    ∫ a in K, fbR c a ^ k ∂muI 12236 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12236])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12236

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12236 / 12236 ≤ chi := by
  have hs : √((12236 : ℝ) * 12) ≤ (383186639 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12236}
    (hc : c ∈ outputCentreEvent (paperCentres 12236)) :
    normSq c.2.1.2 ≤ (2 / (12236 : ℝ)) * eR c * 12236 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12236 : ℝ) * normSq (bR c) * chiUp 12236 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12236)).real (outputCentreEvent (paperCentres 12236))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12236

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12236) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12236) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12236)]
  norm_num [varianceMax]

end BstLean.Part262.Row12236

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12236) (hc : A1 c ∈ Eop 12236) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12236 : ℝ)) ≤ (12784839011 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12236 : ℝ) ≤ (22123291 / 200000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12236 : ℝ) + 2 * √12236 ≤ (1245723291 / 100000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12236) (hc : c ∈ BstLean.Part164.Eop2 12236) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12236 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12236) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12236 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12236) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12236).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12236) (FirstMatrix 12236))
    (h2 : c ∈ BstLean.Part164.Eop2 12236) (a : BstLean.Part161.Ix 12236) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12236

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12236) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12236) c ∈ BstLean.Part212.latitudeEvent 12236
      (ENNReal.ofReal (C / 12236))) (K : Set (Ix 12236)) :
    ∫ a in K, ((12236 : ℝ) * VR c a) ^ 2 ∂muI 12236 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12236

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12236 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12236 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12236 - 1 - 1) 80 ≤ (12392 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12236 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12392 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12236) ≤ (78 * 10 ^ 6 * ((12236 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12236 : ℝ) / 2 + 160) ≤ (8652167821 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12236 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12236 : ℝ) ^ 2 / 2 + 320 = 149720336 / 2 by norm_num,
    show (12236 : ℝ) ^ 2 / 2 + 160 = 149720016 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12236 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12236 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12236 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12236 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12236)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12236) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12236 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12236)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12236 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12236 ≤ (160 : ℝ) := by
  have hs : √(2 / (12236 : ℝ)) ≤ (12784839011 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12236 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12236 : ℝ) = 12236 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12236 : ℝ) + √12236 + gaussMomConst 80 ≤ 12356 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12236 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12236 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12236 4 +
      2 / (mA 12236 : ℝ) * frobEnvelopeSquared160 12236 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12236 4 +
      2 / (mA 12236 : ℝ) * frobEnvelopeSquared160 12236) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12236 : ℝ)) *
      operatorEnvelope160 12236 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12236 4 +
      2 / (mA 12236 : ℝ) * frobEnvelopeSquared160 12236) +
      transverseConstant160 * √(2 / (mA 12236 : ℝ)) * operatorEnvelope160 12236 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12236 4 +
      2 / (mA 12236 : ℝ) * frobEnvelopeSquared160 12236) +
      transverseConstant160 * √(2 / (mA 12236 : ℝ)) * operatorEnvelope160 12236 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12236 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12236 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12236 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12236 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12236

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12236) :=
  agentEv (paperDesignP 12236) (Energy32 12236) ∩
  agentEv (paperDesignP 12236) (freshRetainedEvent160 12236 4) ∩
  agentEv (paperDesignP 12236) (FirstMatrix 12236) ∩
  BstLean.Part164.Eop2 12236 ∩ outputCentreEvent (paperCentres 12236)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12236)).real
      (agentEv (paperDesignP 12236) (FirstMatrix 12236))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12236)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12236 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12236)).real (BstLean.Part164.Eop2 12236)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12236)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12236)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12236) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12236) hτ
  have hL := fresh_retained_charge160 (n := 12236) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12236) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12236 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12236) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12236 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12236) (hw : WINDOW (paperDesignP 12236) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12236))
    (hW : ∫ a in K, ((12236 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12236 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12236 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12236 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12236) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12236 : ℝ)) * eR c * 12236 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12236

/-! Exact rational parameters for the dimension-12237 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12237 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12237 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12237 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12237.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12237] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12237 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12237 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12237.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12237

namespace BstLean.Part262.Row12237
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

theorem energy_allowance_row : energyAllowance 12237 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12237 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12237 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12237)
  change 0 ≤ agentLayerAllowance 12237 at ha0
  have he : energyWeightAllowance 12237 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12237)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12237)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12237).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12237).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12237)) :
    ∫ a in K, fbR c a ^ k ∂muI 12237 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12237])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12237

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12237 / 12237 ≤ chi := by
  have hs : √((12237 : ℝ) * 12) ≤ (383202297 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12237}
    (hc : c ∈ outputCentreEvent (paperCentres 12237)) :
    normSq c.2.1.2 ≤ (2 / (12237 : ℝ)) * eR c * 12237 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12237 : ℝ) * normSq (bR c) * chiUp 12237 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12237)).real (outputCentreEvent (paperCentres 12237))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12237

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12237) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12237) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12237)]
  norm_num [varianceMax]

end BstLean.Part262.Row12237

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12237) (hc : A1 c ∈ Eop 12237) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12237 : ℝ)) ≤ (1598039577 / 125000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12237 : ℝ) ≤ (4424839 / 40000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12237 : ℝ) + 2 * √12237 ≤ (249164839 / 20000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12237) (hc : c ∈ BstLean.Part164.Eop2 12237) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12237 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12237) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12237 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12237) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12237).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12237) (FirstMatrix 12237))
    (h2 : c ∈ BstLean.Part164.Eop2 12237) (a : BstLean.Part161.Ix 12237) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12237

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12237) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12237) c ∈ BstLean.Part212.latitudeEvent 12237
      (ENNReal.ofReal (C / 12237))) (K : Set (Ix 12237)) :
    ∫ a in K, ((12237 : ℝ) * VR c a) ^ 2 ∂muI 12237 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12237

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12237 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12237 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12237 - 1 - 1) 80 ≤ (12393 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12237 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12393 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12237) ≤ (78 * 10 ^ 6 * ((12237 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12237 : ℝ) / 2 + 160) ≤ (8652874927 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12237 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12237 : ℝ) ^ 2 / 2 + 320 = 149744809 / 2 by norm_num,
    show (12237 : ℝ) ^ 2 / 2 + 160 = 149744489 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12237 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12237 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12237 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12237 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12237)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12237) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12237 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12237)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12237 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12237 ≤ (160 : ℝ) := by
  have hs : √(2 / (12237 : ℝ)) ≤ (1598039577 / 125000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12237 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12237 : ℝ) = 12237 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12237 : ℝ) + √12237 + gaussMomConst 80 ≤ 12357 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12237 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12237 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12237 4 +
      2 / (mA 12237 : ℝ) * frobEnvelopeSquared160 12237 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12237 4 +
      2 / (mA 12237 : ℝ) * frobEnvelopeSquared160 12237) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12237 : ℝ)) *
      operatorEnvelope160 12237 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12237 4 +
      2 / (mA 12237 : ℝ) * frobEnvelopeSquared160 12237) +
      transverseConstant160 * √(2 / (mA 12237 : ℝ)) * operatorEnvelope160 12237 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12237 4 +
      2 / (mA 12237 : ℝ) * frobEnvelopeSquared160 12237) +
      transverseConstant160 * √(2 / (mA 12237 : ℝ)) * operatorEnvelope160 12237 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12237 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12237 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12237 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12237 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12237

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12237) :=
  agentEv (paperDesignP 12237) (Energy32 12237) ∩
  agentEv (paperDesignP 12237) (freshRetainedEvent160 12237 4) ∩
  agentEv (paperDesignP 12237) (FirstMatrix 12237) ∩
  BstLean.Part164.Eop2 12237 ∩ outputCentreEvent (paperCentres 12237)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12237)).real
      (agentEv (paperDesignP 12237) (FirstMatrix 12237))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12237)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12237 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12237)).real (BstLean.Part164.Eop2 12237)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12237)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12237)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12237) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12237) hτ
  have hL := fresh_retained_charge160 (n := 12237) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12237) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12237 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12237) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12237 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12237) (hw : WINDOW (paperDesignP 12237) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12237))
    (hW : ∫ a in K, ((12237 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12237 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12237 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12237 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12237) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12237 : ℝ)) * eR c * 12237 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12237

/-! Exact rational parameters for the dimension-12238 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12238 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12238 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12238 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12238.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12238] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12238 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12238 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12238.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12238

namespace BstLean.Part262.Row12238
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

theorem energy_allowance_row : energyAllowance 12238 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12238 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12238 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12238)
  change 0 ≤ agentLayerAllowance 12238 at ha0
  have he : energyWeightAllowance 12238 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12238)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12238)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12238).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12238).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12238)) :
    ∫ a in K, fbR c a ^ k ∂muI 12238 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12238])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12238

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12238 / 12238 ≤ chi := by
  have hs : √((12238 : ℝ) * 12) ≤ (191608977 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12238}
    (hc : c ∈ outputCentreEvent (paperCentres 12238)) :
    normSq c.2.1.2 ≤ (2 / (12238 : ℝ)) * eR c * 12238 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12238 : ℝ) * normSq (bR c) * chiUp 12238 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12238)).real (outputCentreEvent (paperCentres 12238))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12238

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12238) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12238) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12238)]
  norm_num [varianceMax]

end BstLean.Part262.Row12238

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12238) (hc : A1 c ∈ Eop 12238) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12238 : ℝ)) ≤ (2556758857 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12238 : ℝ) ≤ (22125099 / 200000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12238 : ℝ) + 2 * √12238 ≤ (1245925099 / 100000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12238) (hc : c ∈ BstLean.Part164.Eop2 12238) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12238 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12238) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12238 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12238) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12238).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12238) (FirstMatrix 12238))
    (h2 : c ∈ BstLean.Part164.Eop2 12238) (a : BstLean.Part161.Ix 12238) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12238

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12238) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12238) c ∈ BstLean.Part212.latitudeEvent 12238
      (ENNReal.ofReal (C / 12238))) (K : Set (Ix 12238)) :
    ∫ a in K, ((12238 : ℝ) * VR c a) ^ 2 ∂muI 12238 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12238

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12238 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12238 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12238 - 1 - 1) 80 ≤ (12394 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12238 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12394 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12238) ≤ (78 * 10 ^ 6 * ((12238 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12238 : ℝ) / 2 + 160) ≤ (8653582033 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12238 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12238 : ℝ) ^ 2 / 2 + 320 = 149769284 / 2 by norm_num,
    show (12238 : ℝ) ^ 2 / 2 + 160 = 149768964 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12238 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12238 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12238 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12238 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12238)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12238) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12238 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12238)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12238 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12238 ≤ (160 : ℝ) := by
  have hs : √(2 / (12238 : ℝ)) ≤ (2556758857 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12238 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12238 : ℝ) = 12238 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12238 : ℝ) + √12238 + gaussMomConst 80 ≤ 12358 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12238 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12238 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12238 4 +
      2 / (mA 12238 : ℝ) * frobEnvelopeSquared160 12238 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12238 4 +
      2 / (mA 12238 : ℝ) * frobEnvelopeSquared160 12238) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12238 : ℝ)) *
      operatorEnvelope160 12238 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12238 4 +
      2 / (mA 12238 : ℝ) * frobEnvelopeSquared160 12238) +
      transverseConstant160 * √(2 / (mA 12238 : ℝ)) * operatorEnvelope160 12238 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12238 4 +
      2 / (mA 12238 : ℝ) * frobEnvelopeSquared160 12238) +
      transverseConstant160 * √(2 / (mA 12238 : ℝ)) * operatorEnvelope160 12238 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12238 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12238 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12238 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12238 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12238

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12238) :=
  agentEv (paperDesignP 12238) (Energy32 12238) ∩
  agentEv (paperDesignP 12238) (freshRetainedEvent160 12238 4) ∩
  agentEv (paperDesignP 12238) (FirstMatrix 12238) ∩
  BstLean.Part164.Eop2 12238 ∩ outputCentreEvent (paperCentres 12238)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12238)).real
      (agentEv (paperDesignP 12238) (FirstMatrix 12238))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12238)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12238 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12238)).real (BstLean.Part164.Eop2 12238)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12238)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12238)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12238) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12238) hτ
  have hL := fresh_retained_charge160 (n := 12238) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12238) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12238 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12238) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12238 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12238) (hw : WINDOW (paperDesignP 12238) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12238))
    (hW : ∫ a in K, ((12238 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12238 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12238 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12238 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12238) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12238 : ℝ)) * eR c * 12238 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12238

/-! Exact rational parameters for the dimension-12239 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12239 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12239 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12239 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12239.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12239] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12239 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12239 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12239.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12239

namespace BstLean.Part262.Row12239
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

theorem energy_allowance_row : energyAllowance 12239 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12239 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12239 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12239)
  change 0 ≤ agentLayerAllowance 12239 at ha0
  have he : energyWeightAllowance 12239 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12239)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12239)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12239).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12239).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12239)) :
    ∫ a in K, fbR c a ^ k ∂muI 12239 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12239])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12239

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12239 / 12239 ≤ chi := by
  have hs : √((12239 : ℝ) * 12) ≤ (383233611 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12239}
    (hc : c ∈ outputCentreEvent (paperCentres 12239)) :
    normSq c.2.1.2 ≤ (2 / (12239 : ℝ)) * eR c * 12239 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12239 : ℝ) * normSq (bR c) * chiUp 12239 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12239)).real (outputCentreEvent (paperCentres 12239))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12239

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12239) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12239) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12239)]
  norm_num [varianceMax]

end BstLean.Part262.Row12239

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12239) (hc : A1 c ∈ Eop 12239) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12239 : ℝ)) ≤ (6391636009 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12239 : ℝ) ≤ (22126003 / 200000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12239 : ℝ) + 2 * √12239 ≤ (1246026003 / 100000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12239) (hc : c ∈ BstLean.Part164.Eop2 12239) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12239 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12239) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12239 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12239) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12239).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12239) (FirstMatrix 12239))
    (h2 : c ∈ BstLean.Part164.Eop2 12239) (a : BstLean.Part161.Ix 12239) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12239

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12239) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12239) c ∈ BstLean.Part212.latitudeEvent 12239
      (ENNReal.ofReal (C / 12239))) (K : Set (Ix 12239)) :
    ∫ a in K, ((12239 : ℝ) * VR c a) ^ 2 ∂muI 12239 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12239

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12239 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12239 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12239 - 1 - 1) 80 ≤ (12395 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12239 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12395 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12239) ≤ (78 * 10 ^ 6 * ((12239 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12239 : ℝ) / 2 + 160) ≤ (8654289139 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12239 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12239 : ℝ) ^ 2 / 2 + 320 = 149793761 / 2 by norm_num,
    show (12239 : ℝ) ^ 2 / 2 + 160 = 149793441 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12239 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12239 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12239 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12239 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12239)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12239) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12239 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12239)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12239 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12239 ≤ (160 : ℝ) := by
  have hs : √(2 / (12239 : ℝ)) ≤ (6391636009 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12239 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12239 : ℝ) = 12239 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12239 : ℝ) + √12239 + gaussMomConst 80 ≤ 12359 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12239 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12239 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12239 4 +
      2 / (mA 12239 : ℝ) * frobEnvelopeSquared160 12239 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12239 4 +
      2 / (mA 12239 : ℝ) * frobEnvelopeSquared160 12239) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12239 : ℝ)) *
      operatorEnvelope160 12239 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12239 4 +
      2 / (mA 12239 : ℝ) * frobEnvelopeSquared160 12239) +
      transverseConstant160 * √(2 / (mA 12239 : ℝ)) * operatorEnvelope160 12239 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12239 4 +
      2 / (mA 12239 : ℝ) * frobEnvelopeSquared160 12239) +
      transverseConstant160 * √(2 / (mA 12239 : ℝ)) * operatorEnvelope160 12239 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12239 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12239 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12239 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12239 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12239

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12239) :=
  agentEv (paperDesignP 12239) (Energy32 12239) ∩
  agentEv (paperDesignP 12239) (freshRetainedEvent160 12239 4) ∩
  agentEv (paperDesignP 12239) (FirstMatrix 12239) ∩
  BstLean.Part164.Eop2 12239 ∩ outputCentreEvent (paperCentres 12239)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12239)).real
      (agentEv (paperDesignP 12239) (FirstMatrix 12239))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12239)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12239 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12239)).real (BstLean.Part164.Eop2 12239)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12239)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12239)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12239) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12239) hτ
  have hL := fresh_retained_charge160 (n := 12239) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12239) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12239 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12239) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12239 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12239) (hw : WINDOW (paperDesignP 12239) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12239))
    (hW : ∫ a in K, ((12239 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12239 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12239 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12239 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12239) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12239 : ℝ)) * eR c * 12239 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12239

/-! Exact rational parameters for the dimension-12240 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12240 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12240 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12240 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12240.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12240] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12240 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12240 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12240.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12240

namespace BstLean.Part262.Row12240
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

theorem energy_allowance_row : energyAllowance 12240 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12240 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12240 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12240)
  change 0 ≤ agentLayerAllowance 12240 at ha0
  have he : energyWeightAllowance 12240 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12240)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12240)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12240).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12240).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12240)) :
    ∫ a in K, fbR c a ^ k ∂muI 12240 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12240])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12240

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12240 / 12240 ≤ chi := by
  have hs : √((12240 : ℝ) * 12) ≤ (383249267 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12240}
    (hc : c ∈ outputCentreEvent (paperCentres 12240)) :
    normSq c.2.1.2 ≤ (2 / (12240 : ℝ)) * eR c * 12240 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12240 : ℝ) * normSq (bR c) * chiUp 12240 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12240)).real (outputCentreEvent (paperCentres 12240))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12240

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12240) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12240) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12240)]
  norm_num [varianceMax]

end BstLean.Part262.Row12240

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12240) (hc : A1 c ∈ Eop 12240) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12240 : ℝ)) ≤ (2556549963 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12240 : ℝ) ≤ (55317267 / 500000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12240 : ℝ) + 2 * √12240 ≤ (3115317267 / 250000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12240) (hc : c ∈ BstLean.Part164.Eop2 12240) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12240 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12240) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12240 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12240) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12240).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12240) (FirstMatrix 12240))
    (h2 : c ∈ BstLean.Part164.Eop2 12240) (a : BstLean.Part161.Ix 12240) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12240

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12240) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12240) c ∈ BstLean.Part212.latitudeEvent 12240
      (ENNReal.ofReal (C / 12240))) (K : Set (Ix 12240)) :
    ∫ a in K, ((12240 : ℝ) * VR c a) ^ 2 ∂muI 12240 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12240

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12240 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12240 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12240 - 1 - 1) 80 ≤ (12396 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12240 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12396 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12240) ≤ (78 * 10 ^ 6 * ((12240 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12240 : ℝ) / 2 + 160) ≤ (1730999249 / 200000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12240 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12240 : ℝ) ^ 2 / 2 + 320 = 149818240 / 2 by norm_num,
    show (12240 : ℝ) ^ 2 / 2 + 160 = 149817920 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12240 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12240 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12240 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12240 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12240)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12240) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12240 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12240)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12240 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12240 ≤ (160 : ℝ) := by
  have hs : √(2 / (12240 : ℝ)) ≤ (2556549963 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12240 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12240 : ℝ) = 12240 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12240 : ℝ) + √12240 + gaussMomConst 80 ≤ 12360 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12240 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12240 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12240 4 +
      2 / (mA 12240 : ℝ) * frobEnvelopeSquared160 12240 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12240 4 +
      2 / (mA 12240 : ℝ) * frobEnvelopeSquared160 12240) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12240 : ℝ)) *
      operatorEnvelope160 12240 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12240 4 +
      2 / (mA 12240 : ℝ) * frobEnvelopeSquared160 12240) +
      transverseConstant160 * √(2 / (mA 12240 : ℝ)) * operatorEnvelope160 12240 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12240 4 +
      2 / (mA 12240 : ℝ) * frobEnvelopeSquared160 12240) +
      transverseConstant160 * √(2 / (mA 12240 : ℝ)) * operatorEnvelope160 12240 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12240 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12240 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12240 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12240 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12240

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12240) :=
  agentEv (paperDesignP 12240) (Energy32 12240) ∩
  agentEv (paperDesignP 12240) (freshRetainedEvent160 12240 4) ∩
  agentEv (paperDesignP 12240) (FirstMatrix 12240) ∩
  BstLean.Part164.Eop2 12240 ∩ outputCentreEvent (paperCentres 12240)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12240)).real
      (agentEv (paperDesignP 12240) (FirstMatrix 12240))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12240)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12240 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12240)).real (BstLean.Part164.Eop2 12240)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12240)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12240)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12240) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12240) hτ
  have hL := fresh_retained_charge160 (n := 12240) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12240) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12240 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12240) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12240 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12240) (hw : WINDOW (paperDesignP 12240) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12240))
    (hW : ∫ a in K, ((12240 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12240 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12240 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12240 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12240) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12240 : ℝ)) * eR c * 12240 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12240

/-! Exact rational parameters for the dimension-12241 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12241 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12241 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12241 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12241.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12241] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12241 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12241 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12241.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12241

namespace BstLean.Part262.Row12241
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

theorem energy_allowance_row : energyAllowance 12241 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12241 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12241 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12241)
  change 0 ≤ agentLayerAllowance 12241 at ha0
  have he : energyWeightAllowance 12241 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12241)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12241)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12241).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12241).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12241)) :
    ∫ a in K, fbR c a ^ k ∂muI 12241 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12241])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12241

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12241 / 12241 ≤ chi := by
  have hs : √((12241 : ℝ) * 12) ≤ (191632461 / 500000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12241}
    (hc : c ∈ outputCentreEvent (paperCentres 12241)) :
    normSq c.2.1.2 ≤ (2 / (12241 : ℝ)) * eR c * 12241 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12241 : ℝ) * normSq (bR c) * chiUp 12241 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12241)).real (outputCentreEvent (paperCentres 12241))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12241

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12241) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12241) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12241)]
  norm_num [varianceMax]

end BstLean.Part262.Row12241

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12241) (hc : A1 c ∈ Eop 12241) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12241 : ℝ)) ≤ (511289107 / 40000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12241 : ℝ) ≤ (110639053 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12241 : ℝ) + 2 * √12241 ≤ (6231139053 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12241) (hc : c ∈ BstLean.Part164.Eop2 12241) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12241 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12241) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12241 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12241) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12241).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12241) (FirstMatrix 12241))
    (h2 : c ∈ BstLean.Part164.Eop2 12241) (a : BstLean.Part161.Ix 12241) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12241

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12241) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12241) c ∈ BstLean.Part212.latitudeEvent 12241
      (ENNReal.ofReal (C / 12241))) (K : Set (Ix 12241)) :
    ∫ a in K, ((12241 : ℝ) * VR c a) ^ 2 ∂muI 12241 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12241

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12241 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12241 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12241 - 1 - 1) 80 ≤ (12397 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12241 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12397 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12241) ≤ (78 * 10 ^ 6 * ((12241 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12241 : ℝ) / 2 + 160) ≤ (8655703351 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12241 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12241 : ℝ) ^ 2 / 2 + 320 = 149842721 / 2 by norm_num,
    show (12241 : ℝ) ^ 2 / 2 + 160 = 149842401 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12241 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12241 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12241 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12241 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12241)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12241) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12241 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12241)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12241 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12241 ≤ (160 : ℝ) := by
  have hs : √(2 / (12241 : ℝ)) ≤ (511289107 / 40000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12241 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12241 : ℝ) = 12241 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12241 : ℝ) + √12241 + gaussMomConst 80 ≤ 12361 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12241 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12241 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12241 4 +
      2 / (mA 12241 : ℝ) * frobEnvelopeSquared160 12241 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12241 4 +
      2 / (mA 12241 : ℝ) * frobEnvelopeSquared160 12241) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12241 : ℝ)) *
      operatorEnvelope160 12241 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12241 4 +
      2 / (mA 12241 : ℝ) * frobEnvelopeSquared160 12241) +
      transverseConstant160 * √(2 / (mA 12241 : ℝ)) * operatorEnvelope160 12241 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12241 4 +
      2 / (mA 12241 : ℝ) * frobEnvelopeSquared160 12241) +
      transverseConstant160 * √(2 / (mA 12241 : ℝ)) * operatorEnvelope160 12241 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12241 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12241 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12241 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12241 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12241

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12241) :=
  agentEv (paperDesignP 12241) (Energy32 12241) ∩
  agentEv (paperDesignP 12241) (freshRetainedEvent160 12241 4) ∩
  agentEv (paperDesignP 12241) (FirstMatrix 12241) ∩
  BstLean.Part164.Eop2 12241 ∩ outputCentreEvent (paperCentres 12241)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12241)).real
      (agentEv (paperDesignP 12241) (FirstMatrix 12241))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12241)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12241 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12241)).real (BstLean.Part164.Eop2 12241)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12241)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12241)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12241) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12241) hτ
  have hL := fresh_retained_charge160 (n := 12241) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12241) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12241 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12241) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12241 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12241) (hw : WINDOW (paperDesignP 12241) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12241))
    (hW : ∫ a in K, ((12241 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12241 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12241 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12241 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12241) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12241 : ℝ)) * eR c * 12241 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12241

/-! Exact rational parameters for the dimension-12242 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12242 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12242 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12242 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12242.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12242] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12242 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12242 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12242.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12242

namespace BstLean.Part262.Row12242
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

theorem energy_allowance_row : energyAllowance 12242 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12242 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12242 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12242)
  change 0 ≤ agentLayerAllowance 12242 at ha0
  have he : energyWeightAllowance 12242 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12242)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12242)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12242).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12242).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12242)) :
    ∫ a in K, fbR c a ^ k ∂muI 12242 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12242])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12242

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12242 / 12242 ≤ chi := by
  have hs : √((12242 : ℝ) * 12) ≤ (383280577 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12242}
    (hc : c ∈ outputCentreEvent (paperCentres 12242)) :
    normSq c.2.1.2 ≤ (2 / (12242 : ℝ)) * eR c * 12242 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12242 : ℝ) * normSq (bR c) * chiUp 12242 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12242)).real (outputCentreEvent (paperCentres 12242))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12242

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12242) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12242) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12242)]
  norm_num [varianceMax]

end BstLean.Part262.Row12242

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12242) (hc : A1 c ∈ Eop 12242) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12242 : ℝ)) ≤ (3994283 / 312500000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12242 : ℝ) ≤ (27660893 / 250000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12242 : ℝ) + 2 * √12242 ≤ (1557910893 / 125000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12242) (hc : c ∈ BstLean.Part164.Eop2 12242) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12242 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12242) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12242 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12242) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12242).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12242) (FirstMatrix 12242))
    (h2 : c ∈ BstLean.Part164.Eop2 12242) (a : BstLean.Part161.Ix 12242) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12242

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12242) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12242) c ∈ BstLean.Part212.latitudeEvent 12242
      (ENNReal.ofReal (C / 12242))) (K : Set (Ix 12242)) :
    ∫ a in K, ((12242 : ℝ) * VR c a) ^ 2 ∂muI 12242 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12242

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12242 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12242 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12242 - 1 - 1) 80 ≤ (12398 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12242 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12398 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12242) ≤ (78 * 10 ^ 6 * ((12242 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12242 : ℝ) / 2 + 160) ≤ (8656410457 / 1000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12242 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12242 : ℝ) ^ 2 / 2 + 320 = 149867204 / 2 by norm_num,
    show (12242 : ℝ) ^ 2 / 2 + 160 = 149866884 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12242 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12242 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12242 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12242 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12242)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12242) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12242 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12242)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12242 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12242 ≤ (160 : ℝ) := by
  have hs : √(2 / (12242 : ℝ)) ≤ (3994283 / 312500000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12242 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12242 : ℝ) = 12242 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12242 : ℝ) + √12242 + gaussMomConst 80 ≤ 12362 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12242 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12242 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12242 4 +
      2 / (mA 12242 : ℝ) * frobEnvelopeSquared160 12242 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12242 4 +
      2 / (mA 12242 : ℝ) * frobEnvelopeSquared160 12242) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12242 : ℝ)) *
      operatorEnvelope160 12242 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12242 4 +
      2 / (mA 12242 : ℝ) * frobEnvelopeSquared160 12242) +
      transverseConstant160 * √(2 / (mA 12242 : ℝ)) * operatorEnvelope160 12242 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12242 4 +
      2 / (mA 12242 : ℝ) * frobEnvelopeSquared160 12242) +
      transverseConstant160 * √(2 / (mA 12242 : ℝ)) * operatorEnvelope160 12242 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12242 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12242 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12242 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12242 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12242

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12242) :=
  agentEv (paperDesignP 12242) (Energy32 12242) ∩
  agentEv (paperDesignP 12242) (freshRetainedEvent160 12242 4) ∩
  agentEv (paperDesignP 12242) (FirstMatrix 12242) ∩
  BstLean.Part164.Eop2 12242 ∩ outputCentreEvent (paperCentres 12242)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12242)).real
      (agentEv (paperDesignP 12242) (FirstMatrix 12242))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12242)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12242 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12242)).real (BstLean.Part164.Eop2 12242)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12242)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12242)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12242) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12242) hτ
  have hL := fresh_retained_charge160 (n := 12242) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12242) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12242 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12242) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12242 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12242) (hw : WINDOW (paperDesignP 12242) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12242))
    (hW : ∫ a in K, ((12242 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12242 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12242 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12242 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12242) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12242 : ℝ)) * eR c * 12242 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12242

/-! Exact rational parameters for the dimension-12243 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12243 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12243 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12243 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12243.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12243] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12243 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12243 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12243.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12243

namespace BstLean.Part262.Row12243
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

theorem energy_allowance_row : energyAllowance 12243 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12243 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12243 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12243)
  change 0 ≤ agentLayerAllowance 12243 at ha0
  have he : energyWeightAllowance 12243 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12243)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12243)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12243).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12243).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12243)) :
    ∫ a in K, fbR c a ^ k ∂muI 12243 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12243])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12243

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12243 / 12243 ≤ chi := by
  have hs : √((12243 : ℝ) * 12) ≤ (383296231 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12243}
    (hc : c ∈ outputCentreEvent (paperCentres 12243)) :
    normSq c.2.1.2 ≤ (2 / (12243 : ℝ)) * eR c * 12243 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12243 : ℝ) * normSq (bR c) * chiUp 12243 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12243)).real (outputCentreEvent (paperCentres 12243))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12243

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12243) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12243) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12243)]
  norm_num [varianceMax]

end BstLean.Part262.Row12243

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12243) (hc : A1 c ∈ Eop 12243) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12243 : ℝ)) ≤ (12781183589 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12243 : ℝ) ≤ (110648091 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12243 : ℝ) + 2 * √12243 ≤ (6232148091 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12243) (hc : c ∈ BstLean.Part164.Eop2 12243) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12243 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12243) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12243 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12243) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12243).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12243) (FirstMatrix 12243))
    (h2 : c ∈ BstLean.Part164.Eop2 12243) (a : BstLean.Part161.Ix 12243) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12243

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12243) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12243) c ∈ BstLean.Part212.latitudeEvent 12243
      (ENNReal.ofReal (C / 12243))) (K : Set (Ix 12243)) :
    ∫ a in K, ((12243 : ℝ) * VR c a) ^ 2 ∂muI 12243 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12243

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12243 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12243 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12243 - 1 - 1) 80 ≤ (12399 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12243 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12399 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12243) ≤ (78 * 10 ^ 6 * ((12243 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12243 : ℝ) / 2 + 160) ≤ (2164279391 / 250000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12243 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12243 : ℝ) ^ 2 / 2 + 320 = 149891689 / 2 by norm_num,
    show (12243 : ℝ) ^ 2 / 2 + 160 = 149891369 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12243 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12243 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12243 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12243 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12243)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12243) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12243 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12243)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12243 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12243 ≤ (160 : ℝ) := by
  have hs : √(2 / (12243 : ℝ)) ≤ (12781183589 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12243 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12243 : ℝ) = 12243 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12243 : ℝ) + √12243 + gaussMomConst 80 ≤ 12363 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12243 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12243 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12243 4 +
      2 / (mA 12243 : ℝ) * frobEnvelopeSquared160 12243 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12243 4 +
      2 / (mA 12243 : ℝ) * frobEnvelopeSquared160 12243) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12243 : ℝ)) *
      operatorEnvelope160 12243 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12243 4 +
      2 / (mA 12243 : ℝ) * frobEnvelopeSquared160 12243) +
      transverseConstant160 * √(2 / (mA 12243 : ℝ)) * operatorEnvelope160 12243 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12243 4 +
      2 / (mA 12243 : ℝ) * frobEnvelopeSquared160 12243) +
      transverseConstant160 * √(2 / (mA 12243 : ℝ)) * operatorEnvelope160 12243 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12243 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12243 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12243 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12243 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12243

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12243) :=
  agentEv (paperDesignP 12243) (Energy32 12243) ∩
  agentEv (paperDesignP 12243) (freshRetainedEvent160 12243 4) ∩
  agentEv (paperDesignP 12243) (FirstMatrix 12243) ∩
  BstLean.Part164.Eop2 12243 ∩ outputCentreEvent (paperCentres 12243)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12243)).real
      (agentEv (paperDesignP 12243) (FirstMatrix 12243))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12243)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12243 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12243)).real (BstLean.Part164.Eop2 12243)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12243)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12243)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12243) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12243) hτ
  have hL := fresh_retained_charge160 (n := 12243) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12243) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12243 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12243) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12243 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12243) (hw : WINDOW (paperDesignP 12243) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12243))
    (hW : ∫ a in K, ((12243 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12243 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12243 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12243 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12243) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12243 : ℝ)) * eR c * 12243 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12243

/-! Exact rational parameters for the dimension-12244 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12244 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12244 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12244 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12244.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12244] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12244 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12244 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12244.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12244

namespace BstLean.Part262.Row12244
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

theorem energy_allowance_row : energyAllowance 12244 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12244 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12244 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12244)
  change 0 ≤ agentLayerAllowance 12244 at ha0
  have he : energyWeightAllowance 12244 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12244)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12244)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12244).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12244).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12244)) :
    ∫ a in K, fbR c a ^ k ∂muI 12244 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12244])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12244

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12244 / 12244 ≤ chi := by
  have hs : √((12244 : ℝ) * 12) ≤ (95827971 / 250000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12244}
    (hc : c ∈ outputCentreEvent (paperCentres 12244)) :
    normSq c.2.1.2 ≤ (2 / (12244 : ℝ)) * eR c * 12244 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12244 : ℝ) * normSq (bR c) * chiUp 12244 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12244)).real (outputCentreEvent (paperCentres 12244))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12244

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12244) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12244) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12244)]
  norm_num [varianceMax]

end BstLean.Part262.Row12244

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12244) (hc : A1 c ∈ Eop 12244) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12244 : ℝ)) ≤ (6390330821 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12244 : ℝ) ≤ (11065261 / 100000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12244 : ℝ) + 2 * √12244 ≤ (623265261 / 50000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12244) (hc : c ∈ BstLean.Part164.Eop2 12244) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12244 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12244) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12244 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12244) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12244).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12244) (FirstMatrix 12244))
    (h2 : c ∈ BstLean.Part164.Eop2 12244) (a : BstLean.Part161.Ix 12244) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12244

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12244) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12244) c ∈ BstLean.Part212.latitudeEvent 12244
      (ENNReal.ofReal (C / 12244))) (K : Set (Ix 12244)) :
    ∫ a in K, ((12244 : ℝ) * VR c a) ^ 2 ∂muI 12244 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12244

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12244 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12244 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12244 - 1 - 1) 80 ≤ (12400 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12244 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12400 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12244) ≤ (78 * 10 ^ 6 * ((12244 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12244 : ℝ) / 2 + 160) ≤ (865782467 / 100000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12244 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12244 : ℝ) ^ 2 / 2 + 320 = 149916176 / 2 by norm_num,
    show (12244 : ℝ) ^ 2 / 2 + 160 = 149915856 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12244 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12244 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12244 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12244 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12244)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12244) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12244 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12244)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12244 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12244 ≤ (160 : ℝ) := by
  have hs : √(2 / (12244 : ℝ)) ≤ (6390330821 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12244 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12244 : ℝ) = 12244 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12244 : ℝ) + √12244 + gaussMomConst 80 ≤ 12364 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12244 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12244 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12244 4 +
      2 / (mA 12244 : ℝ) * frobEnvelopeSquared160 12244 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12244 4 +
      2 / (mA 12244 : ℝ) * frobEnvelopeSquared160 12244) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12244 : ℝ)) *
      operatorEnvelope160 12244 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12244 4 +
      2 / (mA 12244 : ℝ) * frobEnvelopeSquared160 12244) +
      transverseConstant160 * √(2 / (mA 12244 : ℝ)) * operatorEnvelope160 12244 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12244 4 +
      2 / (mA 12244 : ℝ) * frobEnvelopeSquared160 12244) +
      transverseConstant160 * √(2 / (mA 12244 : ℝ)) * operatorEnvelope160 12244 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12244 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12244 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12244 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12244 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12244

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12244) :=
  agentEv (paperDesignP 12244) (Energy32 12244) ∩
  agentEv (paperDesignP 12244) (freshRetainedEvent160 12244 4) ∩
  agentEv (paperDesignP 12244) (FirstMatrix 12244) ∩
  BstLean.Part164.Eop2 12244 ∩ outputCentreEvent (paperCentres 12244)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12244)).real
      (agentEv (paperDesignP 12244) (FirstMatrix 12244))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12244)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12244 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12244)).real (BstLean.Part164.Eop2 12244)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12244)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12244)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12244) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12244) hτ
  have hL := fresh_retained_charge160 (n := 12244) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12244) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12244 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12244) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12244 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12244) (hw : WINDOW (paperDesignP 12244) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12244))
    (hW : ∫ a in K, ((12244 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12244 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12244 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12244 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12244) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12244 : ℝ)) * eR c * 12244 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12244

/-! Exact rational parameters for the dimension-12245 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12245 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12245 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12245 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12245.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12245] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12245 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12245 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12245.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12245

namespace BstLean.Part262.Row12245
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

theorem energy_allowance_row : energyAllowance 12245 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12245 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12245 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12245)
  change 0 ≤ agentLayerAllowance 12245 at ha0
  have he : energyWeightAllowance 12245 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12245)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12245)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12245).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12245).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12245)) :
    ∫ a in K, fbR c a ^ k ∂muI 12245 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12245])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12245

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12245 / 12245 ≤ chi := by
  have hs : √((12245 : ℝ) * 12) ≤ (383327537 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12245}
    (hc : c ∈ outputCentreEvent (paperCentres 12245)) :
    normSq c.2.1.2 ≤ (2 / (12245 : ℝ)) * eR c * 12245 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12245 : ℝ) * normSq (bR c) * chiUp 12245 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12245)).real (outputCentreEvent (paperCentres 12245))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12245

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12245) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12245) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12245)]
  norm_num [varianceMax]

end BstLean.Part262.Row12245

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12245) (hc : A1 c ∈ Eop 12245) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12245 : ℝ)) ≤ (6390069879 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12245 : ℝ) ≤ (110657129 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12245 : ℝ) + 2 * √12245 ≤ (6233157129 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12245) (hc : c ∈ BstLean.Part164.Eop2 12245) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12245 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12245) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12245 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12245) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12245).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12245) (FirstMatrix 12245))
    (h2 : c ∈ BstLean.Part164.Eop2 12245) (a : BstLean.Part161.Ix 12245) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12245

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12245) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12245) c ∈ BstLean.Part212.latitudeEvent 12245
      (ENNReal.ofReal (C / 12245))) (K : Set (Ix 12245)) :
    ∫ a in K, ((12245 : ℝ) * VR c a) ^ 2 ∂muI 12245 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12245

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12245 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12245 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12245 - 1 - 1) 80 ≤ (12401 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12245 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12401 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12245) ≤ (78 * 10 ^ 6 * ((12245 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12245 : ℝ) / 2 + 160) ≤ (135289559 / 15625) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12245 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12245 : ℝ) ^ 2 / 2 + 320 = 149940665 / 2 by norm_num,
    show (12245 : ℝ) ^ 2 / 2 + 160 = 149940345 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12245 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12245 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12245 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12245 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12245)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12245) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12245 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12245)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12245 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12245 ≤ (160 : ℝ) := by
  have hs : √(2 / (12245 : ℝ)) ≤ (6390069879 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12245 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12245 : ℝ) = 12245 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12245 : ℝ) + √12245 + gaussMomConst 80 ≤ 12365 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12245 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12245 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12245 4 +
      2 / (mA 12245 : ℝ) * frobEnvelopeSquared160 12245 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12245 4 +
      2 / (mA 12245 : ℝ) * frobEnvelopeSquared160 12245) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12245 : ℝ)) *
      operatorEnvelope160 12245 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12245 4 +
      2 / (mA 12245 : ℝ) * frobEnvelopeSquared160 12245) +
      transverseConstant160 * √(2 / (mA 12245 : ℝ)) * operatorEnvelope160 12245 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12245 4 +
      2 / (mA 12245 : ℝ) * frobEnvelopeSquared160 12245) +
      transverseConstant160 * √(2 / (mA 12245 : ℝ)) * operatorEnvelope160 12245 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12245 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12245 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12245 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12245 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12245

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12245) :=
  agentEv (paperDesignP 12245) (Energy32 12245) ∩
  agentEv (paperDesignP 12245) (freshRetainedEvent160 12245 4) ∩
  agentEv (paperDesignP 12245) (FirstMatrix 12245) ∩
  BstLean.Part164.Eop2 12245 ∩ outputCentreEvent (paperCentres 12245)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12245)).real
      (agentEv (paperDesignP 12245) (FirstMatrix 12245))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12245)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12245 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12245)).real (BstLean.Part164.Eop2 12245)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12245)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12245)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12245) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12245) hτ
  have hL := fresh_retained_charge160 (n := 12245) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12245) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12245 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12245) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12245 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12245) (hw : WINDOW (paperDesignP 12245) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12245))
    (hW : ∫ a in K, ((12245 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12245 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12245 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12245 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12245) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12245 : ℝ)) * eR c * 12245 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12245

/-! Exact rational parameters for the dimension-12246 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12246 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12246 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12246 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12246.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12246] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12246 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12246 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12246.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12246

namespace BstLean.Part262.Row12246
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

theorem energy_allowance_row : energyAllowance 12246 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12246 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12246 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12246)
  change 0 ≤ agentLayerAllowance 12246 at ha0
  have he : energyWeightAllowance 12246 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12246)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12246)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12246).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12246).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12246)) :
    ∫ a in K, fbR c a ^ k ∂muI 12246 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12246])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12246

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12246 / 12246 ≤ chi := by
  have hs : √((12246 : ℝ) * 12) ≤ (383343189 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12246}
    (hc : c ∈ outputCentreEvent (paperCentres 12246)) :
    normSq c.2.1.2 ≤ (2 / (12246 : ℝ)) * eR c * 12246 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12246 : ℝ) * normSq (bR c) * chiUp 12246 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12246)).real (outputCentreEvent (paperCentres 12246))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12246

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12246) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12246) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12246)]
  norm_num [varianceMax]

end BstLean.Part262.Row12246

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12246) (hc : A1 c ∈ Eop 12246) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12246 : ℝ)) ≤ (12779617939 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12246 : ℝ) ≤ (110661647 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12246 : ℝ) + 2 * √12246 ≤ (6233661647 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12246) (hc : c ∈ BstLean.Part164.Eop2 12246) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12246 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12246) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12246 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12246) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12246).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12246) (FirstMatrix 12246))
    (h2 : c ∈ BstLean.Part164.Eop2 12246) (a : BstLean.Part161.Ix 12246) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12246

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12246) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12246) c ∈ BstLean.Part212.latitudeEvent 12246
      (ENNReal.ofReal (C / 12246))) (K : Set (Ix 12246)) :
    ∫ a in K, ((12246 : ℝ) * VR c a) ^ 2 ∂muI 12246 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12246

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12246 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12246 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12246 - 1 - 1) 80 ≤ (12402 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12246 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12402 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12246) ≤ (78 * 10 ^ 6 * ((12246 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12246 : ℝ) / 2 + 160) ≤ (4329619441 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12246 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12246 : ℝ) ^ 2 / 2 + 320 = 149965156 / 2 by norm_num,
    show (12246 : ℝ) ^ 2 / 2 + 160 = 149964836 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12246 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12246 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12246 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12246 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12246)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12246) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12246 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12246)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12246 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12246 ≤ (160 : ℝ) := by
  have hs : √(2 / (12246 : ℝ)) ≤ (12779617939 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12246 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12246 : ℝ) = 12246 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12246 : ℝ) + √12246 + gaussMomConst 80 ≤ 12366 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12246 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12246 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12246 4 +
      2 / (mA 12246 : ℝ) * frobEnvelopeSquared160 12246 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12246 4 +
      2 / (mA 12246 : ℝ) * frobEnvelopeSquared160 12246) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12246 : ℝ)) *
      operatorEnvelope160 12246 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12246 4 +
      2 / (mA 12246 : ℝ) * frobEnvelopeSquared160 12246) +
      transverseConstant160 * √(2 / (mA 12246 : ℝ)) * operatorEnvelope160 12246 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12246 4 +
      2 / (mA 12246 : ℝ) * frobEnvelopeSquared160 12246) +
      transverseConstant160 * √(2 / (mA 12246 : ℝ)) * operatorEnvelope160 12246 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12246 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12246 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12246 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12246 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12246

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12246) :=
  agentEv (paperDesignP 12246) (Energy32 12246) ∩
  agentEv (paperDesignP 12246) (freshRetainedEvent160 12246 4) ∩
  agentEv (paperDesignP 12246) (FirstMatrix 12246) ∩
  BstLean.Part164.Eop2 12246 ∩ outputCentreEvent (paperCentres 12246)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12246)).real
      (agentEv (paperDesignP 12246) (FirstMatrix 12246))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12246)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12246 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12246)).real (BstLean.Part164.Eop2 12246)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12246)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12246)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12246) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12246) hτ
  have hL := fresh_retained_charge160 (n := 12246) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12246) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12246 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12246) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12246 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12246) (hw : WINDOW (paperDesignP 12246) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12246))
    (hW : ∫ a in K, ((12246 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12246 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12246 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12246 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12246) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12246 : ℝ)) * eR c * 12246 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12246

/-! Exact rational parameters for the dimension-12247 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12247 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12247 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12247 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12247.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12247] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12247 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12247 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12247.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12247

namespace BstLean.Part262.Row12247
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

theorem energy_allowance_row : energyAllowance 12247 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12247 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12247 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12247)
  change 0 ≤ agentLayerAllowance 12247 at ha0
  have he : energyWeightAllowance 12247 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12247)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12247)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12247).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12247).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12247)) :
    ∫ a in K, fbR c a ^ k ∂muI 12247 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12247])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12247

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12247 / 12247 ≤ chi := by
  have hs : √((12247 : ℝ) * 12) ≤ (9583971 / 25000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12247}
    (hc : c ∈ outputCentreEvent (paperCentres 12247)) :
    normSq c.2.1.2 ≤ (2 / (12247 : ℝ)) * eR c * 12247 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12247 : ℝ) * normSq (bR c) * chiUp 12247 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12247)).real (outputCentreEvent (paperCentres 12247))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12247

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12247) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12247) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12247)]
  norm_num [varianceMax]

end BstLean.Part262.Row12247

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12247) (hc : A1 c ∈ Eop 12247) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12247 : ℝ)) ≤ (1597387023 / 125000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12247 : ℝ) ≤ (22133233 / 200000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12247 : ℝ) + 2 * √12247 ≤ (1246833233 / 100000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12247) (hc : c ∈ BstLean.Part164.Eop2 12247) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12247 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12247) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12247 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12247) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12247).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12247) (FirstMatrix 12247))
    (h2 : c ∈ BstLean.Part164.Eop2 12247) (a : BstLean.Part161.Ix 12247) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12247

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12247) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12247) c ∈ BstLean.Part212.latitudeEvent 12247
      (ENNReal.ofReal (C / 12247))) (K : Set (Ix 12247)) :
    ∫ a in K, ((12247 : ℝ) * VR c a) ^ 2 ∂muI 12247 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12247

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12247 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12247 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12247 - 1 - 1) 80 ≤ (12403 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12247 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12403 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12247) ≤ (78 * 10 ^ 6 * ((12247 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12247 : ℝ) / 2 + 160) ≤ (2164986497 / 250000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12247 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12247 : ℝ) ^ 2 / 2 + 320 = 149989649 / 2 by norm_num,
    show (12247 : ℝ) ^ 2 / 2 + 160 = 149989329 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12247 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12247 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12247 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12247 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12247)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12247) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12247 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12247)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12247 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12247 ≤ (160 : ℝ) := by
  have hs : √(2 / (12247 : ℝ)) ≤ (1597387023 / 125000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12247 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12247 : ℝ) = 12247 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12247 : ℝ) + √12247 + gaussMomConst 80 ≤ 12367 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12247 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12247 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12247 4 +
      2 / (mA 12247 : ℝ) * frobEnvelopeSquared160 12247 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12247 4 +
      2 / (mA 12247 : ℝ) * frobEnvelopeSquared160 12247) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12247 : ℝ)) *
      operatorEnvelope160 12247 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12247 4 +
      2 / (mA 12247 : ℝ) * frobEnvelopeSquared160 12247) +
      transverseConstant160 * √(2 / (mA 12247 : ℝ)) * operatorEnvelope160 12247 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12247 4 +
      2 / (mA 12247 : ℝ) * frobEnvelopeSquared160 12247) +
      transverseConstant160 * √(2 / (mA 12247 : ℝ)) * operatorEnvelope160 12247 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12247 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12247 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12247 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12247 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12247

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12247) :=
  agentEv (paperDesignP 12247) (Energy32 12247) ∩
  agentEv (paperDesignP 12247) (freshRetainedEvent160 12247 4) ∩
  agentEv (paperDesignP 12247) (FirstMatrix 12247) ∩
  BstLean.Part164.Eop2 12247 ∩ outputCentreEvent (paperCentres 12247)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12247)).real
      (agentEv (paperDesignP 12247) (FirstMatrix 12247))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12247)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12247 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12247)).real (BstLean.Part164.Eop2 12247)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12247)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12247)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12247) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12247) hτ
  have hL := fresh_retained_charge160 (n := 12247) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12247) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12247 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12247) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12247 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12247) (hw : WINDOW (paperDesignP 12247) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12247))
    (hW : ∫ a in K, ((12247 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12247 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12247 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12247 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12247) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12247 : ℝ)) * eR c * 12247 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12247

/-! Exact rational parameters for the dimension-12248 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12248 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12248 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12248 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12248.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12248] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12248 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12248 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12248.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12248

namespace BstLean.Part262.Row12248
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

theorem energy_allowance_row : energyAllowance 12248 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12248 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12248 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12248)
  change 0 ≤ agentLayerAllowance 12248 at ha0
  have he : energyWeightAllowance 12248 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12248)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12248)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12248).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12248).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12248)) :
    ∫ a in K, fbR c a ^ k ∂muI 12248 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12248])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12248

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12248 / 12248 ≤ chi := by
  have hs : √((12248 : ℝ) * 12) ≤ (383374491 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12248}
    (hc : c ∈ outputCentreEvent (paperCentres 12248)) :
    normSq c.2.1.2 ≤ (2 / (12248 : ℝ)) * eR c * 12248 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12248 : ℝ) * normSq (bR c) * chiUp 12248 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12248)).real (outputCentreEvent (paperCentres 12248))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12248

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12248) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12248) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12248)]
  norm_num [varianceMax]

end BstLean.Part262.Row12248

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12248) (hc : A1 c ∈ Eop 12248) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12248 : ℝ)) ≤ (3194643623 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12248 : ℝ) ≤ (110670683 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12248 : ℝ) + 2 * √12248 ≤ (6234670683 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12248) (hc : c ∈ BstLean.Part164.Eop2 12248) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12248 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12248) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12248 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12248) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12248).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12248) (FirstMatrix 12248))
    (h2 : c ∈ BstLean.Part164.Eop2 12248) (a : BstLean.Part161.Ix 12248) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12248

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12248) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12248) c ∈ BstLean.Part212.latitudeEvent 12248
      (ENNReal.ofReal (C / 12248))) (K : Set (Ix 12248)) :
    ∫ a in K, ((12248 : ℝ) * VR c a) ^ 2 ∂muI 12248 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12248

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12248 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12248 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12248 - 1 - 1) 80 ≤ (12404 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12248 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12404 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12248) ≤ (78 * 10 ^ 6 * ((12248 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12248 : ℝ) / 2 + 160) ≤ (4330326547 / 500000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12248 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12248 : ℝ) ^ 2 / 2 + 320 = 150014144 / 2 by norm_num,
    show (12248 : ℝ) ^ 2 / 2 + 160 = 150013824 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12248 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12248 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12248 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12248 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12248)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12248) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12248 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12248)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12248 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12248 ≤ (160 : ℝ) := by
  have hs : √(2 / (12248 : ℝ)) ≤ (3194643623 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12248 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12248 : ℝ) = 12248 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12248 : ℝ) + √12248 + gaussMomConst 80 ≤ 12368 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12248 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12248 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12248 4 +
      2 / (mA 12248 : ℝ) * frobEnvelopeSquared160 12248 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12248 4 +
      2 / (mA 12248 : ℝ) * frobEnvelopeSquared160 12248) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12248 : ℝ)) *
      operatorEnvelope160 12248 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12248 4 +
      2 / (mA 12248 : ℝ) * frobEnvelopeSquared160 12248) +
      transverseConstant160 * √(2 / (mA 12248 : ℝ)) * operatorEnvelope160 12248 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12248 4 +
      2 / (mA 12248 : ℝ) * frobEnvelopeSquared160 12248) +
      transverseConstant160 * √(2 / (mA 12248 : ℝ)) * operatorEnvelope160 12248 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12248 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12248 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12248 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12248 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12248

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12248) :=
  agentEv (paperDesignP 12248) (Energy32 12248) ∩
  agentEv (paperDesignP 12248) (freshRetainedEvent160 12248 4) ∩
  agentEv (paperDesignP 12248) (FirstMatrix 12248) ∩
  BstLean.Part164.Eop2 12248 ∩ outputCentreEvent (paperCentres 12248)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12248)).real
      (agentEv (paperDesignP 12248) (FirstMatrix 12248))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12248)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12248 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12248)).real (BstLean.Part164.Eop2 12248)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12248)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12248)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12248) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12248) hτ
  have hL := fresh_retained_charge160 (n := 12248) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12248) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12248 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12248) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12248 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12248) (hw : WINDOW (paperDesignP 12248) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12248))
    (hW : ∫ a in K, ((12248 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12248 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12248 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12248 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12248) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12248 : ℝ)) * eR c * 12248 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12248

/-! Exact rational parameters for the dimension-12249 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
open Real

noncomputable def eta : ℝ := 2226 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 217184 / 10 ^ 6
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
noncomputable def biasRootCap : ℝ := 610 / 10 ^ 5

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12249 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12249 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 12249 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part259.agent12249.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part259.agent12249] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 12249 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 12249 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part259.agent12249.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part262.Row12249

namespace BstLean.Part262.Row12249
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

theorem energy_allowance_row : energyAllowance 12249 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 12249 : ℝ)) ≤ (116 / 1000000 : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 12249 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 12249)
  change 0 ≤ agentLayerAllowance 12249 at ha0
  have he : energyWeightAllowance 12249 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 12249)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 12249)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 12249).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 12249).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 12249)) :
    ∫ a in K, fbR c a ^ k ∂muI 12249 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 12249])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part262.Row12249

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12249 / 12249 ≤ chi := by
  have hs : √((12249 : ℝ) * 12) ≤ (383390141 / 1000000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12249}
    (hc : c ∈ outputCentreEvent (paperCentres 12249)) :
    normSq c.2.1.2 ≤ (2 / (12249 : ℝ)) * eR c * 12249 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12249 : ℝ) * normSq (bR c) * chiUp 12249 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12249)).real (outputCentreEvent (paperCentres 12249))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part262.Row12249

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12249) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12249) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12249)]
  norm_num [varianceMax]

end BstLean.Part262.Row12249

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12249) (hc : A1 c ∈ Eop 12249) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12249 : ℝ)) ≤ (49914269 / 3906250000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12249 : ℝ) ≤ (110675201 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12249 : ℝ) + 2 * √12249 ≤ (6235175201 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12249) (hc : c ∈ BstLean.Part164.Eop2 12249) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12249 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 12249) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12249 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12249) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12249).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12249) (FirstMatrix 12249))
    (h2 : c ∈ BstLean.Part164.Eop2 12249) (a : BstLean.Part161.Ix 12249) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part262.Row12249

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
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

theorem variance_moment_row (c : Ret 12249) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 12249) c ∈ BstLean.Part212.latitudeEvent 12249
      (ENNReal.ofReal (C / 12249))) (K : Set (Ix 12249)) :
    ∫ a in K, ((12249 : ℝ) * VR c a) ^ 2 ∂muI 12249 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part262.Row12249

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212

theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h

theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, gaussMomConst_pow (by norm_num)]
  norm_num [Nat.factorial]

theorem exact_radius_sq_row : exactRadius (12249 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 12249 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (12249 - 1 - 1) 80 ≤ (12405 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((12249 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (12405 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 12249) ≤ (78 * 10 ^ 6 * ((12249 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 12249 : ℝ) / 2 + 160) ≤ (43306801 / 5000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 12249 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (12249 : ℝ) ^ 2 / 2 + 320 = 150038641 / 2 by norm_num,
    show (12249 : ℝ) ^ 2 / 2 + 160 = 150038321 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 12249 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 12249 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 12249 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 12249 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 12249)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 12249) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((12249 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 12249)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12249 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 12249 ≤ (160 : ℝ) := by
  have hs : √(2 / (12249 : ℝ)) ≤ (49914269 / 3906250000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12249 : ℝ) ≤ 112 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 12249 : ℝ) = 12249 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (12249 : ℝ) + √12249 + gaussMomConst 80 ≤ 12369 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 12249 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 12249 : ℝ)) ≤ 116 / 1000000 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 12249 4 +
      2 / (mA 12249 : ℝ) * frobEnvelopeSquared160 12249 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 12249 4 +
      2 / (mA 12249 : ℝ) * frobEnvelopeSquared160 12249) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 12249 : ℝ)) *
      operatorEnvelope160 12249 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 12249 4 +
      2 / (mA 12249 : ℝ) * frobEnvelopeSquared160 12249) +
      transverseConstant160 * √(2 / (mA 12249 : ℝ)) * operatorEnvelope160 12249 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 12249 4 +
      2 / (mA 12249 : ℝ) * frobEnvelopeSquared160 12249) +
      transverseConstant160 * √(2 / (mA 12249 : ℝ)) * operatorEnvelope160 12249 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 12249 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 12249 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 12249 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 12249 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part262.Row12249

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 12249) :=
  agentEv (paperDesignP 12249) (Energy32 12249) ∩
  agentEv (paperDesignP 12249) (freshRetainedEvent160 12249 4) ∩
  agentEv (paperDesignP 12249) (FirstMatrix 12249) ∩
  BstLean.Part164.Eop2 12249 ∩ outputCentreEvent (paperCentres 12249)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 12249)).real
      (agentEv (paperDesignP 12249) (FirstMatrix 12249))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 12249)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(12249 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 12249)).real (BstLean.Part164.Eop2 12249)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 12249)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 12249)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 12249) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 12249) hτ
  have hL := fresh_retained_charge160 (n := 12249) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 12249) hτ
  have h1 := first_matrix_charge_row
  have h2 := second_matrix_charge_row
  have hC := outputCentre_charge_row
  unfold passEvent
  repeat rw [compl_inter]
  have hEL := (measureReal_union_le _ _).trans (add_le_add hE hL)
  have hEL1 := (measureReal_union_le _ _).trans (add_le_add hEL h1)
  have hEL12 := (measureReal_union_le _ _).trans (add_le_add hEL1 h2)
  exact ((measureReal_union_le _ _).trans (add_le_add hEL12 hC)).trans (by norm_num)

theorem window_winC {n : ℕ} (hn : 1 ≤ n) (c : Ret n) (hw : WINDOW (paperDesignP n) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP n).tau0 c) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    nlinarith

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 12249 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 12249) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 12249 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 12249) (hw : WINDOW (paperDesignP 12249) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 12249))
    (hW : ∫ a in K, ((12249 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12249 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((12249 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12249 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 12249) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (12249 : ℝ)) * eR c * 12249 * chi :=
  outputCentre_row hc.2

end BstLean.Part262.Row12249
