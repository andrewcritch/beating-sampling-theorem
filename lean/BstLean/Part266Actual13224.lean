import BstLean.Part252All
import BstLean.Part262ActualInterface
import BstLean.Part266Parameters


/-! Exact rational parameters for the dimension-13224 stored-pass root.
These certificates do not assert network moment bounds. -/
namespace BstLean.Part266.Row13224
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
noncomputable def biasRootCap : ℝ := (573541 / 100000000)

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 13224 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, energyError, locationError, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 13224 chi biasFloor epsilon varianceMax
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
      BstLean.Part241.biasRoot 13224 chi biasFloor epsilon varianceMax
        energyError locationError locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ BstLean.Part266.agent13224.root := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, BstLean.Part266.agent13224] at *
  linarith

/-- A structure value records all checked scalar guards and the numerical reserve. -/
structure ScalarCertificate : Prop where
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor
  threshold_pos : 0 < epsilon - varianceMax / biasFloor
  price : BstLean.Part241.squaredPrice 13224 chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
    BstLean.Part241.biasRoot 13224 chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤
        BstLean.Part266.agent13224.root

def scalarCertificate : ScalarCertificate :=
  ⟨eta_pos, eta_lt_one, bias_floor_ge, bias_threshold_pos, stored_squared_price, root_reserve⟩

end BstLean.Part266.Row13224

namespace BstLean.Part266.Row13224
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

theorem energy_allowance_row : energyAllowance 13224 ≤ 2 / 1000 := by
  have hs : √(2 / (mA 13224 : ℝ)) ≤ ((2138859 / 20000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA]
  have ha : agentLayerAllowance 13224 ≤ (697 / 1000000 : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    linarith
  have ha0 := layerAllowance_nonneg (mA 13224)
  change 0 ≤ agentLayerAllowance 13224 at ha0
  have he : energyWeightAllowance 13224 ≤ (1395 / 1000000 : ℝ) := by
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
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg 13224)
    (by norm_num : (0 : ℝ) ≤ 7 / 5)
  norm_num at hm ⊢
  linarith

theorem full_location_moment_row (c : Ret 13224)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP 13224).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP 13224).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix 13224)) :
    ∫ a in K, fbR c a ^ k ∂muI 13224 ≤ locationNorm ^ k := by
  refine (full_location_moment (by norm_num) c hc hτ
    (energyMoment_on_event (by norm_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by linarith [energyAllowance_nonneg 13224])
  have hh := energy_allowance_row
  norm_num [locationNorm] at *
  linarith

end BstLean.Part266.Row13224

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part266.Row13224
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

theorem chi_row : chiUp 13224 / 13224 ≤ chi := by
  have hs : √((13224 : ℝ) * 12) ≤ (3186853 / 8000) := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢ <;> linarith

theorem outputCentre_row {c : Ret 13224}
    (hc : c ∈ outputCentreEvent (paperCentres 13224)) :
    normSq c.2.1.2 ≤ (2 / (13224 : ℝ)) * eR c * 13224 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 13224 : ℝ) * normSq (bR c) * chiUp 13224 at hc
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
    (retDist (paperCentres 13224)).real (outputCentreEvent (paperCentres 13224))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part266.Row13224

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part266.Row13224
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

theorem variance_pointwise_row (c : Ret 13224) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 166) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 13224) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 13224)]
  norm_num [varianceMax]

end BstLean.Part266.Row13224

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part266.Row13224
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

theorem first_matrix_row (c : Ret 13224) (hc : A1 c ∈ Eop 13224) : OpB (A1 c) 166 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (13224 : ℝ)) ≤ (12297974199 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(13224 : ℝ) ≤ (114995653 / 1000000) := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13224 : ℝ) + 2 * √13224 ≤ (6726995653 / 500000) := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 13224) (hc : c ∈ BstLean.Part164.Eop2 13224) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 13224 : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / 13224) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 13224 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 13224) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 13224).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 13224) (FirstMatrix 13224))
    (h2 : c ∈ BstLean.Part164.Eop2 13224) (a : BstLean.Part161.Ix 13224) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part266.Row13224

/-! The fresh latitude event supplies the variance moment on any kept set. -/
namespace BstLean.Part266.Row13224
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

theorem variance_moment_row (c : Ret 13224) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 6)
    (hk : agKey (paperDesignP 13224) c ∈ BstLean.Part212.latitudeEvent 13224
      (ENNReal.ofReal (C / 13224))) (K : Set (Ix 13224)) :
    ∫ a in K, ((13224 : ℝ) * VR c a) ^ 2 ∂muI 13224 ≤ varianceNorm ^ 2 := by
  refine (variance_moment_of_latitude (by norm_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm]
  linarith

end BstLean.Part266.Row13224

/-! Coarse rational enclosures suffice for the stored-pass variance moment. -/
namespace BstLean.Part266.Row13224
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

theorem exact_radius_sq_row : exactRadius (13224 - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  have hp := exactRadius_pow (d := 13224 - 1 - 1) (j := 80) (by norm_num) (by norm_num)
  have hprod : radialProduct (13224 - 1 - 1) 80 ≤ (13380 : ℝ) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((13224 - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, (13380 : ℝ) := by
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

theorem plane_envelope_row : planeEnvelope80 (mA 13224) ≤ (78 * 10 ^ 6 * ((13224 : ℝ) / 12225) ^ 2) := by
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have ht : √((mA 13224 : ℝ) / 2 + 160) ≤ (935078863 / 100000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] : (0 : ℝ) ≤ (mA 13224 : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  norm_num only [show (13224 : ℝ) ^ 2 / 2 + 320 = 174874816 / 2 by norm_num,
    show (13224 : ℝ) ^ 2 / 2 + 160 = 174874496 / 2 by norm_num] at h1 h2 ⊢
  linarith

theorem plane_squared_row : planeEnvelopeSquared160 13224 4 ≤ (12 / 5 : ℝ) := by
  have hr : (mA 13224 : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 107 / 100 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num]
    have hp : (mA 13224 : ℝ) ≤ (107 / 100 : ℝ) ^ (320 : ℕ) := by
      have h10 : (7 / 2 : ℝ) ≤ (107 / 100 : ℝ) ^ (20 : ℕ) := by norm_num
      have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] : (mA 13224 : ℝ) ≤ (7 / 2 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num)
      (Nat.cast_nonneg (mA 13224)) (by norm_num : (0 : ℝ) ≤ 107 / 100) hp
  unfold planeEnvelopeSquared160
  have hR := exact_radius_sq_row
  have hP := plane_envelope_row
  have hP0 : 0 ≤ planeEnvelope80 (mA 13224) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((13224 - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 107 / 100)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2 / 13224)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13224 : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA])
  exact h4.trans (by norm_num [mA])

theorem operator_envelope_row : operatorEnvelope160 13224 ≤ (166 : ℝ) := by
  have hs : √(2 / (13224 : ℝ)) ≤ (12297974199 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(13224 : ℝ) ≤ 115 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hh : √(mA 13224 : ℝ) = 13224 := by norm_num [mA]
  unfold operatorEnvelope160
  rw [hh]
  have hsum : (13224 : ℝ) + √13224 + gaussMomConst 80 ≤ 13348 := by
    linarith [gaussian80_le]
  exact (mul_le_mul hs hsum
    (add_nonneg (add_nonneg (by norm_num) (sqrt_nonneg _)) (gaussMomConst_nonneg 80))
    (by norm_num)).trans (by norm_num)

theorem jacobian_squared_row : latitudeJacobianSquared160 13224 4 ≤ (81 / 16 : ℝ) := by
  have hs : √(2 / (mA 13224 : ℝ)) ≤ (2138859 / 20000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  have hinner : planeEnvelopeSquared160 13224 4 +
      2 / (mA 13224 : ℝ) * frobEnvelopeSquared160 13224 ≤ (21 / 10 : ℝ) ^ 2 := by
    have hp := plane_squared_row
    norm_num [frobEnvelopeSquared160, mA] at *
    linarith
  have hr : √(planeEnvelopeSquared160 13224 4 +
      2 / (mA 13224 : ℝ) * frobEnvelopeSquared160 13224) ≤ (21 / 10 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA 13224 : ℝ)) *
      operatorEnvelope160 13224 ≤ (3 / 20 : ℝ) := by
    have h1 := mul_le_mul gaussian80_le hs (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul h1 operator_envelope_row
      (operatorEnvelope_pos160 (by norm_num)).le (by norm_num)
    exact h2.trans (by norm_num)
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 13224 4 +
      2 / (mA 13224 : ℝ) * frobEnvelopeSquared160 13224) +
      transverseConstant160 * √(2 / (mA 13224 : ℝ)) * operatorEnvelope160 13224 ≤ 9 / 4 := by
    linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 13224 4 +
      2 / (mA 13224 : ℝ) * frobEnvelopeSquared160 13224) +
      transverseConstant160 * √(2 / (mA 13224 : ℝ)) * operatorEnvelope160 13224 :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num)

theorem latitude_constant_sharp_row : freshLatitudeConstant160 13224 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num) (by norm_num : (0 : ℝ) ≤ 20000) (by norm_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num)
  have hl : latitudeCoefficient 13224 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  have hl0 : 0 ≤ latitudeCoefficient 13224 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num]
  have h1 := mul_le_mul hr jacobian_squared_row
    (latitudeJacobianSquared_pos160 (by norm_num) (by norm_num)).le (by norm_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num : (0 : ℝ) ≤ 1132 / 1000 * (81 / 16))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num)

theorem latitude_constant_row : freshLatitudeConstant160 13224 4 (55 / 100) ≤ (6 : ℝ) :=
  latitude_constant_sharp_row.trans (by norm_num)

end BstLean.Part266.Row13224

/-! Actual charged events supply four of the six stored-pass moment bounds. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part212

def passEvent : Set (Ret 13224) :=
  agentEv (paperDesignP 13224) (Energy32 13224) ∩
  agentEv (paperDesignP 13224) (freshRetainedEvent160 13224 4) ∩
  agentEv (paperDesignP 13224) (FirstMatrix 13224) ∩
  BstLean.Part164.Eop2 13224 ∩ outputCentreEvent (paperCentres 13224)

theorem passEvent_measurable : MeasurableSet passEvent :=
  ((((measurableSet_agentEv _ (measurableSet_Energy32 _)).inter
    (measurableSet_agentEv _ (measurableSet_freshRetainedEvent160 _ _))).inter
    (measurableSet_agentEv _ (firstMatrix_measurable _))).inter
    (BstLean.Part164.measurableSet_Eop2 _)).inter (outputCentreEvent_measurable _)

theorem first_matrix_charge_row :
    (retDist (paperCentres 13224)).real
      (agentEv (paperDesignP 13224) (FirstMatrix 13224))ᶜ ≤ (1 / 10 ^ 10 : ℝ) := by
  refine (firstMatrix_charge (by norm_num) (paperDesignP 13224)
    (paperDesign_tauWorld _ _ _ _)).trans ?_
  have h : exp (-(13224 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
  exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))

theorem second_matrix_charge_row :
    (retDist (paperCentres 13224)).real (BstLean.Part164.Eop2 13224)ᶜ ≤
      (373 / 10 ^ 8 : ℝ) := by
  refine (BstLean.Part164.Eop2_charge (by norm_num) (paperCentres 13224)).trans ?_
  have he : (-(25 / 2) : ℝ) = -12 + -(1 / 2) := by norm_num
  rw [he, exp_add]
  exact (mul_le_mul exp_neg12_row BstLean.Part182.exp_neg_half_le
    (exp_pos _).le (by norm_num)).trans (by norm_num)

theorem passEvent_charge :
    (retDist (paperCentres 13224)).real passEventᶜ ≤ (16 / 100000 : ℝ) := by
  have hτ := paperDesign_tauWorld (n := 13224) passF passW measurable_passF measurable_passW
  have hE := energy32_ret_charge (by norm_num) (paperDesignP 13224) hτ
  have hL := fresh_retained_charge160 (n := 13224) (q := 4)
    (by norm_num) (by norm_num) (paperDesignP 13224) hτ
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

theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 13224 4 (55 / 100) := by
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := 13224) (q := 4) (by norm_num) (by norm_num)
  have hL : 0 < latitudeCoefficient 13224 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
  positivity

theorem pass_moments_of_events (c : Ret 13224) (hw : WINDOW (paperDesignP 13224) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) (K : Set (Ix 13224))
    (hW : ∫ a in K, ((13224 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13224 ≤ energyError ^ 8)
    (hF : ∫ a in K, ((13224 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13224 ≤ locationError ^ 8) :
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

theorem pass_centre_of_events (c : Ret 13224) (hc : c ∈ passEvent) :
    normSq c.2.1.2 ≤ (2 / (13224 : ℝ)) * eR c * 13224 * chi :=
  outputCentre_row hc.2

end BstLean.Part266.Row13224

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 13224 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 13224).real (BstLean.Part211.CentreSource 13224 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 13224) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 13224 160 (6 / 1000)
  have hj := jS_160_le (n := 13224) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 13224 160 (6 / 1000) ^ 2 * 13224 /
      (((13224 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 13224 160 (6 / 1000) ^ 2 * 13224 /
      (((13224 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(13224 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(13224 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 13224) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 13224 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part266.Row13224

/-! A measurable analytic base leaves an explicit allowance for the stored-table event. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part156
open BstLean.Part159

def worldAngles : Set (Ret 13224) :=
  Ethm (paperCentres 13224) ∩ Ethp (paperCentres 13224)

theorem worldAngles_measurable : MeasurableSet worldAngles :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem worldAngles_charge :
    (retDist (paperCentres 13224)).real worldAnglesᶜ ≤ (6145 / 10 ^ 9 : ℝ) := by
  have h1 := ethm_charge (paperCentres 13224)
  have h2 := ethp_charge (by norm_num : 1 ≤ 13224) (paperCentres 13224)
  have he : exp (-(45 / 10000 * (13224 : ℝ))) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(45 / 10000 * (13224 : ℝ))) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  unfold worldAngles
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add (h1.trans he)
    (h2.trans exp_neg12_row))).trans (by norm_num)

def analyticBase : Set (Ret 13224) :=
  (passEvent ∩ agentEv (paperDesignP 13224) (DirectionError 13224) ∩
    agentEv (paperDesignP 13224) (CentreSources 13224 13224)) ∩ worldAngles

noncomputable def analyticCharge : ℝ := 549145 / 10 ^ 9
noncomputable def tableChargeAllowance : ℝ := 1052754646384 / 10 ^ 15

theorem analyticBase_measurable : MeasurableSet analyticBase :=
  ((passEvent_measurable.inter
    (measurableSet_agentEv _ (measurableSet_DirectionError _))).inter
      (measurableSet_agentEv _ (measurableSet_CentreSources (by norm_num) _))).inter
        worldAngles_measurable

theorem analyticBase_charge :
    (retDist (paperCentres 13224)).real analyticBaseᶜ ≤ analyticCharge := by
  have hτ := paperDesign_tauWorld (n := 13224) passF passW measurable_passF measurable_passW
  have hD := directionError_ret_charge (by norm_num) (paperDesignP 13224) hτ
  have hC := centreSources_ret_charge_row 13224 (paperDesignP 13224) hτ
  unfold analyticBase
  repeat rw [compl_inter]
  have hp := (measureReal_union_le _ _).trans (add_le_add passEvent_charge hD)
  have hc := (measureReal_union_le _ _).trans (add_le_add hp hC)
  exact ((measureReal_union_le _ _).trans (add_le_add hc worldAngles_charge)).trans
    (by norm_num [analyticCharge])

structure AnalyticBaseCertificate : Prop where
  measurable : MeasurableSet analyticBase
  charge : (retDist (paperCentres 13224)).real analyticBaseᶜ ≤ analyticCharge
  pass_fields : analyticBase ⊆ passEvent
  centre_sources : analyticBase ⊆
    agentEv (paperDesignP 13224) (CentreSources 13224 13224)
  direction : analyticBase ⊆ agentEv (paperDesignP 13224) (DirectionError 13224)
  angles : analyticBase ⊆ worldAngles

theorem analyticBaseCertificate : AnalyticBaseCertificate :=
  ⟨analyticBase_measurable, analyticBase_charge, fun _ h => h.1.1.1,
    fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

def baseEvent (T : Set (Ret 13224)) : Set (Ret 13224) := analyticBase ∩ T

theorem baseEvent_measurable {T : Set (Ret 13224)} (hT : MeasurableSet T) :
    MeasurableSet (baseEvent T) := analyticBase_measurable.inter hT

theorem baseEvent_charge {H T : Set (Ret 13224)}
    (hT : (retDist (paperCentres 13224)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    (retDist (paperCentres 13224)).real (H ∩ (baseEvent T)ᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ (baseEvent T)ᶜ ⊆ analyticBaseᶜ ∪ (H ∩ Tᶜ) := by
    intro c hc
    by_cases ha : c ∈ analyticBase
    · exact Or.inr ⟨hc.1, fun ht => hc.2 ⟨ha, ht⟩⟩
    · exact Or.inl ha
  refine (measureReal_mono hs (measure_ne_top _ _)).trans
    (((measureReal_union_le _ _).trans (add_le_add analyticBase_charge hT)).trans ?_)
  norm_num [analyticCharge, tableChargeAllowance, BstLean.Part249.baseChargeAllowance,
    BstLean.Part243.proposedRetainedCharge]

structure BaseEventCertificate (H T : Set (Ret 13224)) : Prop where
  measurable : MeasurableSet (baseEvent T)
  charge : (retDist (paperCentres 13224)).real (H ∩ (baseEvent T)ᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : baseEvent T ⊆ analyticBase
  table : baseEvent T ⊆ T

theorem baseEventCertificate {H T : Set (Ret 13224)} (hT : MeasurableSet T)
    (hcharge : (retDist (paperCentres 13224)).real (H ∩ Tᶜ) ≤ tableChargeAllowance) :
    BaseEventCertificate H T :=
  ⟨baseEvent_measurable hT, baseEvent_charge hcharge, fun _ h => h.1, fun _ h => h.2⟩

end BstLean.Part266.Row13224

/-! The finite-binomial centre allowance. The scalar proof follows Part253FiniteCentre;
this module has no dependency on the concurrent Part253 work. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open Real

theorem wn_upper : BstLean.Part153.wn 13224 ≤ 1.036505 := by
  have hn : (110.566721 : ℝ) ≤ √13224 := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.566721 : ℝ)) ^ 2 := by gcongr <;> linarith
    _ ≤ (1.036505 : ℝ) := by norm_num

theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

theorem deltaChi_upper : BstLean.Part154.deltaChi 13224 12 ≤ 0.0005669 := by
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  unfold BstLean.Part154.deltaChi
  simp only [Nat.cast_ofNat]
  linarith

theorem finite_centre_upper : BstLean.Part211.finiteEnergy 13224 13224 (11 / 1000) ≤
    0.008646 := by
  have ha := BstLean.Part150.alphaJ_le (by norm_num : 1000 ≤ 13224)
  have hb := BstLean.Part150.betaJ_le (by norm_num : 4096 ≤ 13224)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg 13224
  have hb0 := BstLean.Part150.betaJ_nonneg 13224
  have hw := wn_upper
  have hw0 : 0 ≤ BstLean.Part153.wn 13224 := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := deltaChi_upper
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi 13224 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn 13224 * BstLean.Part150.betaJ 13224) * 13224) ≤
      (163521459 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036505 * (81 / 1000 / 13224)) * 13224 := by gcongr <;> linarith
      _ ≤ ((163521459 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn 13224 * 13224 *
      (1 + BstLean.Part154.deltaChi 13224 12 + 2 / π) / BstLean.Part154.csC) ≤
      (187170207 / 1000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036505 * 13224 *
          (1 + 0.0005669 + 2 / 3.141592) / 1.29521 := by gcongr <;> linarith
      _ ≤ ((187170207 / 1000000) : ℝ) ^ 2 := by norm_num
  have hroot3 : √((13224 : ℝ) / BstLean.Part154.csC) ≤ (50522093 / 500000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (13224 : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
      _ ≤ ((50522093 / 500000) : ℝ) ^ 2 := by norm_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / 13224 : ℝ) * (163521459 / 1000000) +
        2 * (1792 / 10000 / 13224) * (187170207 / 1000000) +
        4 * (1 / 2.506628) * 1.036505 * (50522093 / 500000) *
          (81 / 1000 / 13224 + (1792 / 10000 / 13224) ^ 2) := by gcongr <;> linarith
    _ ≤ (0.008646 : ℝ) := by norm_num

end BstLean.Part266.Row13224

/-! Coarse centre-energy bounds suffice for the conditional fluctuation price. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part211

theorem kernel_lower_rational {q s B : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 3 / 4)
    (hs : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - q ^ 2)
    (hB : B ≤ (s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40)) /
      3.141593) : B ≤ kappa q := by
  rw [BstLean.Part182.sn_kappa_eq]
  have hroot : s ≤ √(1 - q ^ 2) := le_sqrt_of_sq_le hsq
  have ha := BstLean.Part182.sn_arcsin_ge hq hq1
  have hp := pi_gt_d6.le
  have hp' := pi_lt_d6.le
  apply hB.trans
  have hnum : 0 ≤ s + q * (3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40) := by
    positivity
  refine (div_le_div_of_nonneg_left hnum pi_pos hp').trans ?_
  apply div_le_div_of_nonneg_right _ pi_pos.le
  have hangle : 3.141592 / 2 + q + q ^ 3 / 6 + 3 * q ^ 5 / 40 ≤
      π / 2 + arcsin q := by linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus 13224 ∧
    1 ≤ gPlus 13224 ∧ gPlus 13224 ≤ 1002 / 1000 := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13224 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold gMinus gPlus
  simp only [Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem energy_g_root_guard :
    2 * √12 / (13224 : ℝ) < √(1 - 2 / (13224 : ℝ) ^ 2) := by
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (13224 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem energy_ratio_coarse : energyRatio 13224 (gMinus 13224) (54 / 100) ≤ 78 / 100 := by
  have hκ := BstLean.Part219.kappa_chord (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have hr : √(kappa (54 / 100) + 5 / (13224 : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hmean : meanRoot 13224 (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hmean0 : 0 ≤ meanRoot 13224 (54 / 100) := by unfold meanRoot; positivity
  have hg := energy_g_bounds.1
  unfold energyRatio
  rw [div_le_iff₀ (by linarith : 0 < gMinus 13224)]
  nlinarith

theorem energy_upper_coarse :
    energyUpper 13224 (gMinus 13224) (gPlus 13224)
      (finiteEnergy 13224 13224 (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  have hg := energy_g_bounds
  have hr := energy_ratio_coarse
  have hr0 : 0 ≤ energyRatio 13224 (gMinus 13224) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio 13224 (gMinus 13224) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
  have hkp := (kappa_mem (by linarith : -1 ≤ energyRatio 13224 (gMinus 13224) (54 / 100))
    (by linarith : energyRatio 13224 (gMinus 13224) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio 13224 (gMinus 13224) (54 / 100)) ≤
      89 / 100 by linarith) hkp (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus 13224 * kappa (energyRatio 13224 (gMinus 13224) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have ht : √(12 * gPlus 13224) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13224 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13224 13224 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy 13224 13224 (11 / 1000) / √13224 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13224)]
    linarith
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus 13224 * kappa (energyRatio 13224 (gMinus 13224) (54 / 100))) +
      2 * √(12 * gPlus 13224) / 13224 + finiteEnergy 13224 13224 (11 / 1000) / √13224 := by
    positivity
  nlinarith

theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot 13224 θ ∧ meanLowerRoot 13224 θ ≤ 1 := by
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
    (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ)
    (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / 13224 - 2 / (13224 : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith [hw.2])
  have hs1 : √(kappa (1 - θ) - 8 * θ / 13224 - 2 / (13224 : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  simp only [Nat.cast_ofNat]
  constructor <;> linarith

theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot 13224 θ ^ 2 / gPlus 13224) - 2 / (13224 : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus 13224 * (kappa (meanLowerRoot 13224 θ ^ 2 / gPlus 13224) -
        2 / (13224 : ℝ) ^ 2)) - 2 * √(12 * gPlus 13224) / 13224 -
        finiteEnergy 13224 13224 (11 / 1000) / √13224 := by
  have hm := energy_mean_lower_coarse hw
  have hg := energy_g_bounds
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot 13224 θ ^ 2 / gPlus 13224 := by
    rw [le_div_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13224)]
    nlinarith [hg.2.2]
  have hr1 : meanLowerRoot 13224 θ ^ 2 / gPlus 13224 ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hg.2.1] : 0 < gPlus 13224)]
    nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num
  have hκ := kappa_monotoneOn (by norm_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot 13224 θ ^ 2 / gPlus 13224 ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / 13224 ^ 2 ≤
      kappa (meanLowerRoot 13224 θ ^ 2 / gPlus 13224) - 2 / (13224 : ℝ) ^ 2 := by
    linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus 13224 *
      (kappa (meanLowerRoot 13224 θ ^ 2 / gPlus 13224) - 2 / (13224 : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num : (0 : ℝ) ≤ 65 / 100 - 2 / 13224 ^ 2)
      (by linarith [hg.1] : 0 ≤ gMinus 13224)
    linarith
  have ht : √(12 * gPlus 13224) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith [hg.2.2]⟩
  have hn : (110 : ℝ) ≤ √13224 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hfd : finiteEnergy 13224 13224 (11 / 1000) / √13224 ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < √13224)]
    linarith
  constructor <;> linarith

theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower 13224 (gMinus 13224) (gPlus 13224)
      (finiteEnergy 13224 13224 (11 / 1000)) θ := by
  have hh := (energy_lower_components hw).2
  unfold energyLower
  simp only [Nat.cast_ofNat]
  nlinarith

theorem computed_energy_eq (c : Ret 13224) (hτ : 0 < (paperDesignP 13224).tau0 c) :
    eR c = (2 / (mA 13224 : ℝ)) *
      normSq (BstLean.Part150.bT 13224 13224 (A1 c) (A2 c) c.1.2
        ((paperDesignP 13224).tau0 c)) /
      (2 / (13224 : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP 13224).tau0 c) ^ 2) := by
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP 13224).tau0 c))⁻¹ •
      BstLean.Part150.bT 13224 13224 (A1 c) (A2 c) c.1.2 ((paperDesignP 13224).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA 13224 : ℝ)) * normSq (bR c) / (2 / (13224 : ℝ)) := by
      norm_num [eR, mA]
      ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num) (A1 c) (A2 c) c.1.2 hτ

theorem centre_energy_range {c : Ret 13224}
    (hw : BstLean.Part161.WINDOW (paperDesignP 13224) c) (hc : c ∈ analyticBase) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 13224).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (13224 : ℝ) * (paperDesignP 13224).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat]
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num
  have hsrc := analyticBaseCertificate.centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource 13224 13224 c.1.2 ((paperDesignP 13224).tau0 c) :=
    hsrc.1.1
  have hg := energy_g_bounds
  have hmean := energy_mean_lower_coarse hθ
  have hlow := energy_lower_components hθ
  have h := computed_energy_on_source (by norm_num) (by norm_num) c.1.2 hw.2.1
    (by norm_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by linarith [hθ.1]) energy_g_root_guard (by linarith [hg.2.2])
    (energy_ratio_coarse.trans (by norm_num)) (by linarith [hmean.1]) hlow.1
    (by linarith [hlow.2]) hE
  rw [computed_energy_eq c hw.2.1]
  exact ⟨(energy_lower_coarse hθ).trans h.1, h.2.trans energy_upper_coarse⟩

end BstLean.Part266.Row13224

/-! Rational enclosures for the HQ fluctuation price at dimension 13224. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1614061651 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11163067 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13224 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
  have hκ := h.kappa
  have hL := h.location
  have hε := h.epsilon
  have hX := h.exponential
  have hA := h.energy
  have hD := h.displacement
  have he4 := h.energy_four
  have hd4 := h.location_four
  have he6 := h.energy_six
  have hd6 := h.location_six
  have hκ0 := hκ.1
  have hκ1 := hκ.2
  have hL0 := hL.1
  have hL1 := hL.2
  have hε0 := hε.1
  have hε1 := hε.2
  have hX0 := hX.1
  have hX1 := hX.2
  have hA0 := hA.1
  have hA1 := hA.2
  have hD0 := hD.1
  have hD1 := hD.2
  have he40 := he4.1
  have he41 := he4.2
  have hd40 := hd4.1
  have hd41 := hd4.2
  have he60 := he6.1
  have he61 := he6.2
  have hd60 := hd6.1
  have hd61 := hd6.2
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (13224 * A / 2 + D + L * √(A * D)) ≤ (1173242017 / 250000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13224 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1614061651 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13224 L e4 d4 ≤ (42518119227 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13224 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1614061651 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13224 L e6 d6 ≤ (16102812131 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13224 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1614061651 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13224 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13224 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13224 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13224 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11163067 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((1173242017 / 250000000000)) ^ 2 / 2 + ((1173242017 / 250000000000)) * ((42518119227 / 1000000000000)) ^ 2 / 6 +
      ((42518119227 / 1000000000000)) ^ 4 / 24 + ((42518119227 / 1000000000000)) ^ 2 * ((16102812131 / 250000000000)) ^ 3 / 120 +
      2187 * ((16102812131 / 250000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13224 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
  have hε := h.epsilon
  have hA := h.energy
  have hD := h.displacement
  have he6 := h.energy_six
  have hd6 := h.location_six
  have hε0 := hε.1
  have hε1 := hε.2
  have hA0 := hA.1
  have hA1 := hA.2
  have hD0 := hD.1
  have hD1 := hD.2
  have he60 := he6.1
  have he61 := he6.2
  have hd60 := hd6.1
  have hd61 := hd6.2
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((13224 : ℝ) * ((1 + 3 * ((11163067 / 500000000))) / (4 * (1 - (11163067 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11163067 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13224 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11163067 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13224 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13224 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13224

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((28748913 / 250000) : ℝ) ≤ √13224 ∧ √13224 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1520701 : ℝ) ≤ Jz 13224 ∧ 1000000 ≤ Jz 13224 := by
  have hr : ((28748913 / 250000) : ℝ) ≤ √13224 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13224 : ℝ) * √13224 ≤ (⌈(13224 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13224
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13224 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13224 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13224 : ℝ) = (⌈(13224 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1520701 : ℝ) ≤ Jz 13224 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13224 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13224) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13224 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13224 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13224 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13224 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13224 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13224 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13224) :
    (13224 : ℝ) * (283 / 100 * 166 * (d / 2) / (√13224 * √(qB 13224))) ≤
      (4459013 / 8000000000) := by
  have hden : ((28748913 / 250000) : ℝ) * (63 / 100) ≤ √13224 * √(qB 13224) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13224 : ℝ) * √(qB 13224) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13224) :
    (13224 : ℝ) * (2 * (283 / 100 * 166) ^ 2 * (d / 2) /
      (13224 * √(qB 13224))) ≤ (2276993833 / 500000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13224 : ℝ) * √(qB 13224) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13224 : ℝ) * (√13224 *
      (c1F (exp (1 / 2) / 12) (Jz 13224) * (186 / 10000) / Jz 13224)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13224)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13224 : ℝ) * (√13224 *
      (c1F (exp (1 / 2) / 12) (Jz 13224) * (186 / 10000) / Jz 13224)) =
      (13224 * (√13224 * c1F (exp (1 / 2) / 12) (Jz 13224)) * (186 / 10000)) /
        Jz 13224 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13224)]
  nlinarith

theorem row_energy_rule :
    (13224 : ℝ) * (13224 *
      (c2F (exp (1 / 2) / 12) (Jz 13224) * (186 / 10000) ^ 2 / Jz 13224)) ≤
      (1790277081 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13224)]
  nlinarith

end BstLean.Part266.Row13224

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13224) (hc : A1 c ∈ BstLean.Part153.Eop 13224) :
    BstLean.Part152.opN (A1 c) ≤ 166 := by
  refine hc.trans ?_
  have hs : √(2 / (13224 : ℝ)) ≤ (12297974199 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13224 : ℝ) + 2 * √13224 ≤ (6726995653 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13224 : ℝ) ≤ (114995653 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13224)
    (hc : A1 c ∈ BstLean.Part153.Eop 13224) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13224 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13224 * 166 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13224))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13224) (K : Set (Ix 13224)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13224 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13224 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13224) (hw : WINDOW (paperDesignP 13224) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13224)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13224) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13224 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13224 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13224 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13224 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13224) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13224)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13224)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13224

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13224) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13224 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13224) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13224) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13224 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13224 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13224 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 13224}
    (hw : WINDOW (paperDesignP 13224) c) (hc : c ∈ tableEvent) (K : Set (Ix 13224)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 13224) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13224)) : Prop where
  charge : (retDist (paperCentres 13224)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13224)} (h : TablePayment H) :
    (retDist (paperCentres 13224)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13224)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13224

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13224) (i : Fin 4) (a : Ix 13224) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13224) (a : Ix 13224) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13224) : Prop where
  moment : ∀ i, MomentBound (muI 13224) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13224} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13224) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part266.Row13224

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 13224) : Prop where
  location : LBound (muI 13224) 12
    (fun a => conditionalVariance (stdGauss (Fin (13224 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13224) 12
    (fun a => conditionalVariance (stdGauss (Fin (13224 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13224) (hw : WINDOW (paperDesignP 13224) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13224 4 (55 / 100) /
      (13224 : ℝ) / ((13224 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13224

/-! The dimension-13224 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13224) (wl ws : ℝ) : SplitData 13224 :=
  BstLean.Part162.dPaper (paperDesignP 13224) c wl ws
    (√(2 / (13224 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13224 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13224 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13224) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13224) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13224 : ℝ)) * eR c * 13224 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13224) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13224 - 1)))
    (rowSplit c wl ws).good a ∂muI 13224 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13224) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13224 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13224) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13224 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13224) c (rowSplit c wl ws),
    hellG2 13224 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13224 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13224} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13224} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13224 t c BstLean.Part266.agent13224.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 13224} (R : RootSource t c) :
    |√(QStand (paperDesignP 13224) t c) - √(qTilde (paperDesignP 13224) t c)| ≤
      BstLean.Part266.agent13224.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13224

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13224 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13224) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13224 : ℝ) * (13224 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13224) /
    ((13224 : ℝ) * (13224 - 1 - 2 * q)))

theorem rotation_positive (q : ℕ) : 0 < rotationConstant q := by
  have ho : 0 < oddMoment q := by
    unfold oddMoment
    exact Finset.prod_pos (fun j _ => by positivity)
  unfold rotationConstant
  split_ifs
  · norm_num
  · exact mul_pos (by positivity) (Real.rpow_pos_of_pos ho _)

theorem locationMomentBudget_pos {c : Ret 13224} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13224}
    (hw : WINDOW (paperDesignP 13224) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13224) c a v - lbar (paperDesignP 13224) c a| ^ (2 * q)
      ∂stdGauss (Fin (13224 - 1)) ∂muI 13224 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13224)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13224}
    (hw : WINDOW (paperDesignP 13224) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13224) c a v - gbar (paperDesignP 13224) c a| ^ (2 * q)
      ∂stdGauss (Fin (13224 - 1)) ∂muI 13224 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13224)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13224) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13224}
    (hw : WINDOW (paperDesignP 13224) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13224 - 1))).real
      {v | sgA (paperDesignP 13224) c a v < √(2 / (13224 : ℝ) * mixtureFloor)}
      ∂muI 13224 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13224 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13224 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13224) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13224

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13224 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13224)
    (p : Ix 13224 × (Fin (13224 - 1) → ℝ)) :
    sgA (paperDesignP 13224) c p.1 p.2 ^ 2 ≤
      (2 / (13224 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13224).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13224) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13224 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13224 : ℝ) * _ ≤ 2 / 13224 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13224)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13224}
    (hw : WINDOW (paperDesignP 13224) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13224) c a v ^ 8
      ∂stdGauss (Fin (13224 - 1)) ∂muI 13224 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13224).prod (stdGauss (Fin (13224 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13224) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13224) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13224 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13224) c p.1 p.2)
      (√(2 / (13224 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13224)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13224 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13224) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13224}
    (hw : WINDOW (paperDesignP 13224) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13224) c a v -
      ∫ w, sA (paperDesignP 13224) c a w ∂stdGauss (Fin (13224 - 1))) ^ 2
      ∂stdGauss (Fin (13224 - 1))) ^ 2 ∂muI 13224 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13224) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13224

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem latitude_mass_of_MASS {n : ℕ} (hn : 2 ≤ n) (D : Design n) (c : Ret n)
    (hc : c.1.2 ≠ 0) (hτ : 0 < D.tau0 c) {d β : ℝ} (hd : 0 ≤ d)
    (hM : MASS_at D c d β) :
    ∫ a, (stdGauss (Fin (n - 1))).real
      {v | sgA D c a v < √(2 / (n : ℝ) * d)} ∂muI n ≤ β / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [mass_eq_stand hn D c hc hτ]
  have hs : {ξ : Fin n → ℝ | sigX D c (sphPt (c.1.2 + D.tau0 c • ξ)) <
      √(2 / (n : ℝ) * d)} =
      {ξ | 2 / (mA n : ℝ) * normSq (res (D.bA c.1 c.2.1.1) (hStand D c ξ)) <
        2 / (n : ℝ) * d} := by
    ext ξ
    simp only [Set.mem_setOf_eq]
    change √(2 / (mA n : ℝ)) * √(normSq (res (D.bA c.1 c.2.1.1)
      (hStand D c ξ))) < _ ↔ _
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_lt_sqrt_iff (mul_nonneg (by positivity) (normSq_nonneg _))
  rw [hs, le_div_iff₀ hnR, mul_comm]
  exact hM

theorem low_mass_of_interfaces {c : Ret 13224}
    (hw : WINDOW (paperDesignP 13224) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13224).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13224) c M H xi)
    (hE : centreEnergy (paperDesignP 13224) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13224 : ℝ))))
    (hprice : massBound 13224 M H xi E u mixtureFloor ≤ 13224 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13224 - 1))).real
      {v | sgA (paperDesignP 13224) c a v < √(2 / (13224 : ℝ) * mixtureFloor)}
        ∂muI 13224 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13224).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13224) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13224) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13224)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13224

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13224) : ℝ :=
  (latitudeC / eR c) / ((13224 : ℝ) * (13224 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13224) / ((13224 : ℝ) * (13224 - 3))

theorem location_variance_on_event {c : Ret 13224}
    (hw : WINDOW (paperDesignP 13224) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13224) c a v - lbar (paperDesignP 13224) c a) ^ 2
      ∂stdGauss (Fin (13224 - 1))) ^ 2 ∂muI 13224 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13224)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13224}
    (hw : WINDOW (paperDesignP 13224) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13224) c a v - gbar (paperDesignP 13224) c a) ^ 2
      ∂stdGauss (Fin (13224 - 1))) ^ 2 ∂muI 13224 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13224)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13224}
    (hw : WINDOW (paperDesignP 13224) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13224 - 1))).real
      {v | sgA (paperDesignP 13224) c a v < √(2 / (13224 : ℝ) * mixtureFloor)}
      ∂muI 13224 ≤ lowMassBudget) :
    LatMom (paperDesignP 13224) c (√(2 / (13224 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13224

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem rotation_four : rotationConstant 4 ≤ 285 / 100 := by
  apply rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

theorem rotation_six : rotationConstant 6 ≤ 35 / 10 := by
  apply rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

theorem rotation_twelve : rotationConstant 12 ≤ 48 / 10 := by
  apply rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

theorem location_budget_cap {c : Ret 13224} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13224 : ℝ) * (13224 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13224 : ℝ) * (13224 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13224 : ℝ) /
      ((13224 : ℝ) * (13224 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13224 : ℝ) * (13224 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13224 ≤ (2 * (16 / 5) / 13224 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13224} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (124471301 / 250000000000) ∧
    locationMomentBudget c 6 ≤ (19110329 / 31250000000) ∧
    locationMomentBudget c 12 ≤ (419525797 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4742839441 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (5825421369 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (7992780187 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13224} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30505039 / 1000000000000000) ∧ residualVarianceBudget ≤ (2768153 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13224 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4742839441 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13224

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13224 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13224) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13224) : ℝ :=
  exp (hqKappa * (13224 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((1439953 / 250000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5759813 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13224} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (419525797 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (7992780187 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (7992780187 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((7992780187 / 250000000000000) : ℝ) / ((1439953 / 250000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11163067 / 500000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13224} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1614061651 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((419525797 / 125000000000))) / ((1439953 / 250000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13224} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13224 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13224 * ((11163067 / 500000000) : ℝ) ^ 2 / 2 + ((1614061651 / 1000000000)) ^ 2 * (1 + (11163067 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13224 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13224 * ((11163067 / 500000000)) ^ 2 / 2 + ((1614061651 / 1000000000)) ^ 2 * (1 + (11163067 / 500000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((1439953 / 250000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (174580507 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (15239171371 / 125000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13224

/-! The realized moment supplies meet the rational HQ price bounds. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180

noncomputable def hqEnergy : ℝ :=
  cVw splitResidualWidth rowSigma * ((1 - eta)⁻¹ * residualVarianceBudget)
noncomputable def hqDisplacement (c : Ret 13224) : ℝ :=
  hqCentreCap / rowSigma ^ 2 * ((1 - eta)⁻¹ * locationVarianceBudget c)
noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw splitResidualWidth rowSigma *
    ((iotaP eta p + c2η eta + c3η eta splitResidualWidth rowSigma) * residualMomentBudget (p / 2))
noncomputable def hqLocationMoment (c : Ret 13224) (p : ℕ) : ℝ :=
  √hqCentreCap / rowSigma * ((iotaP eta p + c2η eta) * locationMomentBudget c (p / 2))

theorem hq_price_certificate {c : Ret 13224} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds hqKappa (hqLocation c) hqEpsilon (hqExp c) hqEnergy
      (hqDisplacement c) (hqEnergyMoment 8) (hqLocationMoment c 8)
      (hqEnergyMoment 12) (hqLocationMoment c 12) := by
  obtain ⟨hV0, hV1⟩ := cV_width_bounds
  obtain ⟨hE0, hE1⟩ := cE_width_bounds
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := c3_eta_bounds
  obtain ⟨hVl, hVs⟩ := variance_budgets_row he
  obtain ⟨hl4, hl6, hl12⟩ := location_budgets_row he
  obtain ⟨hs4, hs6, hs12⟩ := residual_budgets_row
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVs0 : 0 ≤ residualVarianceBudget :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num)) (by norm_num)
  have hl40 := (locationMomentBudget_pos he0 (by norm_num : 4 ≤ 12)).le
  have hl60 := (locationMomentBudget_pos he0 (by norm_num : 6 ≤ 12)).le
  have hs40 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hs60 := (residualMomentBudget_pos (by norm_num : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta]
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap]
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hk := hq_kappa_bounds
  have hloc := hq_location_bounds he
  have heps := hq_epsilon_bounds
  have hexp := hq_exponential_bounds he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw splitResidualWidth rowSigma = v at *
  generalize cEw splitResidualWidth rowSigma = w at *
  generalize residualVarianceBudget = vs at *
  generalize locationVarianceBudget c = vl at *
  generalize residualMomentBudget 4 = s4 at *
  generalize residualMomentBudget 6 = s6 at *
  generalize locationMomentBudget c 4 = l4 at *
  generalize locationMomentBudget c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta splitResidualWidth rowSigma = c3 at *
  generalize rowSigma = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear * - hV0 hV1 hE0 hE1 hi80 hi81 hi120 hi121 hc20 hc21 hc30 hc31 hVl hVs hVl0 hVs0 hl4 hl6 hs4 hs6 hl40 hl60 hs40 hs60 hinv hinv0 hσ0 hσ hca0 hroot0 hroot
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((15239171371 / 125000) : ℝ) * ((1003 / 1000) * ((2768153 / 1000000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ (1918 / 1000 : ℝ) / ((1439953 / 250000000)) ^ 2 * ((1003 / 1000) * ((30505039 / 1000000000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((174580507 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((4742839441 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1439953 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((124471301 / 250000000000))) := by
        gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ ((174580507 / 500000) : ℝ) * ((1001 / 1000 + 52 / 1000 + 31 / 10000) * ((5825421369 / 1000000000000000))) := by gcongr
      _ ≤ _ := by norm_num
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / ((1439953 / 250000000)) * ((1001 / 1000 + 52 / 1000) * ((19110329 / 31250000000))) := by
        gcongr
      _ ≤ _ := by norm_num

noncomputable def splitRemovedBudget (c : Ret 13224) : ℝ :=
  Bpap (splitLocationWidth c) splitResidualWidth (locationMomentBudget c 12)
    (residualMomentBudget 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret 13224} (he : 0 < eR c) :
    0 ≤ splitRemovedBudget c ∧ splitRemovedBudget c ≤ removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

theorem hq_displacement_root {c : Ret 13224} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap 13224 B hqCentreCap (locationVarianceBudget c) scaleVarianceBudget eta rowSigma) ≤
      270 / 10 ^ 6 := by
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num,
    hB.trans (by norm_num [removalBudget, eta])⟩
  have hVl := (variance_budgets_row he).1
  have hVS := scale_variance_budget_row
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have he0 : 0 < eR c := by linarith
  have hVl0 : 0 ≤ locationVarianceBudget c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num)
  have hVS0 : 0 ≤ scaleVarianceBudget :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := sigma_pos
  have hσ := sigma_bounds.1
  have hη0 : 0 < 1 - eta := by norm_num [eta]
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  unfold Dpap hqCentreCap
  generalize locationVarianceBudget c = vl at *
  generalize scaleVarianceBudget = vs at *
  generalize rowSigma = sigma at *
  clear * - hroot hVl hVS hVl0 hVS0 hσ0 hσ hη0 hB0
  calc
    _ ≤ (247 / 10 ^ 8 : ℝ) * ((1918 / 1000) * ((30505039 / 1000000000000000)) /
        (2 * (1 - eta) * ((1439953 / 250000000)) ^ 2) +
        13224 * (188 / 10 ^ 16) / (8 * (1 - eta) ^ 2 * ((1439953 / 250000000)) ^ 4)) := by
      gcongr <;> norm_num
    _ ≤ _ := by norm_num [eta]

theorem hq_root_price {c : Ret 13224} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP 13224) c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (13224 - 1))).real
      {v | sgA (paperDesignP 13224) c a v < rowSigma} ∂BstLean.Part161.muI 13224 ≤ lowMassBudget) :
    rootFLH (splitLocationWidth c) splitResidualWidth eta hqCentreCap (85 / 100) (64 / 100)
      (latitudeMoments hw (by linarith) hc hmass) ≤ 24 / 10000 := by
  have he0 : 0 < eR c := by linarith
  have hB := splitRemovedBudget_bounds he0
  have hr : √(2 * (1 + eta⁻¹) * splitRemovedBudget c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta])
  have hm := fluct_mixture_root (hq_price_certificate he)
  have hd := hq_displacement_root he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * splitRemovedBudget c) +
    √(priceC hqKappa 13224 (hqLocation c) hqEpsilon (hqExp c) hqEnergy (hqDisplacement c)
      (hqEnergyMoment 8) (hqLocationMoment c 8) (hqEnergyMoment 12) (hqLocationMoment c 12) / 4 +
      3 / 4 * cubP 13224 hqEpsilon (85 / 100) (64 / 100) hqEnergy (hqDisplacement c)
        (hqEnergyMoment 12) (hqLocationMoment c 12)) +
      √(Dpap 13224 (splitRemovedBudget c) hqCentreCap (locationVarianceBudget c)
        scaleVarianceBudget eta rowSigma) ≤ _
  linarith

end BstLean.Part266.Row13224

/-! A root structure using the realized latitude moments and the HQ price. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part29 (stdGauss)

def LowResidualMass (c : Ret 13224) : Prop :=
  ∫ a, (stdGauss (Fin (13224 - 1))).real
    {v | sgA (paperDesignP 13224) c a v < rowSigma} ∂muI 13224 ≤ lowMassBudget

noncomputable def hqSplit (c : Ret 13224) : SplitData 13224 :=
  rowSplit c (splitLocationWidth c) splitResidualWidth

theorem hq_output_bounds {c : Ret 13224}
    (hw : WINDOW (paperDesignP 13224) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 13224)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  have he := centre_energy_range hw ha
  have hpass := analyticBaseCertificate.pass_fields ha
  have hcap := pass_centre_of_events c hpass
  have hb : 0 < normSq ((paperCentres 13224).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by linarith
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1) (fun h => by norm_num at h)
  refine ⟨hp hb, ?_⟩
  norm_num [chi, hqCentreCap] at hcap ⊢
  linarith [he.2]

theorem hq_fluctuation {c : Ret 13224} (t : ℝ)
    (hw : WINDOW (paperDesignP 13224) c) (ha : c ∈ analyticBase)
    (hp : c ∈ positiveOutputEvent (paperCentres 13224)) (hm : LowResidualMass c) :
    FLUCT_hyp (paperDesignP 13224) t c (hqSplit c) (24 / 10000) := by
  have he := (centre_energy_range hw ha).1
  have he0 : 0 < eR c := by linarith
  have hc := analyticBaseCertificate.pass_fields ha
  have ho := hq_output_bounds hw ha hp
  have hs := split_width_bounds he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num) (paperDesignP 13224) c t
    hs.1 hs.2.2.1 sigma_pos eta_pos eta_lt_one ho.1 ho.2
    (by change hqEpsilon < 1; linarith [hq_epsilon_bounds.2] :
      eps0 splitResidualWidth rowSigma < 1)
    (latitudeMoments hw he0 hc hm) (by norm_num : (0 : ℝ) < 85 / 100)
    (by norm_num) (by norm_num : (0 : ℝ) < 64 / 100) (by norm_num)
    (hq_root_price he hw hc hm)

theorem hq_passes {c : Ret 13224} (hw : WINDOW (paperDesignP 13224) c)
    (ha : c ∈ analyticBase) (ht : c ∈ tableEvent) :
    BstLean.Part241.PassInputs c (hqSplit c) chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm := by
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hc := analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP 13224) c (hqSplit c)) :=
    measurableSet_keptSet _ (hqSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 13224) c (hqSplit c) ⊆ bulkIx (paperDesignP 13224) c :=
    fun _ h => h.1
  have htab := stored_table_moments c hw hc hK hsub
    (exactTableMoments_of_event hw ht _)
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (sqrt_nonneg _) he bias_floor_ge (by norm_num [epsilon]) bias_threshold_pos
    (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    (pass_centre_of_events c hc)
    (pass_moments_of_events c hw he hc _ htab.1 htab.2)

/-- Only the low-mass inequality remains pointwise; the table payment is a separate obligation. -/
noncomputable def hqRootInputs {c : Ret 13224} (t : ℝ)
    (hw : WINDOW (paperDesignP 13224) c) (ha : c ∈ analyticBase)
    (ht : c ∈ tableEvent) (hp : c ∈ positiveOutputEvent (paperCentres 13224))
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 13224 t c BstLean.Part266.agent13224.root where
  split := hqSplit c
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := 0
  mix := 24 / 10000
  displacement := 0
  window := hw
  passes := hq_passes hw ha ht
  fluctuation := by simpa using hq_fluctuation t hw ha hp hm
  scalar := by
    have h := stored_bias_root
    norm_num [biasRootCap, BstLean.Part266.agent13224] at h ⊢
    linarith

end BstLean.Part266.Row13224

/-! The root constructor after the charged pass events have supplied their fields. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

/-- The remaining numerical bounds concern the actual tables and original conditional mixture.
No field in this record asserts the replacement conclusion. -/
structure RootRemainder (t : ℝ) (c : Ret 13224) where
  wl : ℝ
  ws : ℝ
  energy_table : ∫ a in keptIx (paperDesignP 13224) c (rowSplit c wl ws),
    ((13224 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13224 ≤ energyError ^ 8
  location_table : ∫ a in keptIx (paperDesignP 13224) c (rowSplit c wl ws),
    ((13224 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13224 ≤ locationError ^ 8
  removal : ∫ a, removed (stdGauss (Fin (13224 - 1)))
    (rowSplit c wl ws).good a ∂muI 13224 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13224) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13224 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13224) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13224 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13224) c (rowSplit c wl ws),
    hellG2 13224 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13224 ≤ displacementBudget

noncomputable def rootSource_of_events {t : ℝ} {c : Ret 13224}
    (hw : WINDOW (paperDesignP 13224) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) : RootSource t c where
  wl := R.wl
  ws := R.ws
  window := hw
  energy_pos := he
  centre := pass_centre_of_events c hc
  moments := pass_moments_of_events c hw he hc _ R.energy_table R.location_table
  removal := R.removal
  mixture := R.mixture
  displacement := R.displacement

/-- This structure value can be passed directly to Part243 once the five remainder bounds hold. -/
noncomputable def rootInputs_of_events {t : ℝ} {c : Ret 13224}
    (hw : WINDOW (paperDesignP 13224) c) (he : 0 < eR c)
    (hc : c ∈ passEvent) (R : RootRemainder t c) :
    BstLean.Part243.RootInputs 13224 t c BstLean.Part266.agent13224.root :=
  rootInputs (rootSource_of_events hw he hc R)

end BstLean.Part266.Row13224

/-! The analytic base has an unconditional payment. The null output-centre
exception adds no payment. This event does not supply the stored-table bounds. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169

def paidBaseEvent : Set (Ret 13224) :=
  analyticBase ∩ positiveOutputEvent (paperCentres 13224)

theorem paidBaseEvent_measurable : MeasurableSet paidBaseEvent :=
  analyticBase_measurable.inter (positiveOutputEvent_measurable _)

theorem paidBaseEvent_charge :
    (retDist (paperCentres 13224)).real paidBaseEventᶜ ≤ analyticCharge := by
  unfold paidBaseEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add analyticBase_charge (positiveOutputEvent_charge (by norm_num) _))).trans
      (by simp)

structure PaidBaseCertificate (H : Set (Ret 13224)) : Prop where
  measurable : MeasurableSet paidBaseEvent
  charge : (retDist (paperCentres 13224)).real (H ∩ paidBaseEventᶜ) ≤
    BstLean.Part249.baseChargeAllowance
  analytic : paidBaseEvent ⊆ analyticBase
  positive_output : paidBaseEvent ⊆ positiveOutputEvent (paperCentres 13224)

theorem paidBaseCertificate (H : Set (Ret 13224)) : PaidBaseCertificate H := by
  refine ⟨paidBaseEvent_measurable, ?_, fun _ h => h.1, fun _ h => h.2⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    paidBaseEvent_charge).trans (by
      norm_num [analyticCharge, BstLean.Part249.baseChargeAllowance,
        BstLean.Part243.proposedRetainedCharge])

end BstLean.Part266.Row13224

/-! The HQ route reduces the five root remainder inputs to one residual-mass
bound. The actual table payment and local frame remain separate inputs. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def hqBaseEvent : Set (Ret 13224) :=
  proposedBaseEvent ∩ positiveOutputEvent (paperCentres 13224)

theorem hqBaseEvent_measurable : MeasurableSet hqBaseEvent :=
  proposedBaseEvent_measurable.inter (positiveOutputEvent_measurable _)

theorem hqBaseEvent_charge {H : Set (Ret 13224)} (h : TablePayment H) :
    (retDist (paperCentres 13224)).real (H ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := by
  have hs : H ∩ hqBaseEventᶜ ⊆
      (H ∩ proposedBaseEventᶜ) ∪ (positiveOutputEvent (paperCentres 13224))ᶜ := by
    intro c hc
    by_cases hb : c ∈ proposedBaseEvent
    · exact Or.inr fun hp => hc.2 ⟨hb, hp⟩
    · exact Or.inl ⟨hc.1, hb⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (proposedBaseEvent_charge h)
        (positiveOutputEvent_charge (by norm_num) _)))).trans (by simp)

/-- All stored-pass, fluctuation, split, window and reserve fields are proved
internally from membership and the single low-residual-mass bound. -/
noncomputable def hqRootInputs_on_base {c : Ret 13224} (t : ℝ)
    (hw : WINDOW (paperDesignP 13224) c) (hc : c ∈ hqBaseEvent)
    (hm : LowResidualMass c) :
    BstLean.Part243.RootInputs 13224 t c BstLean.Part266.agent13224.root :=
  hqRootInputs t hw hc.1.1 hc.1.2 hc.2 hm


end BstLean.Part266.Row13224

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 13224) (a : Ix 13224) : Fin (Js 13224) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 13224) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 13224) : Measure (Fin (Js 13224)) :=
  (muI 13224).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 13224) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 13224) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 13224) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 13224)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 13224) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 13224)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 13224)
    (M : Matrix (Fin (mA 13224)) (Fin (mA 13224)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 13224) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 13224) (mA 13224) (tA 13224) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 13224) (mA 13224) (tA 13224)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 13224) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part266.Row13224

/-! A first-layer variance payment from dimension 13224. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

lemma variance_alg_low {M D q X m : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hm : 0 < m) (hq : 3969 / 10000 ≤ q)
    (hX : 90 / 100 * M * D / m ≤ X) :
    17 / (100 * m) ≤ 2 / M * (q / (4 * D)) * X := by
  have e : 2 / M * (q / (4 * D)) * X = q * X / (2 * M * D) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [div_le_iff₀ hm] at hX
  have hX0 : 0 ≤ X := by
    have : 0 ≤ 90 / 100 * M * D := by positivity
    nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) (mul_nonneg hX0 hm.le)]

lemma variance_alg_up {M D q Y m : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hm : 0 < m) (hq0 : 0 ≤ q) (hq : q ≤ 61 / 100) (hY0 : 0 ≤ Y)
    (hY : Y ≤ 210 / 100 * M * D / m) :
    2 / M * (q / D) * Y ≤ 26 / (10 * m) := by
  have e : 2 / M * (q / D) * Y = 2 * q * Y / (M * D) := by field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [le_div_iff₀ hm] at hY
  nlinarith [mul_le_mul hq hY (by positivity) (by norm_num : (0 : ℝ) ≤ 61 / 100),
    mul_nonneg hq0 (mul_nonneg hY0 hm.le)]

lemma variance_alg_trace {M D q Y m : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hm : 0 < m) (hq0 : 0 ≤ q)
    (hY : Y ≤ 210 / 100 * M * D / m) :
    2 / M * (q / D) * Y ≤ 42 / (10 * m) * q := by
  calc
    _ ≤ 2 / M * (q / D) * (210 / 100 * M * D / m) :=
      mul_le_mul_of_nonneg_left hY (by positivity)
    _ = _ := by field_simp; ring

lemma variance_cheby_num {m M D B k : ℝ} (hm : 13224 ≤ m) (hM : M = m ^ 2)
    (hD : D = m - 1) (hB : B ≤ m ^ 2 + 2 * m) (hk : 5 / 100 ≤ k) :
    M * B / (k * M * D) ^ 2 ≤ 5 / 10 ^ 6 := by
  have hD0 : 12224 ≤ D := by rw [hD]; linarith
  have hM0 : 0 < M := by rw [hM]; positivity
  have hk0 : 0 < k := by linarith
  rw [div_le_iff₀ (by positivity)]
  have h1 : M * B ≤ 11 / 10 * M ^ 2 := by
    rw [hM]
    have hB2 : B ≤ 11 / 10 * m ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left hB2 (sq_nonneg m)
    nlinarith
  have hk2 : 25 / 10000 ≤ k ^ 2 := by nlinarith
  have hD2 : 12224 ^ 2 ≤ D ^ 2 := by nlinarith
  have h2 : 11 / 10 ≤ 5 / 10 ^ 6 * (k ^ 2 * D ^ 2) := by
    nlinarith [mul_le_mul hk2 hD2 (by norm_num) (by positivity)]
  calc M * B ≤ 11 / 10 * M ^ 2 := h1
    _ ≤ 5 / 10 ^ 6 * (k ^ 2 * D ^ 2) * M ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg M)
    _ = 5 / 10 ^ 6 * (k * M * D) ^ 2 := by ring

theorem node_trace_charge (hn : 13224 ≤ n) {wr : WRet n} (hw : windowW wr)
    (hgeo : ∀ g < Js n, 0 ≤ nodeS (mkR wr (0, 0)) g ∧
      3969 / 10000 ≤ 1 - nodeS (mkR wr (0, 0)) g ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g ^ 2 ≤ 61 / 100) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real {A₁ | ∃ g < Js n,
      vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g) < 17 / (100 * (n : ℝ)) ∨
      42 / (10 * (n : ℝ)) * (1 - nodeS (mkR wr (A₁, 0)) g ^ 2) < vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g)} ≤ 1 / 10 ^ 5 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (13224 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hc : wr.2 ≠ 0 := sg_wr_ne hn1 hw
  set u : Fin n → ℝ := uHat (mkR wr ((0 : AHid n).1, 0)) with hud
  have hu : normSq u = 1 := BstLean.Part161.normSq_uHat (c := mkR wr ((0 : AHid n).1, 0)) hc
  set M : ℝ := ((mA n : ℕ) : ℝ) with hMd
  set D : ℝ := ((n - 1 : ℕ) : ℝ) with hDd
  have hMe : M = (n : ℝ) ^ 2 := by rw [hMd]; unfold mA; push_cast; ring
  have hDe : D = (n : ℝ) - 1 := by rw [hDd, Nat.cast_sub hn1]; simp
  have hM : 0 < M := by rw [hMe]; positivity
  have hD : 0 < D := by rw [hDe]; linarith
  -- the deterministic inclusion
  set T : Set (Matrix (Fin (mA n)) (Fin n) ℝ) := {A | ∑ i, sg_phi1 u (A i) < 90 / 100 * M * D / n ∨
    210 / 100 * M * D / n < ∑ i, sg_phi2 u (A i)} with hT
  have hsub : {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | ∃ g < Js n,
      vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g) < 17 / (100 * (n : ℝ)) ∨
      42 / (10 * (n : ℝ)) * (1 - nodeS (mkR wr (A₁, 0)) g ^ 2) < vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g)} ⊆ T := by
    rintro A ⟨g, hg, hbad⟩
    set c := mkR wr (A, 0)
    have hc' : c.1.2 ≠ 0 := hc
    obtain ⟨hs0, hq, hqU⟩ := hgeo g hg
    change 0 ≤ nodeS c g at hs0
    change 3969 / 10000 ≤ 1 - nodeS c g ^ 2 at hq
    change 1 - nodeS c g ^ 2 ≤ 61 / 100 at hqU
    set s := nodeS c g
    have hs1 : s ^ 2 ≤ 1 := by linarith
    have hL := sg_vsig2_lower (by omega) c hc' hs0 hs1
    have hU := sg_vsig2_upper (by omega) c hc' hs1
    have e1 : ∑ i, (if 0 ≤ sg_z (uHat c) (A1 c i) then
        normSq (A1 c i) - sg_z (uHat c) (A1 c i) ^ 2 else 0) = ∑ i, sg_phi1 u (A i) := rfl
    have e2 : ∑ i, (normSq (A1 c i) - sg_z (uHat c) (A1 c i) ^ 2) = ∑ i, sg_phi2 u (A i) := rfl
    rw [e1] at hL; rw [e2] at hU
    rcases hbad with h | h
    · left
      by_contra hX
      push_neg at hX
      have := variance_alg_low hM hD hn0 hq hX
      linarith
    · right
      by_contra hY
      push_neg at hY
      have hY0 : 0 ≤ ∑ i, sg_phi2 u (A i) := Finset.sum_nonneg fun i _ => sg_phi2_nonneg hu _
      have := variance_alg_trace (q := 1 - s ^ 2) hM hD hn0 (by linarith) hY
      linarith
  have hTm : MeasurableSet T := by
    have h1 : Measurable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => ∑ i, sg_phi1 u (A i)) :=
      Finset.measurable_sum _ fun i _ => (sg_meas_phi1 u).comp (measurable_pi_apply i)
    have h2 : Measurable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => ∑ i, sg_phi2 u (A i)) :=
      Finset.measurable_sum _ fun i _ => (sg_meas_phi2 u).comp (measurable_pi_apply i)
    exact (measurableSet_lt h1 measurable_const).union (measurableSet_lt measurable_const h2)
  set μ := Measure.pi fun _ : Fin (mA n) => stdGauss (Fin n) with hμ
  set γ : ℝ := 2 / (n : ℝ) with hγ
  have hγ0 : 0 < γ := by positivity
  have hsγ : 0 < √γ := Real.sqrt_pos.mpr hγ0
  have hsγ2 : √γ ^ 2 = γ := Real.sq_sqrt hγ0.le
  set f : (Fin (mA n) → Fin n → ℝ) → Matrix (Fin (mA n)) (Fin n) ℝ :=
    fun G => Matrix.of fun i j => √γ * G i j with hfd
  have hf : Measurable f := by
    have hc : Continuous (fun G : Fin (mA n) → Fin n → ℝ => fun i j => √γ * G i j) := by fun_prop
    exact hc.measurable
  have hG : gaussMat (mA n) n γ = μ.map f := BstLean.Part167.gaussMat_rows γ
  have hrow : ∀ G i, f G i = √γ • G i := fun G i => by funext j; rfl
  obtain ⟨-, i1sq, b1⟩ := sg_int_bdd (sg_meas_phi1 u) (sg_phi1_nonneg hu) (sg_phi1_le hu)
  obtain ⟨-, i2sq, b2⟩ := sg_int_bdd (sg_meas_phi2 u) (sg_phi2_nonneg hu) (sg_phi2_le u)
  have hE1 := sg_int_phi1 hu
  have hE2 := (sg_int_phi2 hu).2
  set t₁ : ℝ := 5 / 100 * M * D
  set t₂ : ℝ := 5 / 100 * M * D
  have ht₁ : 0 < t₁ := by positivity
  have ht₂ : 0 < t₂ := by positivity
  have hpre : f ⁻¹' T ⊆ {G | t₁ ≤ |∑ i, sg_phi1 u (G i) - (mA n : ℕ) * ∫ g, sg_phi1 u g ∂stdGauss (Fin n)|} ∪
      {G | t₂ ≤ |∑ i, sg_phi2 u (G i) - (mA n : ℕ) * ∫ g, sg_phi2 u g ∂stdGauss (Fin n)|} := by
    intro G hGT
    simp only [Set.mem_preimage, hT, Set.mem_setOf_eq, hrow] at hGT
    simp_rw [sg_phi1_smul hsγ, sg_phi2_smul, hsγ2, ← Finset.mul_sum] at hGT
    rcases hGT with h | h
    · left
      simp only [Set.mem_setOf_eq]
      have hS : ∑ i, sg_phi1 u (G i) < 45 / 100 * M * D := by
        rw [hγ] at h
        have e : 90 / 100 * M * D / n = 2 / n * (45 / 100 * M * D) := by field_simp; ring
        rw [e] at h
        exact lt_of_mul_lt_mul_left h (by positivity)
      have hm : M * (D / 2) ≤ M * ∫ g, sg_phi1 u g ∂stdGauss (Fin n) :=
        mul_le_mul_of_nonneg_left (by rw [hDe]; exact hE1) hM.le
      rw [abs_sub_comm]
      refine le_trans ?_ (le_abs_self _)
      show t₁ ≤ M * ∫ g, sg_phi1 u g ∂stdGauss (Fin n) - ∑ i, sg_phi1 u (G i)
      have et : t₁ = 5 / 100 * M * D := rfl
      have e2 : M * (D / 2) = 50 / 100 * M * D := by ring
      linarith
    · right
      simp only [Set.mem_setOf_eq]
      have hS : 105 / 100 * M * D < ∑ i, sg_phi2 u (G i) := by
        rw [hγ] at h
        have e : 210 / 100 * M * D / n = 2 / n * (105 / 100 * M * D) := by field_simp; ring
        rw [e] at h
        exact lt_of_mul_lt_mul_left h (by positivity)
      refine le_trans ?_ (le_abs_self _)
      show t₂ ≤ ∑ i, sg_phi2 u (G i) - M * ∫ g, sg_phi2 u g ∂stdGauss (Fin n)
      rw [hE2, ← hDe]
      have et : t₂ = 5 / 100 * M * D := rfl
      linarith
  have hc1 := sg_cheb (m := mA n) (sg_meas_phi1 u) i1sq ht₁
  have hc2 := sg_cheb (m := mA n) (sg_meas_phi2 u) i2sq ht₂
  have hn1' := variance_cheby_num hnR hMe hDe b1 (k := 5 / 100) le_rfl
  have hn2' := variance_cheby_num hnR hMe hDe b2 (k := 5 / 100) (by norm_num)
  have hEμ : gaussMat (mA n) n γ {A₁ | ∃ g < Js n,
      vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g) < 17 / (100 * (n : ℝ)) ∨
      42 / (10 * (n : ℝ)) * (1 - nodeS (mkR wr (A₁, 0)) g ^ 2) < vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g)} ≤
      ENNReal.ofReal (1 / 10 ^ 5) := by
    refine (measure_mono hsub).trans ?_
    rw [hG, Measure.map_apply hf hTm]
    refine (measure_mono hpre).trans ((measure_union_le _ _).trans ?_)
    refine (add_le_add hc1 hc2).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 : ((mA n : ℕ) : ℝ) * (∫ g, sg_phi1 u g ^ 2 ∂stdGauss (Fin n)) / t₁ ^ 2 =
        M * (∫ g, sg_phi1 u g ^ 2 ∂stdGauss (Fin n)) / (5 / 100 * M * D) ^ 2 := rfl
    have e2 : ((mA n : ℕ) : ℝ) * (∫ g, sg_phi2 u g ^ 2 ∂stdGauss (Fin n)) / t₂ ^ 2 =
        M * (∫ g, sg_phi2 u g ^ 2 ∂stdGauss (Fin n)) / (5 / 100 * M * D) ^ 2 := rfl
    rw [e1, e2]
    linarith
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hEμ


theorem row_node_geometry {wr : WRet 13224} (hw : windowW wr)
    (θ : AHid 13224) {g : ℕ} (hg : g < Js 13224) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 13224 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (13224 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (13224 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 13224 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      13224 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 13224 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 13224)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 13224} (hw : windowW wr) :
    (gaussMat (mA 13224) 13224 (2 / (13224 : ℝ))).real {X | ∃ g < Js 13224,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13224 : ℝ)) ∨
      42 / (10 * (13224 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part266.Row13224

/-! A coarse bound on the actual paper statistics constant at dimension 13224. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part212 BstLean.Part220 BstLean.Part223

theorem table_gaussian_constant : gaussMomConst 128 ≤ 16 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := gaussMomConst_pow (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only at h
  rw [h]
  norm_num [Nat.factorial]

theorem table_radius_constant : exactRadius 13222 128 ≤ 1011 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by norm_num : 2 ≤ (13222 : ℕ))
    (by norm_num : 1 ≤ (128 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hp : radialProduct 13222 128 ≤ (13476 : ℝ) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, (13476 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          norm_num only [Nat.cast_ofNat]
          linarith
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans (by norm_num)

theorem table_statistics_constant : statisticsConstant (paperBound256 13224) ≤ 4 := by
  have h0 := paperT0_bounds (by norm_num : 8000 ≤ (13224 : ℕ))
    (by norm_num : (13224 : ℕ) ≤ 16384)
  have ht : paperTail256 13224 ≤ 16 :=
    (min_le_left _ _).trans table_gaussian_constant
  have hs : √(13224 : ℝ) ≤ 115 := sqrt_le_iff.mpr (by norm_num)
  have hh : √(2 / (13224 : ℝ)) ≤ 128 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 13224 := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 13224 := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hL : paperLJ256 13224 ≤ (1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16) := by
    change exactRadius 13222 128 * √(2 / (13224 : ℝ)) *
      (√(13224 : ℝ) + paperT0 13224 + paperTail256 13224) ≤ _
    have hp := mul_le_mul table_radius_constant hh (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1011 / 1000)
    exact mul_le_mul hp (add_le_add (add_le_add hs h0.2) ht)
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt) (by norm_num)
  have ha : paperActivationFactor 13224 ≤ 1002 / 1000 := by
    have h2 : √(2 : ℝ) ≤ 1415 / 1000 := sqrt_le_iff.mpr (by norm_num)
    have hprod := mul_le_mul h2 table_gaussian_constant
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 1415 / 1000)
    unfold paperActivationFactor
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 118 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 13224 := by
    unfold paperLJ256
    have hR : 0 ≤ exactRadius (13224 - 1 - 1) 128 := by
      change 0 ≤ exactRadius 13222 128
      unfold exactRadius
      exact div_nonneg (rpow_nonneg
        (radialProduct_pos (by norm_num : 1 ≤ (13222 : ℕ)) 128).le _) (sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hR (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor 13224 :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (118 / 100 : ℝ) *
      (((1011 / 1000 : ℝ) * (128 / 10000) * (115 + 8 + 16)) ^ 2 *
        (1002 / 1000 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 4 := by norm_num

end BstLean.Part266.Row13224

/-! Uniform scalar envelopes for the two original-matrix bias prices. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part172 BstLean.Part220 BstLean.Part223

noncomputable def tableEnvelope (C : ℝ) : RAData :=
  envelopeData 13224 (61 / 100) 166 (17 / (100 * 13224)) (26 / (10 * 13224)) C C C

theorem table_envelope_gap :
    0 < envelopeGap 13224 (61 / 100) 166 (17 / (100 * 13224)) := by
  norm_num [envelopeGap, tA, mA]

theorem table_envelope_D {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).D ∧ (tableEnvelope C).D ≤ (211055653 / 50000000000000000000) := by
  norm_num [tableEnvelope, envelopeData, envelopeD, tA, mA]
  constructor <;> linarith

theorem table_envelope_V {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).V ∧ (tableEnvelope C).V ≤ (319200931 / 250000000000000000000000) := by
  have hc2 : C ^ 2 ≤ 16 := by nlinarith
  norm_num [tableEnvelope, envelopeData, envelopeD, envelopeV, tA, mA]
  constructor <;> nlinarith [sq_nonneg C]

theorem table_envelope_P {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).P ∧ (tableEnvelope C).P ≤ (3696851591 / 1000000000000000000000000) := by
  constructor
  · dsimp [tableEnvelope, envelopeData]
    unfold envelopeP
    have hc4 := BstLean.Part162.cLS_nonneg 4
    norm_num [inverseRadius8, envelopeGap, tA, mA]
    positivity
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 *
          (8 * tA 13224 / 13224 * (61 / 100)) ^ 4 * inverseRadius8 (13224 - 1) /
            envelopeGap 13224 (61 / 100) 166 (17 / (100 * 13224)) ^ 8 * 4 ^ 4 := by
        dsimp [tableEnvelope, envelopeData]
        unfold envelopeP
        gcongr <;> first
          | exact cLS4_le
          | exact BstLean.Part162.cLS_nonneg 4
          | exact hC4
          | exact hC
          | norm_num [inverseRadius8, envelopeGap, tA, mA]
      _ ≤ _ := by norm_num [inverseRadius8, envelopeGap, tA, mA]

end BstLean.Part266.Row13224

namespace BstLean.Part266.Row13224
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 13224 166 ≤ (4142106333 / 1000000000000000000)
  f1 : (tableEnvelope C).f1 13224 166 ≤ (1381876623 / 1000000000000000000)
  f2 : (tableEnvelope C).f2 ≤ (332134551 / 1000000000000000000)
  w0 : (tableEnvelope C).w0 13224 166 ≤ (811894541 / 50000000000000000000)
  w1 : (tableEnvelope C).w1 13224 166 ≤ (577647433 / 50000000000000000000)
  w2 : (tableEnvelope C).w2 13224 166 ≤ (52764361 / 12500000000000000000)

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ (211055653 / 50000000000000000000) := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ (211055653 / 50000000000000000000) := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ (319200931 / 250000000000000000000000) := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ (3696851591 / 1000000000000000000000000) := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : ((896361 / 250000000) : ℝ) ≤ √(17 / (100 * 13224) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 13224) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ (513633689 / 250000000000000) :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ (7146478081 / 200000000000000000) :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 13224) * 166 ≤ 186 / 10000 := by
    have hs : √(tA 13224) ≤ (2138859 / 20000000000) := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 13224) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 13224 * (166 : ℝ) ^ 2 + 26 / (10 * 13224) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 13224) : ℝ)) (tA 13224 * 166 ^ 2 + 26 / (10 * 13224)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * ((896361 / 250000000))) * ((211055653 / 50000000000000000000)) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * ((896361 / 250000000)) ^ 3) * ((319200931 / 250000000000000000000000))) + ((3696851591 / 1000000000000000000000000)) * (3 / 2 * (39895 / 100000) / ((896361 / 250000000)) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 13224) : ℝ)) d.D d.V d.P (√(tA 13224) * 166) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / ((896361 / 250000000)) ^ 2 * (((513633689 / 250000000000000)) * ((7146478081 / 200000000000000000)))) + ((3696851591 / 1000000000000000000000000)) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 13224) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / ((896361 / 250000000)) * ((211055653 / 50000000000000000000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 13224) : ℝ)) (tA 13224 * 166 ^ 2 + 26 / (10 * 13224)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ ((211055653 / 50000000000000000000) : ℝ) + (24198 / 100000) / (2 * ((896361 / 250000000)) ^ 2) * ((319200931 / 250000000000000000000000)) + ((3696851591 / 1000000000000000000000000)) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 13224) : ℝ)) (√(26 / (10 * 13224) : ℝ)) d.D d.V d.P (√(tA 13224) * 166) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / ((896361 / 250000000)) * (((513633689 / 250000000000000)) * ((7146478081 / 200000000000000000))) + ((3696851591 / 1000000000000000000000000)) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 13224) * 166) ≤ _
    unfold AW2
    calc
      _ ≤ ((211055653 / 50000000000000000000) : ℝ) + ((3696851591 / 1000000000000000000000000)) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part266.Row13224

namespace BstLean.Part266.Row13224
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part213 BstLean.Part220 BstLean.Part223

theorem table_coefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    0 ≤ (tableEnvelope C).f0 13224 166 ∧
    0 ≤ (tableEnvelope C).f1 13224 166 ∧ 0 ≤ (tableEnvelope C).f2 ∧
    0 ≤ (tableEnvelope C).w0 13224 166 ∧
    0 ≤ (tableEnvelope C).w1 13224 166 ∧ 0 ≤ (tableEnvelope C).w2 13224 166 := by
  let d := tableEnvelope C
  have hD : 0 ≤ d.D := (table_envelope_D hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (table_envelope_V hC hC4).1
  have hP : 0 ≤ d.P := (table_envelope_P hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA 13224 * (166 : ℝ) ^ 2 + d.Smax := by
    norm_num [d, tableEnvelope, envelopeData, tA, mA]
  change 0 ≤ d.f0 13224 166 ∧ 0 ≤ d.f1 13224 166 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 13224 166 ∧ 0 ≤ d.w1 13224 166 ∧ 0 ≤ d.w2 13224 166
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem table_location_correction : locationR16 13224 ≤ 2 * (228 / 100 : ℝ) / 13224 := by
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem table_energy_correction : energyR16 13224 ≤ 2 * (370 / 100 : ℝ) / 13224 := by
  have hr : (1216070380 : ℝ) ^ (1 / 16 : ℝ) ≤ 370 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (16 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 1216070380)
      (by norm_num : (16 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold energyR16
  gcongr

theorem table_bias_prices {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    (completeRAData (tableEnvelope C) 13224 166).locationBound 13224 166 ≤
      (15 / 1000 : ℝ) ^ 16 ∧
    (completeRAData (tableEnvelope C) 13224 166).energyBound 13224 166 ≤
      (10 / 1000 : ℝ) ^ 16 := by
  let d := tableEnvelope C
  have F := table_coefficient_certificate hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := table_coefficient_nonneg hC hC4
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 13224 166) (d.f1 13224 166) d.f2 ≤
      32 * (((4142106333 / 1000000000000000000) : ℝ) + (1381876623 / 1000000000000000000) + (332134551 / 1000000000000000000)) :=
    (radius_polynomial_root_price hf0 hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 13224 166) (d.w1 13224 166)
      (d.w2 13224 166) ≤
      32 * (((811894541 / 50000000000000000000) : ℝ) + (577647433 / 50000000000000000000) + (52764361 / 12500000000000000000)) :=
    (radius_polynomial_root_price hw0 hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 13224 166) (d.f1 13224 166) d.f2 ≤
      ((4142106333 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4142106333 / 1000000000000000000)) * ((1381876623 / 1000000000000000000)) * (126 / 100) +
      2 * (((1381876623 / 1000000000000000000)) ^ 2 + 2 * ((4142106333 / 1000000000000000000)) * ((332134551 / 1000000000000000000))) +
      6 * ((1381876623 / 1000000000000000000)) * ((332134551 / 1000000000000000000)) * (126 / 100) + 8 * ((332134551 / 1000000000000000000)) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 13224 166) (d.f1 13224 166) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 13224 := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 13224 := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 13224 166) (d.f1 13224 166) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 13224 166) (d.w1 13224 166) (d.w2 13224 166)
  have hwexpr0 : 0 ≤ d.w0 13224 166 + d.w1 13224 166 * √(π / 2) +
      2 * d.w2 13224 166 + energyR16 13224 *
      radiusPolynomialRoot16 (d.w0 13224 166) (d.w1 13224 166) (d.w2 13224 166) := by
    positivity
  constructor
  · change (13224 : ℝ) ^ 8 * (mA 13224 : ℝ) ^ 8 *
      (collectedSecond (d.f0 13224 166) (d.f1 13224 166) d.f2 + locationR16 13224 *
        radiusPolynomialRoot16 (d.f0 13224 166) (d.f1 13224 166) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (13224 : ℝ) ^ 8 * (mA 13224 : ℝ) ^ 8 *
        ((((4142106333 / 1000000000000000000) : ℝ) ^ 2 + 2 * ((4142106333 / 1000000000000000000)) * ((1381876623 / 1000000000000000000)) * (126 / 100) +
          2 * (((1381876623 / 1000000000000000000)) ^ 2 + 2 * ((4142106333 / 1000000000000000000)) * ((332134551 / 1000000000000000000))) +
          6 * ((1381876623 / 1000000000000000000)) * ((332134551 / 1000000000000000000)) * (126 / 100) + 8 * ((332134551 / 1000000000000000000)) ^ 2) +
          (2 * (228 / 100 : ℝ) / 13224) *
          (32 * (((4142106333 / 1000000000000000000) : ℝ) + (1381876623 / 1000000000000000000) + (332134551 / 1000000000000000000))) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact table_location_correction
          | exact htF
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]
  · change (mA 13224 : ℝ) ^ 16 *
      (d.w0 13224 166 + d.w1 13224 166 * √(π / 2) + 2 * d.w2 13224 166 +
        energyR16 13224 * radiusPolynomialRoot16 (d.w0 13224 166) (d.w1 13224 166)
          (d.w2 13224 166)) ^ 16 ≤ _
    calc
      _ ≤ (mA 13224 : ℝ) ^ 16 *
        (((811894541 / 50000000000000000000) : ℝ) + ((577647433 / 50000000000000000000)) * (126 / 100) + 2 * ((52764361 / 12500000000000000000)) +
          (2 * (370 / 100 : ℝ) / 13224) *
          (32 * (((811894541 / 50000000000000000000) : ℝ) + (577647433 / 50000000000000000000) + (52764361 / 12500000000000000000)))) ^ 16 := by
        gcongr <;> first
          | exact F.w0
          | exact F.w1
          | exact F.w2
          | exact hπ
          | exact table_energy_correction
          | exact htW
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num [mA]

theorem table_bias_charge_caps :
    (15 / 1000 : ℝ) ^ 16 / fourAllowances 1 ^ 16 +
      (10 / 1000 : ℝ) ^ 16 / fourAllowances 3 ^ 16 ≤ 6 / 10 ^ 6 := by
  norm_num [fourAllowances]

end BstLean.Part266.Row13224

/-! Rational certificates for the two common-cap fluctuation prices.
The first-layer and bias moment supplies remain separate obligations. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part170 BstLean.Part216 BstLean.Part223

theorem table_location_fluctuation_price :
    (k24 * (√(13224 : ℝ) *
      √(tA 13224 * ((166 : ℝ) ^ 2 / (13224 - 2))) / 2) * √(61 / 100 : ℝ)) ^ 24 ≤
      (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 := by
  have hN : √(13224 : ℝ) ^ 24 = (13224 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  have hlam : √(tA 13224 * ((166 : ℝ) ^ 2 / (13224 - 2))) ^ 24 =
      (tA 13224 * ((166 : ℝ) ^ 2 / (13224 - 2))) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hH : √(61 / 100 : ℝ) ^ 24 = (61 / 100 : ℝ) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, div_pow, k24_pow, hN, hlam, hH]
  norm_num [tA, mA, fourAllowances, Nat.factorial]

theorem table_energy_coefficient :
    energyCoefficient18 13224 ≤ (2 * 13224 * (212 / 100 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 212 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  simp only [Nat.cast_ofNat]
  gcongr

theorem table_energy_fluctuation_price :
    (√(tA 13224 * ((166 : ℝ) ^ 2 / (13224 - 2))) * √((42 / 10 : ℝ) / 13224) *
      energyCoefficient18 13224) ^ 18 * (61 / 100 : ℝ) ^ 18 ≤
        (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
  have hlam : √(tA 13224 * ((166 : ℝ) ^ 2 / (13224 - 2))) ^ 18 =
      (tA 13224 * ((166 : ℝ) ^ 2 / (13224 - 2))) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num [tA, mA])]
  have hσ : √((42 / 10 : ℝ) / 13224) ^ 18 = ((42 / 10 : ℝ) / 13224) ^ 9 := by
    rw [show (18 : ℕ) = 2 * 9 from rfl, pow_mul, sq_sqrt (by norm_num)]
  simp only [mul_pow, hlam, hσ]
  calc
    _ ≤ (tA 13224 * ((166 : ℝ) ^ 2 / (13224 - 2))) ^ 9 *
        ((42 / 10 : ℝ) / 13224) ^ 9 *
        (2 * 13224 * (212 / 100 : ℝ) + (269 / 10) * 8) ^ 18 * (61 / 100 : ℝ) ^ 18 := by
      gcongr <;> first
        | exact table_energy_coefficient
        | exact energyCoefficient18_nonneg _
        | norm_num [tA, mA]
        | positivity
    _ ≤ _ := by norm_num [tA, mA, fourAllowances]

theorem table_remaining_price_allocation :
    (1 / 10 ^ 5 : ℝ) + 1 / 10000 + 717 / 10 ^ 6 + 19 / 10 ^ 6 +
      206754646384 / 10 ^ 15 = tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13224

/-! The four actual common-cap scalar prices fit a single table allowance. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part170 BstLean.Part220 BstLean.Part223

noncomputable def tableMomentPrices : Fin 4 → ℝ :=
  completeMomentPrices 13224 (61 / 100) 166 (17 / (100 * 13224)) (26 / (10 * 13224))
    (statisticsConstant (paperBound256 13224)) √((42 / 10 : ℝ) / 13224) (61 / 100)

theorem table_statistics_nonneg : 0 ≤ statisticsConstant (paperBound256 13224) :=
  (statisticsConstant_pos ((paperStatisticsBound_pos (by norm_num : 4 ≤ (13224 : ℕ))
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by norm_num) (by norm_num)))).le

theorem table_four_price :
    tableMomentPrices 0 / fourAllowances 0 ^ 24 +
      tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 2 / fourAllowances 2 ^ 18 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ 742 / 10 ^ 6 := by
  have h0 : tableMomentPrices 0 ≤ (717 / 10 ^ 6 : ℝ) * fourAllowances 0 ^ 24 :=
    table_location_fluctuation_price
  have h2 : tableMomentPrices 2 ≤ (19 / 10 ^ 6 : ℝ) * fourAllowances 2 ^ 18 := by
    change (√(tA 13224 * ((166 : ℝ) ^ 2 / (13224 - 2))) *
      √((42 / 10 : ℝ) / 13224) * energyCoefficient18 13224) ^ 18 *
      (61 / 100 : ℝ) ^ 12 * (61 / 100 : ℝ) ^ 6 ≤ _
    convert table_energy_fluctuation_price using 1 <;> ring
  have hb := table_bias_prices table_statistics_nonneg table_statistics_constant
  have h1 : tableMomentPrices 1 ≤ (15 / 1000 : ℝ) ^ 16 := hb.1
  have h3 : tableMomentPrices 3 ≤ (10 / 1000 : ℝ) ^ 16 := hb.2
  have hd0 : tableMomentPrices 0 / fourAllowances 0 ^ 24 ≤ (717 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h0
  have hd2 : tableMomentPrices 2 / fourAllowances 2 ^ 18 ≤ (19 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourAllowances])).mpr
    exact h2
  have hdb : tableMomentPrices 1 / fourAllowances 1 ^ 16 +
      tableMomentPrices 3 / fourAllowances 3 ^ 16 ≤ (6 / 10 ^ 6 : ℝ) :=
    (add_le_add (div_le_div_of_nonneg_right h1 (by norm_num [fourAllowances]))
      (div_le_div_of_nonneg_right h3 (by norm_num [fourAllowances]))).trans table_bias_charge_caps
  linarith

theorem table_first_charge_price :
    exp (-(13224 : ℝ) / 2) + 1 / 10 ^ 5 + 1 / 10000 ≤ (116145 / 10 ^ 9 : ℝ) := by
  have he : exp (-(13224 : ℝ) / 2) ≤ (6145 / 10 ^ 9 : ℝ) :=
    ((exp_le_exp.mpr (by norm_num : -(13224 : ℝ) / 2 ≤ -12)).trans
      exp_neg12_row).trans (by norm_num)
  linarith

theorem table_total_charge_price :
    (116145 / 10 ^ 9 : ℝ) + 742 / 10 ^ 6 ≤ 9 / 10000 := by norm_num

theorem table_charge_price : (9 / 10000 : ℝ) ≤ tableChargeAllowance := by
  norm_num [tableChargeAllowance]

end BstLean.Part266.Row13224

/-! One first-layer event and the four original second-layer moments pay for
the actual stored-table event at a fixed retained World value. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223

def tableVarianceEvent (wr : WRet 13224) : Set (Matrix (Fin (mA 13224)) (Fin 13224) ℝ) :=
  {X | ∀ g : Fin (Js 13224),
    17 / (100 * (13224 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
    vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
      42 / (10 * (13224 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)}

theorem tableVarianceEvent_measurable (wr : WRet 13224) :
    MeasurableSet (tableVarianceEvent wr) := by
  have mc : Measurable (fun X => mkR wr (X, 0)) :=
    measurable_mkR.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have he : tableVarianceEvent wr = ⋂ g : Fin (Js 13224),
      {X | 17 / (100 * (13224 : ℝ)) ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ∧
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (0, 0)) g.val) ≤
          42 / (10 * (13224 : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2)} := by
    ext X
    simp only [tableVarianceEvent, mem_setOf_eq, mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro g
  exact (measurableSet_le measurable_const (measurable_vsig2_comp mc measurable_const)).inter
    (measurableSet_le (measurable_vsig2_comp mc measurable_const) measurable_const)

theorem tableVarianceEvent_charge {wr : WRet 13224} (hw : windowW wr) :
    (gaussMat (mA 13224) 13224 (2 / (13224 : ℝ))).real (tableVarianceEvent wr)ᶜ ≤
      1 / 10 ^ 5 := by
  have hs : (tableVarianceEvent wr)ᶜ ⊆ {X | ∃ g < Js 13224,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (13224 : ℝ)) ∨
      42 / (10 * (13224 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) <
        vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} := by
    intro X hX
    obtain ⟨g, hg⟩ := not_forall.mp hX
    refine ⟨g.val, g.isLt, ?_⟩
    exact (not_and_or.mp hg).elim
      (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact (measureReal_mono hs (measure_ne_top _ _)).trans (node_trace_charge_row hw)

def tableFirstEvent (wr : WRet 13224) : Set (Matrix (Fin (mA 13224)) (Fin 13224) ℝ) :=
  (Eop 13224 ∩ tableVarianceEvent wr) ∩
    paperStatisticsEvent wr (tableNodeMeasure wr) Fin.val (statisticsConstant (paperBound256 13224))

theorem tableFirstEvent_measurable (wr : WRet 13224) : MeasurableSet (tableFirstEvent wr) :=
  ((measurableSet_Eop _).inter (tableVarianceEvent_measurable wr)).inter
    (paperStatisticsEvent_measurable wr (tableNodeMeasure wr) Fin.val _)

theorem tableFirstEvent_charge {wr : WRet 13224} (hw : windowW wr) :
    (gaussMat (mA 13224) 13224 (2 / (13224 : ℝ))).real (tableFirstEvent wr)ᶜ ≤
      (116145 / 10 ^ 9 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13224)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by norm_num) (by norm_num)
    wr hc (tableNodeMeasure wr) (tableNodeMeasure_mass wr).le Fin.val hs
  unfold tableFirstEvent
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by norm_num))
      (tableVarianceEvent_charge hw))) hstat)).trans table_first_charge_price

def tableBadPair (wr : WRet 13224) : Set (AHid 13224) := {θ | mkR wr θ ∉ tableEvent}

theorem tableBadPair_measurable (wr : WRet 13224) : MeasurableSet (tableBadPair wr) :=
  tableEvent_measurable.compl.preimage
    (measurable_mkR.comp (measurable_const.prodMk measurable_id))

theorem table_conditional_charge {wr : WRet 13224} (hw : windowW wr) :
    ∀ᵐ X ∂gaussMat (mA 13224) 13224 (2 / (13224 : ℝ)), X ∈ tableFirstEvent wr →
      (gaussMat (mA 13224) (mA 13224) (tA 13224))
        {M | (X, M) ∈ tableBadPair wr} ≤ ENNReal.ofReal (742 / 10 ^ 6 : ℝ) := by
  have hc := BstLean.Part172.sg_wr_ne (by norm_num) hw
  have hs (g : Fin (Js 13224)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := row_node_geometry hw (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js 13224)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (61 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (row_node_geometry hw (0, 0) g.isLt).2.2⟩
  have h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ^ 12)
      ∂tableNodeMeasure wr ≤ ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) := by
    calc
      _ ≤ ∫⁻ _g, ENNReal.ofReal ((61 / 100 : ℝ) ^ 12) ∂tableNodeMeasure wr :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hq g).1 (hq g).2 12)
      _ = _ := by rw [lintegral_const, tableNodeMeasure_mass, mul_one]
  filter_upwards [paperNodes_kink_ae (by norm_num) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js 13224)) := (hvar g).1
  have hmax (g : Fin (Js 13224)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * 13224) : ℝ) :=
    (hvar g).2.trans ((mul_le_mul_of_nonneg_left (hq g).2 (by norm_num)).trans (by norm_num))
  have htrace (g : Fin (Js 13224)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / 13224) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by norm_num)]
    convert (hvar g).2 using 1 <;> first | rfl | norm_num
  have hA (i : Fin 4) : 0 < fourAllowances i := by fin_cases i <;> norm_num [fourAllowances]
  have hmark := paperOriginalFour_markov (by norm_num) wr hc (tableNodeMeasure wr)
    (tableNodeMeasure_mass wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (0 : ℝ) ≤ 166) (by norm_num : (0 : ℝ) < 17 / (100 * 13224))
    (by norm_num : (0 : ℝ) ≤ 26 / (10 * 13224)) table_statistics_nonneg
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (first_matrix_row (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace table_envelope_gap h12 hk fourAllowances hA
  have hreal : (gaussMat (mA 13224) (mA 13224) (tA 13224)).real
      {M | (X, M) ∈ tableBadPair wr} ≤ (742 / 10 ^ 6 : ℝ) :=
    ((measureReal_mono (table_second_layer_bad_subset (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark).trans table_four_price
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem table_world_charge (wr : WRet 13224) :
    (nuA 13224).real (tableBadPair wr) ≤ (9 / 10000 : ℝ) := by
  by_cases hw : windowW wr
  · exact (product_charge_ae _ _ (tableFirstEvent_measurable wr) (tableBadPair_measurable wr)
      (by norm_num) (by norm_num) (tableFirstEvent_charge hw)
      (table_conditional_charge hw)).trans table_total_charge_price
  · have he : tableBadPair wr = ∅ := by
      ext θ
      simp only [tableBadPair, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

end BstLean.Part266.Row13224

/-! The actual table event has an unconditional retained-data payment. -/
namespace BstLean.Part266.Row13224
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part170

def tablePairEvent : Set (WRet 13224 × AHid 13224) :=
  {p | mkR p.1 p.2 ∈ tableEvent}

theorem tablePairEvent_measurable : MeasurableSet tablePairEvent :=
  tableEvent_measurable.preimage measurable_mkR

theorem tableEvent_ret_charge :
    (retDist (paperCentres 13224)).real tableEventᶜ ≤ (9 / 10000 : ℝ) := by
  have h := retDist_pair_charge (paperCentres 13224) tablePairEvent_measurable
    (by norm_num : (0 : ℝ) ≤ 9 / 10000) table_world_charge
  convert h using 1
  congr 1

noncomputable def certifiedTablePayment (H : Set (Ret 13224)) : TablePayment H := by
  refine ⟨?_⟩
  exact ((measureReal_mono inter_subset_right (measure_ne_top _ _)).trans
    tableEvent_ret_charge).trans table_charge_price

theorem certifiedBaseEvent (H : Set (Ret 13224)) : BaseEventCertificate H tableEvent :=
  proposedBaseEvent_certificate (certifiedTablePayment H)

theorem certified_hq_base_charge (H : Set (Ret 13224)) :
    (retDist (paperCentres 13224)).real (H ∩ hqBaseEventᶜ) ≤ (1449145 / 10 ^ 9 : ℝ) := by
  have hs : H ∩ hqBaseEventᶜ ⊆ paidBaseEventᶜ ∪ tableEventᶜ := by
    intro c hc
    by_cases hp : c ∈ paidBaseEvent
    · exact Or.inr fun ht => hc.2 ⟨⟨hp.1, ht⟩, hp.2⟩
    · exact Or.inl hp
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add paidBaseEvent_charge
      tableEvent_ret_charge))).trans (by norm_num [analyticCharge])

end BstLean.Part266.Row13224

namespace BstLean.Part266
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188

noncomputable def actualCertificate13224 :
    BstLean.Part262.ActualRootCertificate 13224 BstLean.Part266.agent13224.root where
  dimension := by norm_num
  table_payment := Row13224.tableEvent_ret_charge
  inputs := by
    intro t c hw hc I hE
    have he : 0 < eR c := by linarith [(Row13224.centre_energy_range hw hc.1.1.1).1]
    have hm := BstLean.Part266.low_mass_of_interfaces (by norm_num) hw he I hE
    exact Row13224.hqRootInputs_on_base t hw hc.1 hm

end BstLean.Part266
