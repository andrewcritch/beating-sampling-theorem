-- Dimension arguments made explicit by p285-interval-explicit.py.
import BstLean.Part285IntervalTools
import BstLean.Part252All

/-! Uniform pilot estimates on an interval in the dimension. -/
namespace BstLean.Part285.Interval.PilotA
open MeasureTheory Real
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part130 BstLean.Part152 BstLean.Part212
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part150 (c1F c2F)
open BstLean.Part156
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part157 BstLean.Part169
open BstLean.Part157 BstLean.Part169 BstLean.Part162
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195
open BstLean.Part159
open BstLean.Part162 (psiA)
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222
open BstLean.Part162 BstLean.Part180
open BstLean.Part169
open BstLean.Part169 BstLean.Part195 BstLean.Part212
open BstLean.Part169 BstLean.Part212
open BstLean.Part169 BstLean.Part242
open BstLean.Part195 BstLean.Part222
open BstLean.Part211
open BstLean.Part212
open BstLean.Part220 BstLean.Part223 BstLean.Part242
open BstLean.Part252
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53)
open Real
open Real MeasureTheory
open Real Set
open scoped ENNReal
variable {n : ℕ} [Fact (12000 ≤ n ∧ n ≤ 16199)]

macro "band_num" : tactic => do
  let n := Lean.mkIdent `n
  `(tactic| (have bandBounds : 12000 ≤ $n ∧ $n ≤ 16199 := Fact.out
             have bandLower : (12000 : ℝ) ≤ $n := by
               exact_mod_cast (Fact.out : 12000 ≤ $n ∧ $n ≤ 16199).1
             have bandUpper : ($n : ℝ) ≤ 16199 := by
               exact_mod_cast (Fact.out : 12000 ≤ $n ∧ $n ≤ 16199).2
             try simp (disch := omega) only [Nat.cast_sub, Nat.cast_ofNat] at *
             try constructor
             all_goals first | omega | positivity | interval_num | (field_simp <;> nlinarith) | nlinarith))

macro "band_bounds" : tactic => do
  let n := Lean.mkIdent `n
  let b := Lean.mkIdent `bandBounds
  let l := Lean.mkIdent `bandLower
  let u := Lean.mkIdent `bandUpper
  let p := Lean.mkIdent `bandPos
  `(tactic| (have $b : 12000 ≤ $n ∧ $n ≤ 16199 := Fact.out
             have $l : (12000 : ℝ) ≤ $n := by exact_mod_cast $b.1
             have $u : ($n : ℝ) ≤ 16199 := by exact_mod_cast $b.2
             have $p : (0 : ℝ) < $n := by linarith))

macro "band_linarith" : tactic =>
  `(tactic| first | linarith | band_num)
macro "band_linarith" "[" args:term,* "]" : tactic =>
  `(tactic| first | linarith [$args,*] | band_num)

macro "band_nlinarith" : tactic =>
  `(tactic| first | nlinarith | band_num)
macro "band_nlinarith" "[" args:term,* "]" : tactic =>
  `(tactic| first | nlinarith [$args,*] | band_num)

noncomputable def eta : ℝ := 2147 / 10 ^ 6

noncomputable def mixtureFloor : ℝ := 215240 / 10 ^ 6

noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor

noncomputable def chi : ℝ := (10653 / 10000)

noncomputable def epsilon : ℝ := 1 / 50

noncomputable def varianceMax : ℝ := 3 / 1000

noncomputable def energyError : ℝ := 250 / 1000

noncomputable def locationError : ℝ := 75 / 1000

noncomputable def locationNorm : ℝ := 1002 / 1000

noncomputable def varianceNorm : ℝ := 1 / 2000

noncomputable def removalBudget : ℝ := (68 / 10 ^ 6) ^ 2 / (2 * (1 + eta⁻¹))

theorem eta_pos : 0 < eta := by norm_num [eta] <;> try band_num

theorem eta_lt_one : eta < 1 := by norm_num [eta] <;> try band_num

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 68 / 10 ^ 6 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (68 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget] <;> try band_num
  rw [h, Real.sqrt_sq (by norm_num <;> try band_num : (0 : ℝ) ≤ 68 / 10 ^ 6)]


theorem rotation16_le : rotationConstant 16 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num <;> try band_num : (32 : ℕ) ≠ 0) (by norm_num <;> try band_num : (0 : ℝ) ≤ 6)
  rw [show (32 : ℕ) = 2 * 16 by norm_num <;> try band_num, rotationConstant_pow (by norm_num <;> try band_num) (by norm_num <;> try band_num),
    ← oddMoment_eq]
  have hp : π / 2 ≤ (22 / 7 : ℝ) / 2 := by band_linarith [pi_lt_d4]
  have hm : 0 ≤ oddMoment 16 := by rw [oddMoment_eq]; exact BstLean.Part162.gmom_nonneg _
  calc
    (π / 2) ^ (2 * 16) * oddMoment 16
        ≤ ((22 / 7 : ℝ) / 2) ^ (2 * 16) * oddMoment 16 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) hm
    _ ≤ 6 ^ (2 * 16) := by norm_num [oddMoment, Finset.prod_range_succ] <;> try band_num


theorem energy_allowance_row : energyAllowance n ≤ 2 / 1000 := by
  band_bounds
  have hs : √(2 / (mA n : ℝ)) ≤ ((117851131 / 1000000000000) : ℝ) := by
    apply (sqrt_le_iff).2
    norm_num [mA] <;> try band_num
  have ha : agentLayerAllowance n ≤ ((177 / 250000) : ℝ) := by
    unfold agentLayerAllowance layerAllowance
    have hm := mul_le_mul rotation16_le hs (sqrt_nonneg _) (by norm_num <;> try band_num : (0 : ℝ) ≤ 6)
    norm_num [mA] at *
    have hsmall : (5 : ℝ) / (2 * (n : ℝ) ^ 2) ≤ 1 / 10 ^ 7 := by band_num
    linarith only [hm, hsmall]
  have ha0 := layerAllowance_nonneg (mA n)
  change 0 ≤ agentLayerAllowance n at ha0
  have he : energyWeightAllowance n ≤ ((1417 / 1000000) : ℝ) := by
    unfold energyWeightAllowance
    have h2 := pow_le_pow_left₀ ha0 ha 2
    all_goals band_nlinarith
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 13628 / 10000 := by
    apply le_of_pow_le_pow_left₀ (by norm_num <;> try band_num : (32 : ℕ) ≠ 0) (by norm_num <;> try band_num : (0 : ℝ) ≤ 13628 / 10000)
    have hrpow := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 32)
      (by norm_num <;> try band_num : (0 : ℝ) ≤ 20000) (by norm_num <;> try band_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hrpow
    simp only [one_div] at hrpow
    rw [hrpow]
    norm_num <;> try band_num
  unfold energyAllowance
  have hm := mul_le_mul hr he (energyWeightAllowance_nonneg n)
    (by norm_num <;> try band_num : (0 : ℝ) ≤ 13628 / 10000)
  norm_num at hm ⊢
  all_goals band_linarith


theorem full_location_moment_row (c : Ret n)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP n).tau0 c)
    (he : c.2.1.1 ∈ energyEvent c.1.2 ((paperDesignP n).tau0 c))
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix n)) :
    ∫ a in K, fbR c a ^ k ∂muI n ≤ locationNorm ^ k := by
  band_bounds
  refine (full_location_moment (by norm_num <;> try band_num) c hc hτ
    (energyMoment_on_event (by norm_num <;> try band_num) _ c he) hk hke hk32 K).trans ?_
  apply pow_le_pow_left₀ (by band_linarith [energyAllowance_nonneg n])
  have hh := (energy_allowance_row (n := n))
  norm_num [locationNorm] at *
  all_goals band_linarith


def outputCentreEvent {k : ℕ} (D : Centres k) : Set (Ret k) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA k : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp k}


theorem chi_row : chiUp n / n ≤ chi := by
  band_bounds
  have lower : (12000 : ℝ) ≤ n := by band_num
  have pos : (0 : ℝ) < n := by band_num
  have hs : √((n : ℝ) * 12) ≤ ((31622777 / 1000000000) : ℝ) * n := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hmul := mul_nonneg (sub_nonneg.mpr lower) pos.le
    all_goals band_nlinarith
  unfold chiUp
  calc
    _ ≤ 1 + 2 * ((31622777 / 1000000000) : ℝ) + 24 / 12000 := by
      rw [div_le_iff₀ pos]
      all_goals band_nlinarith
    _ ≤ chi := by norm_num [chi] <;> try band_num


theorem outputCentre_row {c : Ret n}
    (hc : c ∈ outputCentreEvent (paperCentres n)) :
    normSq c.2.1.2 ≤ (2 / (n : ℝ)) * eR c * n * chi := by
  band_bounds
  change normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (bR c) * chiUp n at hc
  have heq : 2 / (mA n : ℝ) * normSq (bR c) * chiUp n =
      (2 / (n : ℝ)) * eR c * n * (chiUp n / n) := by
    unfold mA eR
    push_cast
    field_simp [bandPos.ne']
    <;> first | exact mul_comm _ _ | ring
  rw [heq] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left (chi_row (n := n))
    (by have := normSq_nonneg (bR c); unfold eR; positivity))


theorem variance_pointwise {k : ℕ} (hn : 3 ≤ k) (c : Ret k)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix k) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(k : ℝ)) ^ 2 / ((k : ℝ) - 2) := by
  have hn1 : 1 ≤ k := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(k : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP k) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP k) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP k) c a v ∂stdGauss (Fin (k - 1)) ≤
      2 * (O₂ * O₁ / √(k : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP k) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP k) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(k : ℝ)) ^ 2 ∂stdGauss (Fin (k - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (k : ℝ) - 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hn
    all_goals band_linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le


theorem variance_pointwise_row (c : Ret n) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) ((145 / 100) * √(n : ℝ))) (h2 : OpB (A2 c) (283 / 100)) (a : Ix n) :
    |VR c a| ≤ varianceMax := by
  band_bounds
  have h := variance_pointwise (by omega) c hb h1 h2 (by positivity) (by norm_num <;> try band_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  have he : (283 / 100 : ℝ) * (145 / 100 * √(n : ℝ)) / √n =
      (283 / 100) * (145 / 100) := by
    field_simp
  rw [he]
  norm_num [varianceMax] <;> try band_num
  all_goals band_num


def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}


theorem first_matrix_row (c : Ret n) (hc : A1 c ∈ Eop n) :
    OpB (A1 c) ((145 / 100) * √(n : ℝ)) := by
  band_bounds
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (n : ℝ)) * √n = √2 := by
    rw [← sqrt_mul (by positivity), div_mul_cancel₀ _ bandPos.ne']
  have hn : (109 : ℝ) ≤ √n := le_sqrt_of_sq_le (by band_linarith)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num <;> try band_num)
  have he : √(2 / (n : ℝ)) * ((n : ℝ) + 2 * √n) = √2 * (√n + 2) := by
    have hmain : √(2 / (n : ℝ)) * n = √2 * √n := by
      calc
        _ = (√(2 / (n : ℝ)) * √n) * √n := by
          rw [mul_assoc, ← pow_two, sq_sqrt bandPos.le]
        _ = _ := by rw [hs]
    calc
      _ = √(2 / (n : ℝ)) * n + 2 * (√(2 / (n : ℝ)) * √n) := by ring
      _ = _ := by rw [hmain, hs]; ring
  rw [he]
  all_goals band_nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ √n + 2)]


theorem second_matrix_row (c : Ret n) (hc : c ∈ BstLean.Part164.Eop2 n) :
    OpB (A2 c) (283 / 100) := by
  band_bounds
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA n : ℝ)) ≤ ((1414214 / 10 ^ 6 : ℝ) / n) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA] <;> try band_num
  exact (mul_le_mul_of_nonneg_right hs (by norm_num <;> try band_num : (0 : ℝ) ≤ 2 * n + 5)).trans
    (by norm_num <;> try band_num)


theorem variance_of_matrix_events (c : Ret n) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP n).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP n) (FirstMatrix n))
    (h2 : c ∈ BstLean.Part164.Eop2 n) (a : BstLean.Part161.Ix n) :
    |VR c a| ≤ varianceMax := by
  band_bounds
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact (variance_pointwise_row (n := n)) c hb ((first_matrix_row (n := n)) c (h1 hτ)) ((second_matrix_row (n := n)) c h2) a


theorem variance_moment_of_latitude {k : ℕ} (hn : 26 ≤ k) (c : Ret k)
    (he : 0 < eR c) {C : ℝ} (hC : 0 < C)
    (hk : agKey (paperDesignP k) c ∈ BstLean.Part212.latitudeEvent k
      (ENNReal.ofReal (C / k))) (K : Set (Ix k)) :
    ∫ a in K, ((k : ℝ) * VR c a) ^ 2 ∂muI k ≤ (C / ((k : ℝ) - 3)) ^ 2 := by
  have hn1 : 1 ≤ k := by omega
  have hnR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hb : normSq (bR c) ≠ 0 := by
    intro h
    unfold eR at he
    rw [h, zero_div] at he
    exact (lt_irrefl 0 he)
  set Vl : Ix k → ℝ := fun a => ∫ v, (lamX (paperDesignP k) c (xLat c (latC (paperDesignP k) c a) (unitF53 v)) -
    ∫ w, lamX (paperDesignP k) c (xLat c (latC (paperDesignP k) c a) (unitF53 w)) ∂stdGauss (Fin (k - 1))) ^ 2 ∂stdGauss (Fin (k - 1)) with hVl
  have hVe : ∀ a, VR c a = eR c * Vl a := by
    intro a
    have hs := BstLean.Part162.latC_sq_le (paperDesignP k) c a
    obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
    have hV := VR_eq hn1 c hb a
    rw [fbR_eq] at hV
    unfold fbarS at hV
    rw [← var_eq i1 i2] at hV
    rw [hV, hVl]
    simp only [fX_eq_lam c]
    have hin : ∫ w, √(eR c) * lamX (paperDesignP k) c (xLat c (latC (paperDesignP k) c a)
        (unitF53 w)) ∂stdGauss (Fin (k - 1)) = √(eR c) * ∫ w, lamX (paperDesignP k) c
          (xLat c (latC (paperDesignP k) c a) (unitF53 w)) ∂stdGauss (Fin (k - 1)) :=
      integral_const_mul _ _
    rw [hin]
    have e2 : ∀ v, (√(eR c) * lamX (paperDesignP k) c (xLat c (latC (paperDesignP k) c a)
        (unitF53 v)) - √(eR c) * ∫ w, lamX (paperDesignP k) c (xLat c (latC (paperDesignP k) c a)
          (unitF53 w)) ∂stdGauss (Fin (k - 1))) ^ 2 =
        eR c * (lamX (paperDesignP k) c (xLat c (latC (paperDesignP k) c a) (unitF53 v)) -
          ∫ w, lamX (paperDesignP k) c (xLat c (latC (paperDesignP k) c a) (unitF53 w))
            ∂stdGauss (Fin (k - 1))) ^ 2 := by
      intro v; rw [← mul_sub, mul_pow, Real.sq_sqrt he.le]
    simp only [e2]
    exact integral_const_mul _ _
  have hcert := BstLean.Part212.fresh_LG_variance_lambda hn (paperDesignP k)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  change √(∫ a, Vl a ^ 2 ∂muI k) ≤ (C / eR c) / ((k : ℝ) * ((k : ℝ) - 3)) at hcert
  have hint : ∫ a, Vl a ^ 2 ∂muI k ≤ ((C / eR c) / ((k : ℝ) * ((k : ℝ) - 3))) ^ 2 :=
    (sqrt_le_iff.mp hcert).2
  obtain ⟨MV, bV⟩ := bdd_VR hn1 c
  have iV : Integrable (fun a => ((k : ℝ) * VR c a) ^ 2) (muI k) := by
    have hh := intOn_of_bdd (((measurable_VR c).const_mul (k : ℝ)).pow_const 2)
      (bdd_pow (bdd_nmul bV) 2) Set.univ
    simpa only [IntegrableOn, Measure.restrict_univ] using hh
  refine (setIntegral_le_integral iV
    (Filter.Eventually.of_forall fun a => sq_nonneg ((k : ℝ) * VR c a))).trans ?_
  have hid : (fun a => ((k : ℝ) * VR c a) ^ 2) =
      fun a => ((k : ℝ) * eR c) ^ 2 * Vl a ^ 2 := by
    funext a
    rw [hVe a]
    all_goals ring
  rw [hid, integral_const_mul]
  refine (mul_le_mul_of_nonneg_left hint (sq_nonneg _)).trans_eq ?_
  field_simp
  <;> ring


theorem variance_moment_row (c : Ret n) (he : 0 < eR c) {C : ℝ}
    (hC : 0 < C) (hC6 : C ≤ 16 / 5)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) (K : Set (Ix n)) :
    ∫ a in K, ((n : ℝ) * VR c a) ^ 2 ∂muI n ≤ varianceNorm ^ 2 := by
  band_bounds
  have hden : (0 : ℝ) < n - 3 := by linarith
  refine (variance_moment_of_latitude (by norm_num <;> try band_num) c he hC hk K).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num [varianceNorm] <;> try band_num
  all_goals band_linarith


theorem root_le_of_pow {x b : ℝ} {k : ℕ} (hk : k ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (h : x ≤ b ^ k) :
    x ^ (1 / (k : ℝ)) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [one_div, rpow_inv_natCast_pow hx hk]
  exact h


theorem gaussian80_le : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num <;> try band_num : (160 : ℕ) ≠ 0) (by norm_num <;> try band_num : (0 : ℝ) ≤ 8)
  rw [show (160 : ℕ) = 2 * 80 by norm_num <;> try band_num, gaussMomConst_pow (by norm_num <;> try band_num)]
  norm_num [Nat.factorial] <;> try band_num


theorem exact_radius_sq_row : exactRadius (n - 1 - 1) 80 ^ 2 ≤ (102 / 100 : ℝ) := by
  band_bounds
  have hd : ((n - 1 - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    all_goals ring
  have hp := exactRadius_pow (d := n - 1 - 1) (j := 80) (by omega) (by norm_num <;> try band_num)
  have hprod : radialProduct (n - 1 - 1) 80 ≤ ((n : ℝ) + 156) ^ 80 := by
    unfold radialProduct
    calc
      (∏ i ∈ Finset.range 80, (((n - 1 - 1 : ℕ) : ℝ) + 2 * (i : ℝ)))
          ≤ ∏ i ∈ Finset.range 80, ((n : ℝ) + 156) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i hi => ?_)
        have h : i ≤ 79 := by have := Finset.mem_range.mp hi; omega
        have hR : (i : ℝ) ≤ 79 := by exact_mod_cast h
        rw [hd]
        all_goals band_linarith
      _ = _ := by simp
  apply le_of_pow_le_pow_left₀ (by norm_num <;> try band_num : (80 : ℕ) ≠ 0)
    (by norm_num <;> try band_num : (0 : ℝ) ≤ 102 / 100)
  rw [← pow_mul, hp, hd, div_le_iff₀ (pow_pos (by band_linarith : (0 : ℝ) < n - 2 - 1) 80)]
  calc
    _ ≤ ((n : ℝ) + 156) ^ 80 := hprod
    _ ≤ ((102 / 100 : ℝ) * ((n : ℝ) - 2 - 1)) ^ 80 :=
      pow_le_pow_left₀ (by positivity) (by band_linarith) _
    _ = _ := by ring


theorem plane_envelope_row : planeEnvelope80 (mA n) ≤ (511 / 1000) * (n : ℝ) ^ 2 := by
  band_bounds
  have hr : (2 : ℝ) ^ (1 / 80 : ℝ) ≤ 102 / 100 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num <;> try band_num) (by norm_num <;> try band_num : (0 : ℝ) ≤ 2) (by norm_num <;> try band_num : (0 : ℝ) ≤ 102 / 100)
      (by norm_num <;> try band_num)
  have hs : √(80 : ℝ) ≤ 9 := (sqrt_le_iff).mpr ⟨by norm_num <;> try band_num, by norm_num <;> try band_num⟩
  have ht : √((mA n : ℝ) / 2 + 160) ≤ (708 / 1000) * n := by
    apply (sqrt_le_iff).mpr
    norm_num [mA] <;> try band_num
    all_goals band_nlinarith [sq_nonneg ((n : ℝ) - 12000)]
  unfold planeEnvelope80
  have h1 := mul_le_mul_of_nonneg_right hr
    (by norm_num [mA] <;> try band_num : (0 : ℝ) ≤ (mA n : ℝ) / 2 + 320)
  have h2 := mul_le_mul hs ht (sqrt_nonneg _) (by norm_num <;> try band_num : (0 : ℝ) ≤ 9)
  norm_num only [mA, Nat.cast_pow, Nat.cast_ofNat] at h1 h2 ⊢
  all_goals band_nlinarith [sq_nonneg ((n : ℝ) - 12000)]


theorem plane_squared_row : planeEnvelopeSquared160 n 4 ≤ (12 / 5 : ℝ) := by
  band_bounds
  have hr : (mA n : ℝ) ^ (1 / (80 * 4) : ℝ) ≤ 1063 / 1000 := by
    norm_num only [show (80 * 4 : ℝ) = 320 by norm_num] <;> try band_num
    have hp : (mA n : ℝ) ≤ (1063 / 1000 : ℝ) ^ (320 : ℕ) := by
      have h10 : (339 / 100 : ℝ) ≤ (1063 / 1000 : ℝ) ^ (20 : ℕ) := by norm_num <;> try band_num
      have h32 := pow_le_pow_left₀ (by norm_num <;> try band_num : (0 : ℝ) ≤ 339 / 100) h10 16
      rw [← pow_mul] at h32
      exact (by norm_num [mA] <;> band_num : (mA n : ℝ) ≤ (339 / 100 : ℝ) ^ (16 : ℕ)).trans h32
    exact_mod_cast root_le_of_pow (k := 320) (by norm_num <;> try band_num)
      (Nat.cast_nonneg (mA n)) (by norm_num <;> try band_num : (0 : ℝ) ≤ 1063 / 1000) hp
  unfold planeEnvelopeSquared160
  have hR := (exact_radius_sq_row (n := n))
  have hP := (plane_envelope_row (n := n))
  have hP0 : 0 ≤ planeEnvelope80 (mA n) := by unfold planeEnvelope80; positivity
  have hm := mul_le_mul hr (le_refl (((n - 1 - 1 : ℕ) : ℝ) + 160 * 4))
    (by positivity) (by norm_num <;> try band_num : (0 : ℝ) ≤ 1063 / 1000)
  have h1 := mul_le_mul hR hm (by positivity) (by norm_num <;> try band_num : (0 : ℝ) ≤ 102 / 100)
  have h2 := mul_le_mul_of_nonneg_right h1 (by norm_num <;> try band_num : (0 : ℝ) ≤ 2 / n)
  have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num [mA] <;> try band_num : (0 : ℝ) ≤ 2 / (mA n : ℝ))
  have h4 := mul_le_mul h3 hP hP0 (by norm_num [mA] <;> try band_num)
  refine h4.trans ?_
  simp (disch := omega) only [mA, Nat.cast_pow, Nat.cast_sub, Nat.cast_ofNat]
  field_simp
  nlinarith


theorem operator_envelope_row : operatorEnvelope160 n ≤ (144 / 100) * √(n : ℝ) := by
  band_bounds
  have hs : √(2 / (n : ℝ)) * √n = √2 := by
    rw [← sqrt_mul (by positivity), div_mul_cancel₀ _ bandPos.ne']
  have hn : (109 : ℝ) ≤ √n := le_sqrt_of_sq_le (by band_linarith)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num <;> try band_num)
  have hsn : √(2 / (n : ℝ)) ≤ 13 / 1000 := sqrt_le_iff.mpr ⟨by norm_num <;> try band_num, by band_num⟩
  have hh : √(mA n : ℝ) = n := by simp [mA]
  unfold operatorEnvelope160
  rw [hh]
  have he : √(2 / (n : ℝ)) * ((n : ℝ) + √n + gaussMomConst 80) =
      √2 * √n + √2 + √(2 / (n : ℝ)) * gaussMomConst 80 := by
    have hmain : √(2 / (n : ℝ)) * n = √2 * √n := by
      calc
        _ = (√(2 / (n : ℝ)) * √n) * √n := by
          rw [mul_assoc, ← pow_two, sq_sqrt bandPos.le]
        _ = _ := by rw [hs]
    simp only [mul_add, hmain, hs]
  rw [he]
  have hprod := mul_le_mul hsn gaussian80_le (gaussMomConst_nonneg 80) (by norm_num <;> try band_num)
  have hprod2 := mul_le_mul_of_nonneg_right h2 (sqrt_nonneg (n : ℝ))
  all_goals band_nlinarith


theorem jacobian_squared_row : latitudeJacobianSquared160 n 4 ≤ (5066 / 1000 : ℝ) := by
  band_bounds
  have hs : √(2 / (mA n : ℝ)) ≤ (117851131 / 1000000000000) := by
    apply (sqrt_le_iff).mpr
    norm_num [mA] <;> try band_num
  have hinner : planeEnvelopeSquared160 n 4 +
      2 / (mA n : ℝ) * frobEnvelopeSquared160 n ≤ (20981 / 10000 : ℝ) ^ 2 := by
    have hp := (plane_squared_row (n := n))
    norm_num [frobEnvelopeSquared160, mA] at *
    all_goals band_linarith
  have hr : √(planeEnvelopeSquared160 n 4 +
      2 / (mA n : ℝ) * frobEnvelopeSquared160 n) ≤ (20981 / 10000 : ℝ) :=
    (sqrt_le_iff).mpr ⟨by norm_num <;> try band_num, hinner⟩
  have ht : transverseConstant160 * √(2 / (mA n : ℝ)) *
      operatorEnvelope160 n ≤ (1524 / 10000 : ℝ) := by
    have h2 := mul_le_mul (mul_le_mul_of_nonneg_right gaussian80_le
      (sqrt_nonneg (2 / (mA n : ℝ)))) (operator_envelope_row (n := n))
      (operatorEnvelope_pos160 (by omega)).le (by positivity)
    have hsprod : √(2 / (mA n : ℝ)) * √(n : ℝ) = √(2 / (n : ℝ)) := by
      rw [← sqrt_mul (by positivity)]
      congr 1
      simp [mA]
      field_simp
    have hsn : √(2 / (n : ℝ)) ≤ 13 / 1000 := sqrt_le_iff.mpr ⟨by norm_num <;> try band_num, by band_num⟩
    change gaussMomConst 80 * _ * _ ≤ _
    calc
      _ ≤ 8 * √(2 / (mA n : ℝ)) * ((144 / 100) * √(n : ℝ)) := h2
      _ = (8 * (144 / 100)) * √(2 / (n : ℝ)) := by rw [← hsprod]; ring
      _ ≤ _ := by band_linarith
  unfold latitudeJacobianSquared160 jacobianConstantSquared160
  have hh : √(planeEnvelopeSquared160 n 4 +
      2 / (mA n : ℝ) * frobEnvelopeSquared160 n) +
      transverseConstant160 * √(2 / (mA n : ℝ)) * operatorEnvelope160 n ≤ 22506 / 10000 := by
    all_goals band_linarith
  have hh0 : 0 ≤ √(planeEnvelopeSquared160 n 4 +
      2 / (mA n : ℝ) * frobEnvelopeSquared160 n) +
      transverseConstant160 * √(2 / (mA n : ℝ)) * operatorEnvelope160 n :=
    add_nonneg (sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (gaussMomConst_nonneg 80) (sqrt_nonneg _))
      (operatorEnvelope_pos160 (by norm_num <;> try band_num)).le)
  exact (pow_le_pow_left₀ hh0 hh 2).trans (by norm_num <;> try band_num)


theorem latitude_constant_sharp_row : freshLatitudeConstant160 n 4 (55 / 100) ≤ (16 / 5 : ℝ) := by
  band_bounds
  have hr : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1132 / 1000 := by
    simpa only [Nat.cast_ofNat] using root_le_of_pow (k := 80)
      (by norm_num <;> try band_num) (by norm_num <;> try band_num : (0 : ℝ) ≤ 20000) (by norm_num <;> try band_num : (0 : ℝ) ≤ 1132 / 1000)
      (by norm_num <;> try band_num)
  have hl : latitudeCoefficient n 12 (55 / 100) ≤ (554 / 1000 : ℝ) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient]
    have hden : (0 : ℝ) < 1 - 55 / 2 / (n : ℝ) := by interval_num
    calc
      _ = (11 / 20 : ℝ) * (1 + 45 / n) / (1 - (55 / 2 : ℝ) / n) := by
        field_simp [bandPos.ne', hden.ne'] <;> ring
      _ ≤ _ := by interval_num
  have hl0 : 0 ≤ latitudeCoefficient n 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient] <;> try band_num
  unfold freshLatitudeConstant160 latitudeConstant
  rw [sq_sqrt (latitudeJacobianSquared_pos160 (by norm_num <;> try band_num) (by norm_num <;> try band_num)).le]
  norm_num only [show (2 / (1 / 10000) : ℝ) = 20000 by norm_num] <;> try band_num
  have h1 := mul_le_mul hr (jacobian_squared_row (n := n))
    (latitudeJacobianSquared_pos160 (by norm_num <;> try band_num) (by norm_num <;> try band_num)).le (by norm_num <;> try band_num)
  have hh := mul_le_mul h1 hl hl0 (by norm_num <;> try band_num : (0 : ℝ) ≤ 1132 / 1000 * (5066 / 1000))
  norm_num only [Nat.cast_ofNat] at *
  exact hh.trans (by norm_num <;> try band_num)


abbrev passEvent := BstLean.Part262.passEvent n

theorem window_winC {k : ℕ} (hn : 1 ≤ k) (c : Ret k) (hw : WINDOW (paperDesignP k) c) :
    BstLean.Part166.winC c.1.2 ((paperDesignP k).tau0 c) := by
  have hnR : (0 : ℝ) < k := by exact_mod_cast hn
  have hden : 0 < normSq c.1.2 + (k : ℝ) * (paperDesignP k).tau0 c ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hnR (sq_pos_of_pos hw.2.1))
  refine ⟨hw.2.1, ?_, ?_⟩
  all_goals unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
  all_goals rw [sq_sqrt hden.le]
  · exact (le_div_iff₀ hden).mpr hw.2.2.1
  · apply (div_le_iff₀ hden).mpr
    have hh := hw.2.2.2
    all_goals band_nlinarith


theorem fresh_latitude_constant_pos_row : 0 < freshLatitudeConstant160 n 4 (55 / 100) := by
  band_bounds
  unfold freshLatitudeConstant160 latitudeConstant
  have hJ := latitudeJacobianSquared_pos160 (n := n) (q := 4) (by norm_num <;> try band_num) (by norm_num <;> try band_num)
  have hL : 0 < latitudeCoefficient n 12 (55 / 100) := by
    norm_num [latitudeCoefficient, inverseLatitudeCoefficient] <;> try band_num
  positivity


theorem pass_moments_of_events (c : Ret n) (hw : WINDOW (paperDesignP n) c)
    (he : 0 < eR c) (hc : c ∈ (passEvent (n := n))) (K : Set (Ix n))
    (hW : ∫ a in K, ((n : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI n ≤ energyError ^ 8)
    (hF : ∫ a in K, ((n : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI n ≤ locationError ^ 8) :
    PaperMoments c K varianceMax energyError locationError locationNorm varianceNorm := by
  band_bounds
  have hE := hc.1.1.1.1 hw.2.1
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num <;> try band_num) c hw)
  refine ⟨?_, hW, hF, ?_, ?_, ?_⟩
  · intro a _
    exact (variance_of_matrix_events (n := n)) c he hw.2.1 hc.1.1.2 hc.1.2 a
  · exact (full_location_moment_row (n := n)) c hw.1 hw.2.1 hE (by norm_num <;> try band_num) (by decide) (by norm_num <;> try band_num) K
  · exact (full_location_moment_row (n := n)) c hw.1 hw.2.1 hE (by norm_num <;> try band_num) (by decide) (by norm_num <;> try band_num) K
  · exact (variance_moment_row (n := n)) c he (fresh_latitude_constant_pos_row (n := n)) (latitude_constant_sharp_row (n := n)) hL K


theorem pass_centre_of_events (c : Ret n) (hc : c ∈ (passEvent (n := n))) :
    normSq c.2.1.2 ≤ (2 / (n : ℝ)) * eR c * n * chi :=
  (outputCentre_row (n := n)) hc.2


abbrev analyticBase := BstLean.Part262.analyticBase n

structure AnalyticBaseCertificate : Prop where
  pass_fields : (analyticBase (n := n)) ⊆ (passEvent (n := n))
  centre_sources : (analyticBase (n := n)) ⊆ agentEv (paperDesignP n) (CentreSources n n)
  direction : (analyticBase (n := n)) ⊆ agentEv (paperDesignP n) (DirectionError n)
  angles : (analyticBase (n := n)) ⊆ BstLean.Part262.worldAngles n

theorem analyticBaseCertificate : (AnalyticBaseCertificate (n := n)) :=
  ⟨fun _ h => h.1.1.1, fun _ h => h.1.2, fun _ h => h.1.1.2, fun _ h => h.2⟩

theorem wn_upper : BstLean.Part153.wn n ≤ 1.036849 := by
  band_bounds
  have hn : (109.544 : ℝ) ≤ √n := le_sqrt_of_sq_le (by norm_num <;> try band_num)
  unfold BstLean.Part153.wn
  try simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (109.544 : ℝ)) ^ 2 := by gcongr <;> band_linarith
    _ ≤ (1.036849 : ℝ) := by norm_num <;> try band_num


theorem cs_lower : (1.29521 : ℝ) ≤ BstLean.Part154.csC := by
  unfold BstLean.Part154.csC
  have hp := pi_gt_d6
  have hdiv : 1 / π ≤ (1 : ℝ) / 3.141592 :=
    div_le_div_of_nonneg_left (by norm_num <;> try band_num) (by norm_num <;> try band_num) hp.le
  all_goals band_linarith


theorem deltaChi_upper : BstLean.Part154.deltaChi n 12 ≤ 0.000578 := by
  band_bounds
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num <;> try band_num)
  unfold BstLean.Part154.deltaChi
  try simp only [Nat.cast_ofNat]
  all_goals band_linarith


theorem finite_centre_upper : BstLean.Part211.finiteEnergy n n (11 / 1000) ≤
    0.0102 := by
  band_bounds
  have ha := BstLean.Part150.alphaJ_le (by norm_num <;> try band_num : 1000 ≤ n)
  have hb := BstLean.Part150.betaJ_le (by norm_num <;> try band_num : 4096 ≤ n)
  norm_num only [Nat.cast_ofNat] at ha hb
  have ha0 := BstLean.Part150.alphaJ_nonneg n
  have hb0 := BstLean.Part150.betaJ_nonneg n
  have hw := (wn_upper (n := n))
  have hw0 : 0 ≤ BstLean.Part153.wn n := by unfold BstLean.Part153.wn; positivity
  have hc := cs_lower
  have hdc := (deltaChi_upper (n := n))
  have hdc0 : 0 ≤ BstLean.Part154.deltaChi n 12 := by
    unfold BstLean.Part154.deltaChi
    positivity
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by band_linarith)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) *
      (1 + 2 * BstLean.Part153.wn n * BstLean.Part150.betaJ n) * n) ≤
      182 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num <;> try band_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) *
          (1 + 2 * 1.036849 * (81 / 1000 / n)) * n := by gcongr <;> band_linarith
      _ ≤ (182 : ℝ) ^ 2 := by band_num
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * BstLean.Part153.wn n * n *
      (1 + BstLean.Part154.deltaChi n 12 + 2 / π) / BstLean.Part154.csC) ≤
      208 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num <;> try band_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * 1.036849 * n *
          (1 + 0.000578 + 2 / 3.141592) / 1.29521 := by gcongr <;> band_linarith
      _ ≤ (208 : ℝ) ^ 2 := by band_num
  have hroot3 : √((n : ℝ) / BstLean.Part154.csC) ≤ 112 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num <;> try band_num, ?_⟩
    calc
      _ ≤ (n : ℝ) / 1.29521 := div_le_div_of_nonneg_left (by norm_num <;> try band_num) (by norm_num <;> try band_num) hc
      _ ≤ (112 : ℝ) ^ 2 := by band_num
  unfold BstLean.Part211.finiteEnergy BstLean.Part150.epsJ
  try simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1792 / 10000 / n : ℝ) * 182 +
        2 * (1792 / 10000 / n) * 208 +
        4 * (1 / 2.506628) * 1.036849 * 112 *
          (81 / 1000 / n + (1792 / 10000 / n) ^ 2) := by gcongr <;> band_linarith
    _ ≤ (0.0102 : ℝ) := by band_num


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
      π / 2 + arcsin q := by band_linarith
  exact add_le_add hroot (mul_le_mul_of_nonneg_left hangle hq)


theorem noise_tail_bounds : 0 ≤ 2 * √(12 : ℝ) / (n : ℝ) ∧
    2 * √(12 : ℝ) / (n : ℝ) ≤ 7 / 12000 := by
  band_bounds
  have hs : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num)
  exact ⟨by positivity, div_le_div₀ (by norm_num)
    (by linarith : 2 * √(12 : ℝ) ≤ 7) (by norm_num) bandLower⟩

theorem energy_g_bounds : (998 / 1000 : ℝ) ≤ gMinus n ∧
    1 ≤ gPlus n ∧ gPlus n ≤ 1002 / 1000 := by
  band_bounds
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (n : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num <;> try band_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num <;> try band_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  have hd := noise_tail_bounds (n := n)
  have hz : (999 / 1000 : ℝ) ≤ √(1 - 2 / (n : ℝ) ^ 2) -
      2 * √12 / (n : ℝ) := by linarith only [hs, hd.2]
  have hz2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 999 / 1000) hz 2
  unfold gMinus gPlus
  try simp only [Nat.cast_ofNat]
  refine ⟨by nlinarith only [hz2], ?_, ?_⟩
  · nlinarith only [hd.1, sq_nonneg (2 * √(12 : ℝ) / (n : ℝ))]
  · exact (pow_le_pow_left₀ (by positivity)
      (show 1 + 2 * √(12 : ℝ) / (n : ℝ) ≤ 1 + 7 / 12000 by linarith only [hd.2]) 2).trans
      (by norm_num)


theorem energy_g_root_guard :
    2 * √12 / (n : ℝ) < √(1 - 2 / (n : ℝ) ^ 2) := by
  band_bounds
  have hs : (9999 / 10000 : ℝ) ≤ √(1 - 2 / (n : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by norm_num <;> try band_num)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num <;> try band_num)
  all_goals band_linarith


theorem energy_ratio_coarse : energyRatio n (gMinus n) (54 / 100) ≤ 78 / 100 := by
  band_bounds
  have hκ := BstLean.Part219.kappa_chord (by norm_num <;> try band_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num <;> try band_num)
  have hr : √(kappa (54 / 100) + 5 / (n : ℝ)) ≤ 878 / 1000 :=
    sqrt_le_iff.mpr ⟨by norm_num <;> try band_num, by band_linarith⟩
  have hmean : meanRoot n (54 / 100) ≤ 879 / 1000 := by
    unfold meanRoot
    try simp only [Nat.cast_ofNat]
    linarith only [hr, (noise_tail_bounds (n := n)).2]
  have hmean0 : 0 ≤ meanRoot n (54 / 100) := by unfold meanRoot; positivity
  have hg := (energy_g_bounds (n := n)).1
  unfold energyRatio
  rw [div_le_iff₀ (by band_linarith : 0 < gMinus n)]
  all_goals band_nlinarith


theorem energy_upper_coarse :
    energyUpper n (gMinus n) (gPlus n)
      (finiteEnergy n n (11 / 1000)) (54 / 100) ≤ 9 / 10 := by
  band_bounds
  have hg := (energy_g_bounds (n := n))
  have hr := (energy_ratio_coarse (n := n))
  have hr0 : 0 ≤ energyRatio n (gMinus n) (54 / 100) := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) (by band_linarith [hg.1])
  have hk := BstLean.Part219.kappa_chord
    (show energyRatio n (gMinus n) (54 / 100) ∈ Icc (-1 : ℝ) 1 by constructor <;> band_linarith)
  have hkp := (kappa_mem (by band_linarith : -1 ≤ energyRatio n (gMinus n) (54 / 100))
    (by band_linarith : energyRatio n (gMinus n) (54 / 100) ≤ 1)).1
  have hmul := mul_le_mul hg.2.2 (show kappa (energyRatio n (gMinus n) (54 / 100)) ≤
      89 / 100 by band_linarith) hkp (by norm_num <;> try band_num : (0 : ℝ) ≤ 1002 / 1000)
  have hs : √(gPlus n * kappa (energyRatio n (gMinus n) (54 / 100))) ≤
      945 / 1000 := sqrt_le_iff.mpr ⟨by norm_num <;> try band_num, by band_linarith⟩
  have ht : √(12 * gPlus n) ≤ 7 / 2 := sqrt_le_iff.mpr ⟨by norm_num <;> try band_num, by band_linarith [hg.2.2]⟩
  have hn : ((13693 / 125) : ℝ) ≤ √n := le_sqrt_of_sq_le (by norm_num <;> try band_num)
  have hf := (finite_centre_upper (n := n))
  have hf0 := finiteEnergy_nonneg n n (by norm_num <;> try band_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy n n (11 / 1000) / √n ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by band_linarith : (0 : ℝ) < √n)]
    all_goals band_linarith
  unfold energyUpper
  try simp only [Nat.cast_ofNat]
  have h0 : 0 ≤ √(gPlus n * kappa (energyRatio n (gMinus n) (54 / 100))) +
      2 * √(12 * gPlus n) / n + finiteEnergy n n (11 / 1000) / √n := by
    positivity
  have htdiv : 2 * √(12 * gPlus n) / (n : ℝ) ≤ 7 / 12000 :=
    div_le_div₀ (by norm_num) (by linarith : 2 * √(12 * gPlus n) ≤ 7)
      (by norm_num) bandLower
  have hsum : √(gPlus n * kappa (energyRatio n (gMinus n) (54 / 100))) +
      2 * √(12 * gPlus n) / (n : ℝ) + finiteEnergy n n (11 / 1000) / √n ≤
      946 / 1000 := by linarith only [hs, htdiv, hfd]
  exact (pow_le_pow_left₀ h0 hsum 2).trans (by norm_num)


theorem energy_mean_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (759 / 1000 : ℝ) ≤ meanLowerRoot n θ ∧ meanLowerRoot n θ ≤ 1 := by
  band_bounds
  have hk : (58 / 100 : ℝ) ≤ kappa (46 / 100) := by
    apply kernel_lower_rational (s := 887 / 1000) <;> norm_num <;> try band_num
  have hκ := kappa_monotoneOn (by norm_num <;> try band_num : (46 / 100 : ℝ) ∈ Icc (-1) 1)
    (show 1 - θ ∈ Icc (-1 : ℝ) 1 from ⟨by band_linarith [hw.2], by band_linarith [hw.1]⟩)
    (by band_linarith [hw.2])
  have hk1 := (kappa_mem (by band_linarith [hw.2] : -1 ≤ 1 - θ)
    (by band_linarith [hw.1] : 1 - θ ≤ 1)).2
  have hκlo : (58 / 100 : ℝ) ≤ kappa (1 - θ) := hk.trans hκ
  have hθlo := hw.1
  have hθhi := hw.2
  have hs : (76 / 100 : ℝ) ≤ √(kappa (1 - θ) - 8 * θ / n - 2 / (n : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by interval_num)
  have hs1 : √(kappa (1 - θ) - 8 * θ / n - 2 / (n : ℝ) ^ 2) ≤ 1 :=
    sqrt_le_iff.mpr ⟨by norm_num <;> try band_num, by band_linarith [hw.1]⟩
  have ht : √(12 : ℝ) ≤ 7 / 2 := sqrt_le_iff.mpr (by norm_num <;> try band_num)
  have ht0 := sqrt_nonneg (12 : ℝ)
  unfold meanLowerRoot
  try simp only [Nat.cast_ofNat]
  have hd := noise_tail_bounds (n := n)
  constructor <;> linarith only [hs, hs1, hd.1, hd.2]


theorem energy_lower_components {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    0 ≤ kappa (meanLowerRoot n θ ^ 2 / gPlus n) - 2 / (n : ℝ) ^ 2 ∧
    (804 / 1000 : ℝ) ≤
      √(gMinus n * (kappa (meanLowerRoot n θ ^ 2 / gPlus n) -
        2 / (n : ℝ) ^ 2)) - 2 * √(12 * gPlus n) / n -
        finiteEnergy n n (11 / 1000) / √n := by
  band_bounds
  have hm := (energy_mean_lower_coarse (n := n)) hw
  have hg := (energy_g_bounds (n := n))
  have hr : (57 / 100 : ℝ) ≤ meanLowerRoot n θ ^ 2 / gPlus n := by
    rw [le_div_iff₀ (by band_linarith [hg.2.1] : 0 < gPlus n)]
    all_goals band_nlinarith [hg.2.2]
  have hr1 : meanLowerRoot n θ ^ 2 / gPlus n ≤ 1 := by
    rw [div_le_iff₀ (by band_linarith [hg.2.1] : 0 < gPlus n)]
    all_goals band_nlinarith [hg.2.1]
  have hk : (65 / 100 : ℝ) ≤ kappa (57 / 100) := by
    apply kernel_lower_rational (s := 821 / 1000) <;> norm_num <;> try band_num
  have hκ := kappa_monotoneOn (by norm_num <;> try band_num : (57 / 100 : ℝ) ∈ Icc (-1) 1)
    (show meanLowerRoot n θ ^ 2 / gPlus n ∈ Icc (-1 : ℝ) 1 by
      exact ⟨by band_linarith, hr1⟩) hr
  have hbr : (65 / 100 : ℝ) - 2 / n ^ 2 ≤
      kappa (meanLowerRoot n θ ^ 2 / gPlus n) - 2 / (n : ℝ) ^ 2 := by
    all_goals band_linarith
  have hs : (805 / 1000 : ℝ) ≤ √(gMinus n *
      (kappa (meanLowerRoot n θ ^ 2 / gPlus n) - 2 / (n : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    have hp := mul_le_mul hg.1 hbr (by norm_num <;> try band_num : (0 : ℝ) ≤ 65 / 100 - 2 / n ^ 2)
      (by band_linarith [hg.1] : 0 ≤ gMinus n)
    exact (show (805 / 1000 : ℝ) ^ 2 ≤
      (998 / 1000) * (65 / 100 - 2 / (n : ℝ) ^ 2) by interval_num).trans hp
  have ht : √(12 * gPlus n) ≤ 7 / 2 :=
    sqrt_le_iff.mpr ⟨by norm_num <;> try band_num, by band_linarith [hg.2.2]⟩
  have hn : ((13693 / 125) : ℝ) ≤ √n := le_sqrt_of_sq_le (by norm_num <;> try band_num)
  have hf := (finite_centre_upper (n := n))
  have hfd : finiteEnergy n n (11 / 1000) / √n ≤ 1 / 10000 := by
    rw [div_le_iff₀ (by band_linarith : (0 : ℝ) < √n)]
    all_goals band_linarith
  have htdiv : 2 * √(12 * gPlus n) / (n : ℝ) ≤ 7 / 12000 := by
    exact div_le_div₀ (by norm_num) (by linarith : 2 * √(12 * gPlus n) ≤ 7)
      (by norm_num) bandLower
  constructor
  · have hsmall : (2 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 1000 := by interval_num
    linarith only [hk, hκ, hsmall]
  · linarith only [hs, htdiv, hfd]


theorem energy_lower_coarse {θ : ℝ} (hw : θ ∈ Icc (46 / 100 : ℝ) (54 / 100)) :
    (6 / 10 : ℝ) ≤ energyLower n (gMinus n) (gPlus n)
      (finiteEnergy n n (11 / 1000)) θ := by
  band_bounds
  have hh := ((energy_lower_components (n := n)) hw).2
  unfold energyLower
  try simp only [Nat.cast_ofNat]
  all_goals band_nlinarith


theorem computed_energy_eq (c : Ret n) (hτ : 0 < (paperDesignP n).tau0 c) :
    eR c = (2 / (mA n : ℝ)) *
      normSq (BstLean.Part150.bT n n (A1 c) (A2 c) c.1.2
        ((paperDesignP n).tau0 c)) /
      (2 / (n : ℝ) * BstLean.Part150.rhoC c.1.2 ((paperDesignP n).tau0 c) ^ 2) := by
  band_bounds
  have hb : bR c = (BstLean.Part150.rhoC c.1.2 ((paperDesignP n).tau0 c))⁻¹ •
      BstLean.Part150.bT n n (A1 c) (A2 c) c.1.2 ((paperDesignP n).tau0 c) := by
    ext j
    change bAp c.1 c.2.1.1 j = _
    simp only [bAp, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rfl
  calc
    eR c = (2 / (mA n : ℝ)) * normSq (bR c) / (2 / (n : ℝ)) := by
      norm_num [eR, mA] <;> try band_num
      all_goals ring
    _ = _ := by
      rw [hb]
      exact computed_hidden_normalization (by norm_num <;> try band_num) (A1 c) (A2 c) c.1.2 hτ


theorem centre_energy_range {c : Ret n}
    (hw : BstLean.Part161.WINDOW (paperDesignP n) c) (hc : c ∈ (analyticBase (n := n))) :
    (6 / 10 : ℝ) ≤ eR c ∧ eR c ≤ 9 / 10 := by
  band_bounds
  have hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈
      Icc (46 / 100 : ℝ) (54 / 100) := by
    have hn : 0 < normSq c.1.2 + (n : ℝ) * (paperDesignP n).tau0 c ^ 2 :=
      add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (by norm_num <;> try band_num) (sq_pos_of_pos hw.2.1))
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    norm_num only [Nat.cast_ofNat] <;> try band_num
    rw [sq_sqrt hn.le]
    constructor
    · apply (le_div_iff₀ hn).mpr
      convert hw.2.2.1 using 1 <;> norm_num <;> try band_num
    · apply (div_le_iff₀ hn).mpr
      convert hw.2.2.2 using 1 <;> norm_num <;> try band_num
  have hsrc := (analyticBaseCertificate (n := n)).centre_sources hc hw.2.1
  have hE : (A1 c, A2 c) ∈ EnergySource n n c.1.2 ((paperDesignP n).tau0 c) :=
    hsrc.1.1
  have hg := (energy_g_bounds (n := n))
  have hmean := (energy_mean_lower_coarse (n := n)) hθ
  have hlow := (energy_lower_components (n := n)) hθ
  have h := computed_energy_on_source (by norm_num <;> try band_num) (by norm_num <;> try band_num) c.1.2 hw.2.1
    (by norm_num <;> try band_num : (0 : ℝ) ≤ 11 / 1000) (by norm_num <;> try band_num : (54 / 100 : ℝ) ∈ Icc (-1) 1)
    (by band_linarith [hθ.1]) (energy_g_root_guard (n := n)) (by band_linarith [hg.2.2])
    ((energy_ratio_coarse (n := n)).trans (by norm_num <;> try band_num)) (by band_linarith [hmean.1]) hlow.1
    (by band_linarith [hlow.2]) hE
  rw [(computed_energy_eq (n := n)) c hw.2.1]
  exact ⟨((energy_lower_coarse (n := n)) hθ).trans h.1, h.2.trans (energy_upper_coarse (n := n))⟩




noncomputable def rowSplit (c : Ret n) (wl ws : ℝ) : SplitData n :=
  BstLean.Part162.dPaper (paperDesignP n) c wl ws
    (√(2 / (n : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (n : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (n : ℝ) * mixtureFloor)) ^ 2 := by
  band_bounds
  rw [Real.sq_sqrt (by norm_num [mixtureFloor] <;> try band_num)]
  unfold biasFloor
  all_goals ring

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 n 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret n) (q : ℕ) : ℝ :=
  rotationConstant q * √(((latitudeC (n := n)) / eR c) /
    ((n : ℝ) * (n - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * (latitudeC (n := n)) / n) /
    ((n : ℝ) * (n - 1 - 2 * q)))

theorem rotation_positive (q : ℕ) : 0 < rotationConstant q := by
  have ho : 0 < oddMoment q := by
    unfold oddMoment
    exact Finset.prod_pos (fun j _ => by positivity)
  unfold rotationConstant
  split_ifs
  · norm_num <;> try band_num
  · exact mul_pos (by positivity) (Real.rpow_pos_of_pos ho _)

theorem locationMomentBudget_pos {c : Ret n} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < (locationMomentBudget (n := n)) c q := by
  band_bounds
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < (latitudeC (n := n)) := (fresh_latitude_constant_pos_row (n := n))
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num <;> try band_num) (by band_linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < (residualMomentBudget (n := n)) q := by
  band_bounds
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < (latitudeC (n := n)) := (fresh_latitude_constant_pos_row (n := n))
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num <;> try band_num) (by band_linarith))))

theorem location_moment_on_event {c : Ret n}
    (hw : WINDOW (paperDesignP n) c) (he : 0 < eR c) (hc : c ∈ (passEvent (n := n)))
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP n) c a v - lbar (paperDesignP n) c a| ^ (2 * q)
      ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (locationMomentBudget (n := n)) c q ^ (2 * q) := by
  band_bounds
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num <;> try band_num) c hw)
  exact fresh_LG_lambda (by norm_num <;> try band_num) (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c (fresh_latitude_constant_pos_row (n := n)) he hL hq hq12

theorem residual_moment_on_event {c : Ret n}
    (hw : WINDOW (paperDesignP n) c) (hc : c ∈ (passEvent (n := n)))
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP n) c a v - gbar (paperDesignP n) c a| ^ (2 * q)
      ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (residualMomentBudget (n := n)) q ^ (2 * q) := by
  band_bounds
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num <;> try band_num) c hw)
  exact fresh_LG_residual (by norm_num <;> try band_num) (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c (fresh_latitude_constant_pos_row (n := n)) hL hq hq12

noncomputable def splitLocationWidth (c : Ret n) : ℝ := 4 * (locationMomentBudget (n := n)) c 12

noncomputable def splitResidualWidth : ℝ := 4 * (residualMomentBudget (n := n)) 12

noncomputable def lowMassBudget : ℝ := 4 / 10 ^ 12

noncomputable def fullResidualBudget : ℝ := √(2 / (n : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret n)
    (p : Ix n × (Fin (n - 1) → ℝ)) :
    sgA (paperDesignP n) c p.1 p.2 ^ 2 ≤
      (2 / (n : ℝ)) * wLatitude c p := by
  band_bounds
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP n).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP n) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] <;> try band_num : (0 : ℝ) ≤ 2 / (mA n : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA n : ℝ) * _ ≤ 2 / n *
    (normSq (hid2 (A1 c) (A2 c) _) / n)
  norm_num [mA] <;> try band_num
  all_goals band_linarith

theorem full_residual_eighth {c : Ret n}
    (hw : WINDOW (paperDesignP n) c) (hc : c ∈ (passEvent (n := n))) :
    ∫ a, ∫ v, sgA (paperDesignP n) c a v ^ 8
      ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (fullResidualBudget (n := n)) ^ 8 := by
  band_bounds
  let μ := (muI n).prod (stdGauss (Fin (n - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num <;> try band_num)
    (paperDesignP n) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num <;> try band_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance n) :=
    h32.lower (by norm_num <;> try band_num) (by norm_num <;> try band_num) (by norm_num <;> try band_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num <;> try band_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num <;> try band_num)
  have hn := (h1.add (by norm_num <;> try band_num) h8).scale (by norm_num <;> try band_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (n : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP n) c p.1 p.2)
      (√(2 / (n : ℝ)) * (1 + BstLean.Part222.energyAllowance n)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt ((residual_sq_le_energy (n := n)) c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num <;> try band_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (n : ℝ)))
    all_goals band_nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP n) c p.1 p.2) (fullResidualBudget (n := n)) := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := (energy_allowance_row (n := n))
    unfold locationNorm
    all_goals band_linarith
  have hp := (hs'.toMoment (by norm_num <;> try band_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num <;> try band_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * (residualMomentBudget (n := n)) 4 ^ 2 * (fullResidualBudget (n := n)) ^ 2

theorem scale_variance_on_event {c : Ret n}
    (hw : WINDOW (paperDesignP n) c) (hc : c ∈ (passEvent (n := n))) :
    ∫ a, (∫ v, (sA (paperDesignP n) c a v -
      ∫ w, sA (paperDesignP n) c a w ∂stdGauss (Fin (n - 1))) ^ 2
      ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ (scaleVarianceBudget (n := n)) ^ 2 :=
  int_VS_le (by norm_num <;> try band_num) (paperDesignP n) c
    ((residualMomentBudget_pos (n := n)) (by norm_num <;> try band_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    ((residual_moment_on_event (n := n)) hw hc (by norm_num <;> try band_num : 1 ≤ 4) (by norm_num <;> try band_num))
    ((full_residual_eighth (n := n)) hw hc)

noncomputable def locationVarianceBudget (c : Ret n) : ℝ :=
  ((latitudeC (n := n)) / eR c) / ((n : ℝ) * (n - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * (latitudeC (n := n)) / n) / ((n : ℝ) * (n - 3))

theorem location_variance_on_event {c : Ret n}
    (hw : WINDOW (paperDesignP n) c) (he : 0 < eR c) (hc : c ∈ (passEvent (n := n))) :
    ∫ a, (∫ v, (lA (paperDesignP n) c a v - lbar (paperDesignP n) c a) ^ 2
      ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ (locationVarianceBudget (n := n)) c ^ 2 := by
  band_bounds
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num <;> try band_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num <;> try band_num) (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c (fresh_latitude_constant_pos_row (n := n)) he hL
  have hC : 0 < (latitudeC (n := n)) := (fresh_latitude_constant_pos_row (n := n))
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret n}
    (hw : WINDOW (paperDesignP n) c) (hc : c ∈ (passEvent (n := n))) :
    ∫ a, (∫ v, (sgA (paperDesignP n) c a v - gbar (paperDesignP n) c a) ^ 2
      ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ (residualVarianceBudget (n := n)) ^ 2 := by
  band_bounds
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num <;> try band_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num <;> try band_num) (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c (fresh_latitude_constant_pos_row (n := n)) hL
  exact (sqrt_le_iff.mp hh).2


/-- All twenty-eight fields concern the original retained network and latitude measure. -/

noncomputable def latitudeMoments {c : Ret n}
    (hw : WINDOW (paperDesignP n) c) (he : 0 < eR c) (hc : c ∈ (passEvent (n := n)))
    (hmass : ∫ a, (stdGauss (Fin (n - 1))).real
      {v | sgA (paperDesignP n) c a v < √(2 / (n : ℝ) * mixtureFloor)}
      ∂muI n ≤ lowMassBudget) :
    LatMom (paperDesignP n) c (√(2 / (n : ℝ) * mixtureFloor)) 24 where
  Vs := (residualVarianceBudget (n := n))
  Vl := (locationVarianceBudget (n := n)) c
  VS := (scaleVarianceBudget (n := n))
  ts8 := (residualMomentBudget (n := n)) 4
  ts12 := (residualMomentBudget (n := n)) 6
  tl8 := (locationMomentBudget (n := n)) c 4
  tl12 := (locationMomentBudget (n := n)) c 6
  tlq := (locationMomentBudget (n := n)) c 12
  tsq := (residualMomentBudget (n := n)) 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < (latitudeC (n := n)) := (fresh_latitude_constant_pos_row (n := n))
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num <;> try band_num) hC.le) (by norm_num <;> try band_num))
      (by norm_num <;> try band_num)
  hVl0 := by
    have hC : 0 < (latitudeC (n := n)) := (fresh_latitude_constant_pos_row (n := n))
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num <;> try band_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num <;> try band_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := (residualMomentBudget_pos (n := n)) (by norm_num <;> try band_num)
  hts12 := (residualMomentBudget_pos (n := n)) (by norm_num <;> try band_num)
  htl8 := (locationMomentBudget_pos (n := n)) he (by norm_num <;> try band_num)
  htl12 := (locationMomentBudget_pos (n := n)) he (by norm_num <;> try band_num)
  htlq := ((locationMomentBudget_pos (n := n)) he (by norm_num <;> try band_num)).le
  htsq := ((residualMomentBudget_pos (n := n)) (by norm_num <;> try band_num)).le
  hβl := by norm_num [lowMassBudget] <;> try band_num
  hVs := (residual_variance_on_event (n := n)) hw hc
  hVl := (location_variance_on_event (n := n)) hw he hc
  hVS := (scale_variance_on_event (n := n)) hw hc
  hs8 := (residual_moment_on_event (n := n)) hw hc (by norm_num <;> try band_num : 1 ≤ 4) (by norm_num <;> try band_num)
  hs12 := (residual_moment_on_event (n := n)) hw hc (by norm_num <;> try band_num : 1 ≤ 6) (by norm_num <;> try band_num)
  hl8 := (location_moment_on_event (n := n)) hw he hc (by norm_num <;> try band_num : 1 ≤ 4) (by norm_num <;> try band_num)
  hl12 := (location_moment_on_event (n := n)) hw he hc (by norm_num <;> try band_num : 1 ≤ 6) (by norm_num <;> try band_num)
  hlq := (location_moment_on_event (n := n)) hw he hc (by norm_num <;> try band_num : 1 ≤ 12) (by norm_num <;> try band_num)
  hsq := (residual_moment_on_event (n := n)) hw hc (by norm_num <;> try band_num : 1 ≤ 12) (by norm_num <;> try band_num)
  hmass := hmass

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by band_linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem rotation_four : rotationConstant 4 ≤ 285 / 100 := by
  apply rotation_rational_bound <;> norm_num [Finset.prod_range_succ] <;> try band_num

theorem rotation_six : rotationConstant 6 ≤ 35 / 10 := by
  apply rotation_rational_bound <;> norm_num [Finset.prod_range_succ] <;> try band_num

theorem rotation_twelve : rotationConstant 12 ≤ 48 / 10 := by
  apply rotation_rational_bound <;> norm_num [Finset.prod_range_succ] <;> try band_num

theorem location_budget_cap {c : Ret n} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((n : ℝ) * (n - 1 - 2 * q))) ≤ b ^ 2) :
    (locationMomentBudget (n := n)) c q ≤ b := by
  band_bounds
  have he0 : 0 < eR c := by band_linarith
  have hC : 0 < (latitudeC (n := n)) := (fresh_latitude_constant_pos_row (n := n))
  have hCu : (latitudeC (n := n)) ≤ 16 / 5 := (latitude_constant_sharp_row (n := n))
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (n : ℝ) * (n - 1 - 2 * q) := by band_nlinarith
  have hce : (latitudeC (n := n)) / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    all_goals band_linarith
  apply le_of_pow_le_pow_left₀ (by norm_num <;> try band_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / n : ℝ) /
      ((n : ℝ) * (n - 1 - 2 * q))) ≤ b ^ 2) : (residualMomentBudget (n := n)) q ≤ b := by
  band_bounds
  have hC : 0 < (latitudeC (n := n)) := (fresh_latitude_constant_pos_row (n := n))
  have hCu : (latitudeC (n := n)) ≤ 16 / 5 := (latitude_constant_sharp_row (n := n))
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (n : ℝ) * (n - 1 - 2 * q) := by band_nlinarith
  have hce : 2 * (latitudeC (n := n)) / n ≤ (2 * (16 / 5) / n : ℝ) := by band_linarith
  apply le_of_pow_le_pow_left₀ (by norm_num <;> try band_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

end BstLean.Part285.Interval.PilotA
