import BstLean.Part291LatitudeSource
import BstLean.Part291AgentCentre
import BstLean.Part248Supply
import BstLean.Part252Centre
import BstLean.Part252NormalizedVariance
import BstLean.Part291ConditionalVariance
import BstLean.Part252MomentNum
import BstLean.Part242MixtureConstants
import BstLean.Part252PositiveOutput
import BstLean.Part159Win
import BstLean.Part252LowMass
import BstLean.Part263Frame
import BstLean.Part291ConditionalHigh
import BstLean.Part291ConditionalChi
import BstLean.Part242HQNorm
import BstLean.Part291DisplacementPointwise
import BstLean.Part242Chi

/- Component: Part291LatitudeFields.lean -/

/-! Latitude fields on their original measures. These are source fields for
node 39; the conditional mixture comparisons remain separate obligations. -/
namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part212

noncomputable def lowLocationMoment {n : ℕ} (D : Design n) (c : Ret n) (q : ℕ) : ℝ :=
  BstLean.Part195.rotationConstant q *
    √((3.042 / centreEnergy D c) / ((n : ℝ) * ((n : ℝ) - 1 - 2 * q)))

noncomputable def lowResidualMoment (n q : ℕ) : ℝ :=
  BstLean.Part195.rotationConstant q *
    √((2 * 3.042 / n) / ((n : ℝ) * ((n : ℝ) - 1 - 2 * q)))

theorem statedDesign2_agentCentre (n : ℕ) : AgentCentre154 (BstLean.Part289.statedDesign2 n) :=
  paperDesign_agentCentre passF passW measurable_passF measurable_passW

theorem agentLatitudeLocation {n : ℕ} (hn : LowBand n) (c : Ret n)
    (hb : 0 < normSq ((BstLean.Part289.statedDesign2 n).bA c.1 c.2.1.1))
    (hL : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((BstLean.Part289.statedDesign2 n).tau0 c))
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    (∫ a, ∫ v, |lA (BstLean.Part289.statedDesign2 n) c a v -
      lbar (BstLean.Part289.statedDesign2 n) c a| ^ (2 * q)
      ∂stdGauss (Fin (n - 1)) ∂muI n) ≤
        lowLocationMoment (BstLean.Part289.statedDesign2 n) c q ^ (2 * q) := by
  have hn8 := hn.1
  have he : 0 < normSq ((BstLean.Part289.statedDesign2 n).bA c.1 c.2.1.1) / n :=
    div_pos hb (by exact_mod_cast (show 0 < n by omega))
  exact fresh_LG_lambda (by omega) (BstLean.Part289.statedDesign2 n)
    (statedDesign2_agentCentre n) c (by norm_num : (0 : ℝ) < 3.042) he hL hq hq12

theorem agentLatitudeResidual {n : ℕ} (hn : LowBand n) (c : Ret n)
    (hL : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((BstLean.Part289.statedDesign2 n).tau0 c))
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    (∫ a, ∫ v, |sgA (BstLean.Part289.statedDesign2 n) c a v -
      gbar (BstLean.Part289.statedDesign2 n) c a| ^ (2 * q)
      ∂stdGauss (Fin (n - 1)) ∂muI n) ≤ lowResidualMoment n q ^ (2 * q) := by
  have hn8 := hn.1
  exact fresh_LG_residual (by omega) (BstLean.Part289.statedDesign2 n)
    (statedDesign2_agentCentre n) c (by norm_num : (0 : ℝ) < 3.042) hL hq hq12

theorem agentLatitudeResidualVariance {n : ℕ} (hn : LowBand n) (c : Ret n)
    (hL : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((BstLean.Part289.statedDesign2 n).tau0 c)) :
    √(∫ a, (∫ v, (sgA (BstLean.Part289.statedDesign2 n) c a v -
      gbar (BstLean.Part289.statedDesign2 n) c a) ^ 2
      ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n) ≤
        (2 * 3.042 / n) / ((n : ℝ) * ((n : ℝ) - 3)) := by
  have hn8 := hn.1
  exact fresh_LG_variance_residual (by omega) (BstLean.Part289.statedDesign2 n)
    (statedDesign2_agentCentre n) c (by norm_num : (0 : ℝ) < 3.042) hL

theorem outputCentreBand {n : ℕ} (hn : 8000 ≤ n) :
    (retDist (BstLean.Part289.statedDesign2 n).toCentres).real
      (BstLean.Part252.outputCentreEvent (BstLean.Part289.statedDesign2 n).toCentres)ᶜ ≤
        (0.000006145 : ℝ) :=
  (BstLean.Part252.outputCentreEvent_charge (by omega) _).trans
    (BstLean.Part252.exp_neg12_row.trans (by norm_num))

end BstLean.BlueprintLow

/- Component: Part291LatitudeNormalized.lean -/

namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part188 BstLean.Part242

noncomputable def lowLatitudeT (n q : ℕ) : ℝ :=
  BstLean.Part195.rotationConstant q * √(3.042 / ((n : ℝ) * ((n : ℝ) - 1 - 2 * q)))

noncomputable def lowLatitudeV (n : ℕ) : ℝ := 3.042 / ((n : ℝ) * ((n : ℝ) - 3))

theorem norm_of_iterated_moment {A V : Type*} [MeasurableSpace A] [MeasurableSpace V]
    (ρ : Measure A) (ν : Measure V) [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    {f : A × V → ℝ} (hf : Measurable f) {B K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ a v, |f (a, v)| ≤ B) {p : ℕ} (hp : p ≠ 0)
    (h : (∫ a, ∫ v, |f (a, v)| ^ p ∂ν ∂ρ) ≤ K ^ p) : LBound (ρ.prod ν) p f K := by
  have hi : Integrable (fun x => |f x| ^ p) (ρ.prod ν) :=
    intB (hf.abs.pow_const p) (M := B ^ p) (fun x => by
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb x.1 x.2) p)
  apply LBound.ofMoment hp
  refine ⟨hf, hK, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun _ => pow_nonneg (abs_nonneg _) _), integral_prod _ hi]
  exact ENNReal.ofReal_le_ofReal h

theorem lowLatitude_variances {n : ℕ} (hn : LowBand n) (c : Ret n) (he : 0 < eR c)
    (hL : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((paperDesignP n).tau0 c)) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (lowLatitudeV n) ∧
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (lowLatitudeV n) := by
  have hn8 := hn.1
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn.1
  have hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (3.042 / n)) := hL
  have hf := BstLean.Part252.fLatitude_variance_norm12 (by omega) c (by norm_num) he hk
  have hz := BstLean.Part252.zLatitude_variance_norm12 (by omega) c (by norm_num) hk
  have hcap : 3.042 / (n : ℝ) / ((n : ℝ) - 2) ≤ lowLatitudeV n := by
    unfold lowLatitudeV
    rw [div_mul_eq_div_div]
    apply div_le_div_of_nonneg_left (by positivity) (by linarith)
    linarith
  have hV0 : 0 ≤ lowLatitudeV n := by
    exact div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg n) (by linarith))
  exact ⟨⟨hf.measurable, hV0,
    hf.bound.trans (ENNReal.ofReal_le_ofReal hcap)⟩,
    ⟨hz.measurable, hV0,
    hz.bound.trans (ENNReal.ofReal_le_ofReal hcap)⟩⟩

theorem lowLatitude_residual_norm {n : ℕ} (hn : LowBand n) (c : Ret n)
    (hL : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((paperDesignP n).tau0 c))
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    LBound ((muI n).prod (stdGauss (Fin (n - 1)))) ((2 * q : ℕ) : ℝ≥0∞)
      (fun x => zLatitude c x - latitudeMean (stdGauss (Fin (n - 1))) (zLatitude c) x.1)
      (lowLatitudeT n q) := by
  have hn8 := hn.1
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn.1
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq12
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have hden : 0 < (n : ℝ) * ((n : ℝ) - 1 - 2 * q) := mul_pos (by linarith) (by linarith)
  let D := paperDesignP n
  have hraw := BstLean.Part212.fresh_LG_residual (by omega : 26 ≤ n) D
    (paperDesign_agentCentre passF passW measurable_passF measurable_passW) c (by norm_num : (0 : ℝ) < 3.042) hL hq hq12
  have hbm a : |gbar D c a| ≤ lipSig D c := by
    simpa only [gbar, Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := stdGauss (Fin (n - 1)))
        (f := sgA D c a) (C := lipSig D c)
        (ae_of_all _ fun v => by simpa only [Real.norm_eq_abs] using abs_sgA_le (by omega) D c a v)
  have hbd a v : |sgA D c a v - gbar D c a| ≤ 2 * lipSig D c :=
    (abs_sub _ _).trans (by linarith [abs_sgA_le (by omega) D c a v, hbm a])
  have hh := norm_of_iterated_moment (muI n) (stdGauss (Fin (n - 1)))
    ((measurable_sgA D c).sub ((measurable_gbar D c).comp measurable_fst))
    (mul_nonneg (BstLean.Part195.rotationConstant_nonneg q) (sqrt_nonneg _)) hbd
    (by omega : 2 * q ≠ 0) hraw
  have hs := hh.scale (by omega : 2 * q ≠ 0) (inv_nonneg.mpr (sqrt_nonneg (2 / (n : ℝ))))
  have heq : (fun x : Ix n × (Fin (n - 1) → ℝ) => (√(2 / (n : ℝ)))⁻¹ *
      (sgA D c x.1 x.2 - gbar D c x.1)) =
      fun x => zLatitude c x - latitudeMean (stdGauss (Fin (n - 1))) (zLatitude c) x.1 := by
    funext x
    unfold zLatitude latitudeMean gbar
    rw [integral_div]
    ring
  have hscalar : (√(2 / (n : ℝ)))⁻¹ *
      (BstLean.Part195.rotationConstant q *
        √((2 * 3.042 / n) / ((n : ℝ) * ((n : ℝ) - 1 - 2 * q)))) = lowLatitudeT n q := by
    have he : (2 * 3.042 / (n : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1 - 2 * q)) =
        (2 / (n : ℝ)) * (3.042 / ((n : ℝ) * ((n : ℝ) - 1 - 2 * q))) := by ring
    rw [he, sqrt_mul hγ.le]
    unfold lowLatitudeT
    field_simp
  simp only [Pi.sub_apply, Function.comp_apply] at hs
  rwa [heq, hscalar] at hs

end BstLean.BlueprintLow

/- Component: Part291MixtureParameters.lean -/

namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part188 BstLean.Part248

noncomputable def lowMixtureWidth (n : ℕ) : ℝ := 3.5 * lowLatitudeT n 12
noncomputable def lowMixtureMean (n : ℕ) : ℝ :=
  √agentEnergyCap + √(agentParallelCap / n)
noncomputable def lowMixtureY (n : ℕ) : ℝ := 1 - lowMixtureMean n ^ 2
noncomputable def lowMixtureX (n q : ℕ) : ℝ :=
  deficitConstant q (agentEnergyMomentCap / n) (lowMixtureMean n) (√(agentDirectionCap / n))
noncomputable def lowMixtureXhat (n q : ℕ) : ℝ :=
  mixtureConstant (lowMixtureX n q) (agentEnergyMomentCap / n)
    (lowLatitudeT n q) 0.0045 (lowLatitudeV n)
noncomputable def lowMixtureReciprocal (n : ℕ) : ℝ :=
  bound3 0.18 (lowMixtureY n) (lowMixtureXhat n 4) (lowMixtureXhat n 8) (lowMixtureXhat n 12)

theorem lowMixtureMean_bound {n : ℕ} (hn : 8000 ≤ n) :
    0 ≤ lowMixtureMean n ∧ lowMixtureMean n ≤ 0.844 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : √agentEnergyCap ≤ 0.84129 := sqrt_le_iff.mpr (by norm_num [agentEnergyCap])
  have h2 : √(agentParallelCap / n) ≤ 0.002595 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ agentParallelCap / 8000 := by unfold agentParallelCap; gcongr
      _ ≤ (0.002595 : ℝ) ^ 2 := by norm_num [agentParallelCap]
  unfold lowMixtureMean
  exact ⟨by positivity, by linarith⟩

theorem lowMixtureY_lower {n : ℕ} (hn : 8000 ≤ n) : (0.287 : ℝ) ≤ lowMixtureY n := by
  obtain ⟨hl, hu⟩ := lowMixtureMean_bound hn
  unfold lowMixtureY
  nlinarith

theorem lowLatitudeTwelve_bound {n : ℕ} (hn : 8000 ≤ n) :
    0 < lowLatitudeT n 12 ∧ lowLatitudeT n 12 ≤ 0.001049 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1 - 2 * 12) :=
    mul_pos (by linarith) (by linarith)
  have hp := BstLean.Part252.rotation_positive 12
  have hu := BstLean.Part252.rotation_twelve
  have hs : √(3.042 / ((n : ℝ) * ((n : ℝ) - 1 - 2 * 12))) ≤ 0.0002185 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.042 : ℝ) / (8000 * 7975) := by gcongr <;> linarith
      _ ≤ (0.0002185 : ℝ) ^ 2 := by norm_num
  unfold lowLatitudeT
  refine ⟨mul_pos hp (sqrt_pos.mpr (div_pos (by norm_num) hden)), ?_⟩
  exact (mul_le_mul hu hs (sqrt_nonneg _) (by norm_num)).trans (by norm_num)

theorem lowMixtureWidth_bound {n : ℕ} (hn : 8000 ≤ n) :
    0 < lowMixtureWidth n ∧ lowMixtureWidth n ≤ 0.0036715 := by
  obtain ⟨hl, hu⟩ := lowLatitudeTwelve_bound hn
  unfold lowMixtureWidth
  exact ⟨mul_pos (by norm_num) hl, by linarith⟩

theorem lowMixtureEpsilon_bound {n : ℕ} (hn : 8000 ≤ n) :
    0 ≤ eps0 (lowMixtureWidth n) (√(0.18 : ℝ)) ∧
      eps0 (lowMixtureWidth n) (√(0.18 : ℝ)) ≤ 0.035 := by
  obtain ⟨hw, hu⟩ := lowMixtureWidth_bound hn
  have hs : (0.42426 : ℝ) ≤ √(0.18 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hq : 2 * lowMixtureWidth n / √(0.18 : ℝ) ≤ 0.01731 := by
    calc
      _ ≤ 2 * (0.0036715 : ℝ) / 0.42426 := by gcongr
      _ ≤ (0.01731 : ℝ) := by norm_num
  have hq0 : 0 ≤ 2 * lowMixtureWidth n / √(0.18 : ℝ) := by positivity
  unfold eps0
  constructor <;> nlinarith

noncomputable def lowPaperSplit {n : ℕ} (D : Design n) (c : Ret n) : SplitData n :=
  dPaper D c (lowMixtureWidth n / √(centreEnergy D c))
    (√(2 / (n : ℝ)) * lowMixtureWidth n) (√((2 / (n : ℝ)) * 0.18))
    0.0045 (by norm_num) (by norm_num)

theorem lowMixtureFloor {n : ℕ} (hn : LowBand n) :
    BstLean.Part289.scaleFloor n ≤ (1 - (0.0045 : ℝ)) * 0.18 := by
  rw [BstLean.Part289.scaleFloor_low (by have := hn.2; omega)]
  norm_num

theorem lowPaperSplit_epsilon {n : ℕ} (hn : 8000 ≤ n) :
    eps0 (√(2 / (n : ℝ)) * lowMixtureWidth n) (√((2 / (n : ℝ)) * 0.18)) =
      eps0 (lowMixtureWidth n) (√(0.18 : ℝ)) := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hγ : (0 : ℝ) < 2 / n := by positivity
  unfold eps0
  rw [sqrt_mul hγ.le]
  congr 2
  field_simp

end BstLean.BlueprintLow

/- Component: Part291MixtureReciprocal.lean -/

/-! D1 and the order-three reciprocal on the actual retained latitude law. -/
namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part188 BstLean.Part242 BstLean.Part248

theorem lowPaperSplit_cut {n : ℕ} (hn : 8000 ≤ n) (c : Ret n)
    {a : Ix n} {v : Fin (n - 1) → ℝ}
    (hv : v ∈ slice (lowPaperSplit (paperDesignP n) c) a) :
    √(0.18 : ℝ) ≤ zLatitude c (a, v) := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have hh : √((2 / (n : ℝ)) * 0.18) ≤ sgA (paperDesignP n) c a v := hv.2.2
  rw [sqrt_mul hγ.le] at hh
  unfold zLatitude
  exact (le_div_iff₀ (sqrt_pos.mpr hγ)).mpr (by simpa only [mul_comm] using hh)

theorem agentDeficitBand {n : ℕ} (hn : LowBand n) (c : Ret n) (hc : c.1.2 ≠ 0)
    (hτ : 0 < (paperDesignP n).tau0 c) (hb : 0 < normSq (bR c))
    (hI : WFInterfaces (paperDesignP n) c agentDirectionCap (agentEnergyMomentCap / n) agentParallelCap)
    (hE : centreEnergy (paperDesignP n) c ≤ agentEnergyCap) :
    DeficitOrders (muI n) (fun a => (dP c).Sb a / (2 / (n : ℝ)))
      (lowMixtureY n) (lowMixtureX n 4) (lowMixtureX n 8) (lowMixtureX n 12) := by
  have hn8 := hn.1
  exact D1_from_WF (by omega) c hc hτ hb hI hE

theorem agentMixtureReciprocalBand {n : ℕ} (hn : LowBand n) (c : Ret n)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP n).tau0 c) (hb : 0 < normSq (bR c))
    (hI : WFInterfaces (paperDesignP n) c agentDirectionCap (agentEnergyMomentCap / n) agentParallelCap)
    (hE : centreEnergy (paperDesignP n) c ≤ agentEnergyCap)
    (hL : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((paperDesignP n).tau0 c)) :
    LBound ((muI n).restrict (keptIx (paperDesignP n) c (lowPaperSplit (paperDesignP n) c))) 4
      (fun a => 1 / goodMeanSq (stdGauss (Fin (n - 1)))
        (slice (lowPaperSplit (paperDesignP n) c) a) (fun v => zLatitude c (a, v)))
      (lowMixtureReciprocal n) := by
  have hn8 := hn.1
  have he : 0 < eR c := div_pos hb (by exact_mod_cast (show 0 < n by omega))
  have hY : 0 < 1 - lowMixtureMean n ^ 2 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 0.287) (lowMixtureY_lower hn.1)
  have hd := agentDeficitBand hn c hc hτ hb hI hE
  have he32 := energy_latitude (by omega) c hc hτ hI.energy
  have ht8 := lowLatitude_residual_norm hn c hL (q := 4) (by omega) (by omega)
  have ht16 := lowLatitude_residual_norm hn c hL (q := 8) (by omega) (by omega)
  have ht24 := lowLatitude_residual_norm hn c hL (q := 12) (by omega) (by omega)
  have hv := (lowLatitude_variances hn c he hL).2
  have h := R_mixture_network (by omega) c hb.ne' (lowPaperSplit (paperDesignP n) c)
    (by norm_num : (0 : ℝ) < 0.18) hY (fun _ _ _ hv => lowPaperSplit_cut hn.1 c hv)
    hd he32 ht8 ht16 ht24 hv
  have hcap : bestBound 0.18 (lowMixtureY n) (lowMixtureXhat n 4)
      (lowMixtureXhat n 8) (lowMixtureXhat n 12) ≤ lowMixtureReciprocal n :=
    (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨h.measurable, h.nonneg.trans hcap, h.bound.trans (ENNReal.ofReal_le_ofReal hcap)⟩

end BstLean.BlueprintLow

/- Component: Part291ConditionalNormalized.lean -/

namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part188 BstLean.Part242

theorem goodMeanSq_scale {V : Type*} [MeasurableSpace V]
    (ν : Measure V) (G : Set V) (f : V → ℝ) (s : ℝ) :
    goodMeanSq ν G (fun v => s * f v) = s ^ 2 * goodMeanSq ν G f := by
  unfold goodMeanSq
  rw [integral_const_mul, mul_pow]

theorem normalized_conditional_second {n : ℕ} (hn : 8000 ≤ n) (c : Ret n)
    (he : 0 < eR c) {χ : ℝ} (hCA : normSq c.2.1.2 ≤ 2 * eR c * χ)
    {a : Ix n} (ha : a ∈ keptIx (paperDesignP n) c (lowPaperSplit (paperDesignP n) c)) :
    let split := lowPaperSplit (paperDesignP n) c
    let ν := stdGauss (Fin (n - 1))
    let Z := goodMeanSq ν (slice split a) (fun v => zLatitude c (a, v))
    condMom split (epsF (paperDesignP n) c split) 2 a ≤
      (4 * (1 + lowMixtureWidth n / √(0.18 : ℝ)) ^ 2 / (1 - 0.0045)) *
        (conditionalVariance ν (fun v => zLatitude c (a, v)) / Z) ∧
    condMom split (delF (paperDesignP n) c split) 2 a ≤
      ((n : ℝ) * χ / (1 - 0.0045)) *
        (conditionalVariance ν (fun v => fLatitude c (a, v)) / Z) := by
  dsimp only
  let D := paperDesignP n
  let split := lowPaperSplit D c
  let ν := stdGauss (Fin (n - 1))
  let γ := 2 / (n : ℝ)
  let Z := goodMeanSq ν (slice split a) (fun v => zLatitude c (a, v))
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hs : sgA D c a = fun v => √γ * zLatitude c (a, v) := by
    funext v
    unfold zLatitude
    change _ = √γ * (_ / √γ)
    field_simp
    rfl
  have hf : (fun v => fLatitude c (a, v)) = fun v => √(eR c) * lA D c a v := by
    funext v
    exact fX_eq_lam c _
  have hZ : goodMeanSq ν (slice split a) (sgA D c a) = γ * Z := by
    rw [hs, goodMeanSq_scale, sq_sqrt hγ.le]
  have hV : conditionalVariance ν (sgA D c a) =
      γ * conditionalVariance ν (fun v => zLatitude c (a, v)) := by
    rw [hs, BstLean.Part252.conditionalVariance_scale, sq_sqrt hγ.le]
  have hF : conditionalVariance ν (fun v => fLatitude c (a, v)) =
      eR c * conditionalVariance ν (lA D c a) := by
    rw [hf, BstLean.Part252.conditionalVariance_scale, sq_sqrt he.le]
  have hratio : (√γ * lowMixtureWidth n) / √(γ * 0.18) =
      lowMixtureWidth n / √(0.18 : ℝ) := by
    rw [sqrt_mul hγ.le]
    exact mul_div_mul_left _ _ (sqrt_pos.mpr hγ).ne'
  have hw := (lowMixtureWidth_bound hn).1
  have h := paper_conditional_variances (by omega) D c
    (by change 0 ≤ √γ * lowMixtureWidth n; positivity)
    (by change 0 < √(γ * 0.18); positivity)
    (by norm_num : (0 : ℝ) < 0.0045) (by norm_num) ha
  change condMom split (epsF D c split) 2 a ≤ _ ∧ condMom split (delF D c split) 2 a ≤ _ at h
  change _ ≤ (4 * (1 + (√γ * lowMixtureWidth n) / √(γ * 0.18)) ^ 2 / (1 - 0.0045)) *
      (conditionalVariance ν (sgA D c a) / goodMeanSq ν (slice split a) (sgA D c a)) ∧ _ at h
  rw [hZ, hV, hratio, mul_div_mul_left _ _ hγ.ne'] at h
  refine ⟨h.1, ?_⟩
  rw [hF]
  have hdel := h.2
  change condMom split (delF D c split) 2 a ≤
    normSq c.2.1.2 / (1 - 0.0045) *
      (conditionalVariance ν (lA D c a) / goodMeanSq ν (slice split a) (sgA D c a)) at hdel
  rw [hZ] at hdel
  refine hdel.trans ?_
  have hV0 : 0 ≤ conditionalVariance ν (lA D c a) := integral_nonneg fun _ => sq_nonneg _
  have hZ0 : 0 ≤ Z := sq_nonneg _
  calc
    _ ≤ (2 * eR c * χ / (1 - 0.0045)) * (conditionalVariance ν (lA D c a) / (γ * Z)) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hCA (by norm_num))
        (div_nonneg hV0 (mul_nonneg hγ.le hZ0))
    _ = ((n : ℝ) * χ / (1 - 0.0045)) * (eR c * conditionalVariance ν (lA D c a) / Z) := by
      dsimp [γ]
      field_simp
      <;> ring

end BstLean.BlueprintLow

/- Component: Part291ConditionalNorms.lean -/

/-! The SY2 constants bound the actual conditional moments at both outer
orders. No normalization is applied to the kept latitude measure. -/
namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part188 BstLean.Part242

noncomputable def lowMixtureA (n : ℕ) : ℝ :=
  mixA (lowMixtureWidth n) 0.18 (lowMixtureReciprocal n) (lowLatitudeV n) 0.0045

noncomputable def lowMixtureD (n : ℕ) (χ : ℝ) : ℝ :=
  mixD n χ (lowMixtureReciprocal n) (lowLatitudeV n) 0.0045

theorem agentConditionalNormsBand {n : ℕ} (hn : LowBand n) (c : Ret n)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP n).tau0 c) (hb : 0 < normSq (bR c))
    (hI : WFInterfaces (paperDesignP n) c agentDirectionCap (agentEnergyMomentCap / n) agentParallelCap)
    (hE : centreEnergy (paperDesignP n) c ≤ agentEnergyCap)
    (hL : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((paperDesignP n).tau0 c))
    {χ : ℝ} (hχ : 0 ≤ χ) (hCA : normSq c.2.1.2 ≤ 2 * eR c * χ) :
    let split := lowPaperSplit (paperDesignP n) c
    let ρ := (muI n).restrict (keptIx (paperDesignP n) c split)
    LBound ρ 2 (condMom split (epsF (paperDesignP n) c split) 2) (lowMixtureA n) ∧
    LBound ρ 3 (condMom split (epsF (paperDesignP n) c split) 2) (lowMixtureA n) ∧
    LBound ρ 2 (condMom split (delF (paperDesignP n) c split) 2) (lowMixtureD n χ) ∧
    LBound ρ 3 (condMom split (delF (paperDesignP n) c split) 2) (lowMixtureD n χ) := by
  let split := lowPaperSplit (paperDesignP n) c
  let K := keptIx (paperDesignP n) c split
  let ρ := (muI n).restrict K
  let ν := stdGauss (Fin (n - 1))
  have hn8 := hn.1
  have he : 0 < eR c := div_pos hb (by exact_mod_cast (show 0 < n by omega))
  have mK : MeasurableSet K := measurableSet_keptSet _ split.mgood (measurableSet_bulkIx _ c) _
  have hmass : ρ univ ≤ 1 := (Measure.restrict_le_self univ).trans (by simp)
  have hR := agentMixtureReciprocalBand hn c hc hτ hb hI hE hL
  obtain ⟨hf, hz⟩ := lowLatitude_variances hn c he hL
  have hf12 := hf.restrict K
  have hz12 := hz.restrict K
  have hf4 := hf12.lower (by norm_num) (by norm_num) (by norm_num : (4 : ℝ≥0∞) ≤ 12) hmass
  have hz4 := hz12.lower (by norm_num) (by norm_num) (by norm_num : (4 : ℝ≥0∞) ≤ 12) hmass
  obtain ⟨hA2, hA3⟩ := SY2_variance_constants (dw := lowMixtureWidth n) (d := 0.18)
    (by norm_num : (0.0045 : ℝ) < 1) hz4 hz12 hR
  obtain ⟨hD2, hD3⟩ := SY2_location_constants n hχ (by norm_num : (0.0045 : ℝ) < 1) hf4 hf12 hR
  have mE := measurable_condMom split (measurable_epsF (paperDesignP n) c split) 2
  have mD := measurable_condMom split (measurable_delF (paperDesignP n) c split) 2
  have hAE : ∀ᵐ a ∂ρ, |condMom split (epsF (paperDesignP n) c split) 2 a| ≤
      |(4 * (1 + lowMixtureWidth n / √(0.18 : ℝ)) ^ 2 / (1 - 0.0045)) *
        (conditionalVariance ν (fun v => zLatitude c (a, v)) *
          (1 / goodMeanSq ν (slice split a) (fun v => zLatitude c (a, v))))| := by
    apply (ae_restrict_iff' mK).mpr
    exact ae_of_all _ fun a ha => by
      rw [abs_of_nonneg (condMom_nonneg split _ 2 a)]
      have h := (normalized_conditional_second hn.1 c he hCA ha).1
      exact h.trans ((le_of_eq (by ring)).trans (le_abs_self _))
  have hAD : ∀ᵐ a ∂ρ, |condMom split (delF (paperDesignP n) c split) 2 a| ≤
      |((n : ℝ) * χ / (1 - 0.0045)) *
        (conditionalVariance ν (fun v => fLatitude c (a, v)) *
          (1 / goodMeanSq ν (slice split a) (fun v => zLatitude c (a, v))))| := by
    apply (ae_restrict_iff' mK).mpr
    exact ae_of_all _ fun a ha => by
      rw [abs_of_nonneg (condMom_nonneg split _ 2 a)]
      have h := (normalized_conditional_second hn.1 c he hCA ha).2
      exact h.trans ((le_of_eq (by ring)).trans (le_abs_self _))
  exact ⟨hA2.mono mE hAE, hA3.mono mE hAE, hD2.mono mD hAD, hD3.mono mD hAD⟩

end BstLean.BlueprintLow

/- Component: Part291AuxiliaryEvents.lean -/

namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part156 BstLean.Part157 BstLean.Part159 BstLean.Part169

noncomputable def lowMixtureChi (n : ℕ) : ℝ := 1 + 2 * √(12 / (n : ℝ)) + 24 / n

theorem lowMixtureChi_pos (n : ℕ) : 0 < lowMixtureChi n := by
  unfold lowMixtureChi
  positivity

theorem lowMixtureChi_eq {n : ℕ} (hn : 0 < n) :
    BstLean.Part164.chiUp n / n = lowMixtureChi n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : √((n : ℝ) * 12) / n = √(12 / (n : ℝ)) := by
    have hsq : (√((n : ℝ) * 12) / n) ^ 2 = 12 / (n : ℝ) := by
      rw [div_pow, sq_sqrt (by positivity)]
      field_simp
    rw [← hsq, sqrt_sq (by positivity)]
  unfold BstLean.Part164.chiUp lowMixtureChi
  rw [add_div, add_div, div_self hnR.ne']
  rw [show 2 * √((n : ℝ) * 12) / n = 2 * (√((n : ℝ) * 12) / n) by ring, he]
  norm_num

theorem outputCentre_normalized {n : ℕ} (hn : 0 < n) {c : Ret n}
    (hc : c ∈ BstLean.Part252.outputCentreEvent (paperDesignP n).toCentres) :
    normSq c.2.1.2 ≤ 2 * eR c * lowMixtureChi n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  change normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (bR c) * BstLean.Part164.chiUp n at hc
  refine hc.trans_eq ?_
  rw [← lowMixtureChi_eq hn]
  unfold eR mA
  push_cast
  ring

def lowAnglesEvent (n : ℕ) : Set (Ret n) :=
  Ethm (BstLean.Part289.statedDesign2 n).toCentres ∩ Ethp (BstLean.Part289.statedDesign2 n).toCentres

theorem lowAnglesEvent_measurable (n : ℕ) : MeasurableSet (lowAnglesEvent n) :=
  (measurableSet_Ethm _).inter (measurableSet_Ethp _)

theorem lowAnglesEvent_charge {n : ℕ} (hn : 8000 ≤ n) :
    (retDist (BstLean.Part289.statedDesign2 n).toCentres).real (lowAnglesEvent n)ᶜ ≤
      (0.0000062 : ℝ) := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := ethm_charge (BstLean.Part289.statedDesign2 n).toCentres
  have h2 := ethp_charge (by omega) (BstLean.Part289.statedDesign2 n).toCentres
  have he : exp (-(45 / 10000 * (n : ℝ))) ≤ exp (-12) ^ 2 := by
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    norm_num
    linarith
  have hu := BstLean.Part252.exp_neg12_row
  have hq := pow_le_pow_left₀ (exp_pos (-12 : ℝ)).le hu 2
  unfold lowAnglesEvent
  rw [compl_inter]
  exact ((measureReal_union_le _ _).trans
    (add_le_add (h1.trans (he.trans hq)) (h2.trans hu))).trans (by norm_num)

end BstLean.BlueprintLow

/- Component: Part291Removal.lean -/

namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part188 BstLean.Part222

noncomputable def lowMixtureBeta (n : ℕ) : ℝ :=
  massBound n agentDirectionCap (agentEnergyMomentCap / n) agentParallelCap agentEnergyCap 0.0066 0.18 / n

noncomputable def lowMixtureB (n : ℕ) : ℝ := 2 * (1 / (3.5 : ℝ)) ^ 24 + lowMixtureBeta n

theorem lowMixtureBeta_nonneg (n : ℕ) : 0 ≤ lowMixtureBeta n := by
  unfold lowMixtureBeta massBound
  positivity

theorem lowMixtureB_nonneg (n : ℕ) : 0 ≤ lowMixtureB n := by
  unfold lowMixtureB
  have := lowMixtureBeta_nonneg n
  positivity

theorem lowLocationMoment_eq {n q : ℕ} (D : Design n) (c : Ret n) :
    lowLocationMoment D c q = lowLatitudeT n q / √(centreEnergy D c) := by
  unfold lowLocationMoment lowLatitudeT
  have hE : 0 ≤ centreEnergy D c := by
    exact div_nonneg (normSq_nonneg _) (Nat.cast_nonneg n)
  rw [show (3.042 / centreEnergy D c) / ((n : ℝ) * ((n : ℝ) - 1 - 2 * q)) =
    (3.042 / ((n : ℝ) * ((n : ℝ) - 1 - 2 * q))) / centreEnergy D c by ring,
    sqrt_div' _ hE]
  ring

theorem lowResidualMoment_eq {n q : ℕ} :
    lowResidualMoment n q = √(2 / (n : ℝ)) * lowLatitudeT n q := by
  unfold lowResidualMoment lowLatitudeT
  rw [show (2 * 3.042 / (n : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1 - 2 * q)) =
    (2 / (n : ℝ)) * (3.042 / ((n : ℝ) * ((n : ℝ) - 1 - 2 * q))) by ring,
    sqrt_mul (by positivity : (0 : ℝ) ≤ 2 / n)]
  ring

theorem agentLowMassBand {n : ℕ} (hn : LowBand n) (c : Ret n)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP n).tau0 c) (hb : 0 < normSq (bR c))
    (hI : WFInterfaces (paperDesignP n) c agentDirectionCap (agentEnergyMomentCap / n) agentParallelCap)
    (hE : centreEnergy (paperDesignP n) c ≤ agentEnergyCap) :
    (∫ a, (stdGauss (Fin (n - 1))).real
      {v | sgA (paperDesignP n) c a v < √((2 / (n : ℝ)) * 0.18)} ∂muI n) ≤ lowMixtureBeta n := by
  have hn8 := hn.1
  have hm := (lowMixtureMean_bound hn.1).2
  have hs : (0.898 : ℝ) ≤ √((1 - (0.0066 : ℝ)) ^ 2 - 0.18) :=
    le_sqrt_of_sq_le (by norm_num)
  have hmass := sharp_residual_mass (by omega) (paperDesignP n) c hτ hb
    (BstLean.Part263.paper_centre_nonneg c) hI hE
    (by norm_num : (0 : ℝ) < 0.0066) (by norm_num) (by norm_num : (0.18 : ℝ) < (1 - 0.0066) ^ 2)
    (by change 0 < √((1 - (0.0066 : ℝ)) ^ 2 - 0.18) - lowMixtureMean n; linarith)
  exact BstLean.Part252.latitude_mass_of_MASS (by omega) (paperDesignP n) c hc hτ (by norm_num) hmass

theorem agentRemovalBand {n : ℕ} (hn : LowBand n) (c : Ret n)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP n).tau0 c) (hb : 0 < normSq (bR c))
    (hI : WFInterfaces (paperDesignP n) c agentDirectionCap (agentEnergyMomentCap / n) agentParallelCap)
    (hE : centreEnergy (paperDesignP n) c ≤ agentEnergyCap)
    (hL : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((paperDesignP n).tau0 c)) :
    (∫ a, removed (stdGauss (Fin (n - 1))) (lowPaperSplit (paperDesignP n) c).good a ∂muI n) ≤
      lowMixtureB n := by
  have hn8 := hn.1
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn.1
  have he : 0 < centreEnergy (paperDesignP n) c := div_pos hb (by positivity)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have ht := (lowLatitudeTwelve_bound hn.1).1
  have hw := (lowMixtureWidth_bound hn.1).1
  have hl := agentLatitudeLocation hn c hb hL (q := 12) (by norm_num) (by norm_num)
  have hs := agentLatitudeResidual hn c hL (q := 12) (by norm_num) (by norm_num)
  have hmass := agentLowMassBand hn c hc hτ hb hI hE
  have hcentre : centreEnergy (Part289.statedDesign2 n) c = centreEnergy (paperDesignP n) c := rfl
  have h := int_removed (by omega) (paperDesignP n) c
    (show 0 < lowMixtureWidth n / √(centreEnergy (paperDesignP n) c) by positivity)
    (show 0 < √(2 / (n : ℝ)) * lowMixtureWidth n by positivity) 24 hl hs hmass
  refine h.trans_eq ?_
  unfold Bpap lowMixtureB
  rw [lowLocationMoment_eq, hcentre, lowResidualMoment_eq]
  unfold lowMixtureWidth
  field_simp
  <;> ring

end BstLean.BlueprintLow

/- Component: Part291MixtureScalars.lean -/

namespace BstLean.BlueprintLow
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part162 BstLean.Part169
open BstLean.Part242 BstLean.Part248

noncomputable def lowMixtureEpsilon (n : ℕ) : ℝ := eps0 (lowMixtureWidth n) (√(0.18 : ℝ))
noncomputable def lowMixtureL (n : ℕ) : ℝ := n * lowMixtureChi n * (2 * lowMixtureWidth n) ^ 2 / 0.18
noncomputable def lowMixtureI (n j : ℕ) : ℝ :=
  iotaP 0.0045 (2 * j) + √(0.0045 : ℝ) / (1 - 0.0045) + lowMixtureWidth n / √(0.18 * (1 - 0.0045))
noncomputable def lowMixtureE (n j : ℕ) : ℝ :=
  (2 + 2 * lowMixtureWidth n / √(0.18 : ℝ)) * lowMixtureI n j * lowLatitudeT n j / √(0.18 : ℝ)
noncomputable def lowMixtureLocation (n j : ℕ) : ℝ :=
  √((n : ℝ) * lowMixtureChi n / 0.18) * lowMixtureI n j * lowLatitudeT n j
noncomputable def lowMixtureK (n : ℕ) : ℝ := (1 - lowMixtureEpsilon n ^ 2)⁻¹
noncomputable def lowMixtureT2 (n : ℕ) : ℝ :=
  lowMixtureK n * ((n : ℝ) * lowMixtureA n / 2 + lowMixtureD n (lowMixtureChi n) +
    √(lowMixtureL n * lowMixtureA n * lowMixtureD n (lowMixtureChi n)))
noncomputable def lowMixtureT (n j : ℕ) : ℝ :=
  tK (lowMixtureK n) n (√(lowMixtureL n)) (lowMixtureE n j) (lowMixtureLocation n j)
noncomputable def lowMixtureQ (n : ℕ) : ℝ :=
  lowMixtureK n * ((n : ℝ) * lowMixtureA n ^ 2 / 4 +
    (1 + lowMixtureEpsilon n) * lowMixtureA n * lowMixtureD n (lowMixtureChi n)) +
    lowMixtureT2 n ^ 2 / 2 + lowMixtureT2 n * lowMixtureT n 4 ^ 2 / 6 +
    lowMixtureT n 4 ^ 4 / 24 + lowMixtureT n 6 ^ 5 / 120 +
    exp (lowMixtureK n * ((n : ℝ) * lowMixtureEpsilon n ^ 2 / 2 +
      lowMixtureL n * (1 + lowMixtureEpsilon n))) * lowMixtureT n 6 ^ 6 / 720
noncomputable def lowMixtureHQ (n : ℕ) : ℝ :=
  mixL3 n (lowMixtureEpsilon n) (lowMixtureA n) (lowMixtureD n (lowMixtureChi n))

theorem lowLatitudeT_pos {n q : ℕ} (hn : 8000 ≤ n) (hq : q ≤ 12) : 0 < lowLatitudeT n q := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  unfold lowLatitudeT
  exact mul_pos (BstLean.Part252.rotation_positive q)
    (sqrt_pos.mpr (div_pos (by norm_num) (mul_pos (by linarith) (by linarith))))

theorem lowLatitudeV_pos {n : ℕ} (hn : 8000 ≤ n) : 0 < lowLatitudeV n := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  unfold lowLatitudeV
  exact div_pos (by norm_num) (mul_pos (by linarith) (by linarith))

theorem lowMixtureReciprocal_pos {n : ℕ} (hn : 8000 ≤ n) : 0 < lowMixtureReciprocal n := by
  have hY : 0 < lowMixtureY n := lt_of_lt_of_le (by norm_num) (lowMixtureY_lower hn)
  have hV := lowLatitudeV_pos hn
  have hm := (lowMixtureMean_bound hn).1
  have hT q : 0 ≤ lowLatitudeT n q := by
    unfold lowLatitudeT
    exact mul_nonneg (BstLean.Part195.rotationConstant_nonneg q) (sqrt_nonneg _)
  have hX q : 0 ≤ lowMixtureX n q := by
    unfold lowMixtureX deficitConstant
    have := BstLean.Part195.rotationConstant_nonneg (q / 2)
    unfold agentEnergyMomentCap agentDirectionCap
    positivity
  have hXh q : 0 ≤ lowMixtureXhat n q := by
    unfold lowMixtureXhat mixtureConstant
    have := hX q
    have := hT q
    unfold agentEnergyMomentCap
    positivity
  unfold lowMixtureReciprocal bound3
  have := hXh 4
  have := hXh 8
  have := hXh 12
  positivity

theorem lowMixtureA_pos {n : ℕ} (hn : 8000 ≤ n) : 0 < lowMixtureA n := by
  have := lowMixtureReciprocal_pos hn
  have := lowLatitudeV_pos hn
  have := (lowMixtureWidth_bound hn).1
  unfold lowMixtureA mixA
  positivity

theorem lowMixtureD_pos {n : ℕ} (hn : 8000 ≤ n) : 0 < lowMixtureD n (lowMixtureChi n) := by
  have := lowMixtureReciprocal_pos hn
  have := lowLatitudeV_pos hn
  have := lowMixtureChi_pos n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold lowMixtureD mixD
  positivity

theorem lowMixtureL_nonneg (n : ℕ) : 0 ≤ lowMixtureL n := by
  have := lowMixtureChi_pos n
  unfold lowMixtureL
  positivity

end BstLean.BlueprintLow

/- Component: Part291HighScalars.lean -/

namespace BstLean.BlueprintLow
open Real Set
open BstLean.Part162

theorem lowMixtureI_pos {n j : ℕ} (hn : 8000 ≤ n) : 0 < lowMixtureI n j := by
  have := (lowMixtureWidth_bound hn).1
  have := iotaP_pos (by norm_num : (0.0045 : ℝ) < 1) (2 * j)
  unfold lowMixtureI
  positivity

theorem lowMixtureI_majorizes {n j : ℕ} (hn : 8000 ≤ n) :
    iotaP 0.0045 (2 * j) + c2η 0.0045 +
      c3η 0.0045 (√(2 / (n : ℝ)) * lowMixtureWidth n) (√((2 / (n : ℝ)) * 0.18)) ≤
        lowMixtureI n j := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have hw := (lowMixtureWidth_bound hn).1
  have hη : (1 - (0.0045 : ℝ)) ≤ √(1 - (0.0045 : ℝ)) := le_sqrt_of_sq_le (by norm_num)
  have h2 : c2η 0.0045 ≤ √(0.0045 : ℝ) / (1 - 0.0045) := by
    unfold c2η
    rw [sqrt_div (by norm_num : (0 : ℝ) ≤ 0.0045)]
    exact div_le_div_of_nonneg_left (sqrt_nonneg _) (by norm_num) hη
  have h3 : c3η 0.0045 (√(2 / (n : ℝ)) * lowMixtureWidth n) (√((2 / (n : ℝ)) * 0.18)) =
      lowMixtureWidth n / (2 * √(0.18 * (1 - 0.0045))) := by
    unfold c3η
    rw [sqrt_mul hγ.le, sqrt_mul (by norm_num : (0 : ℝ) ≤ 0.18)]
    field_simp
  have h3' : c3η 0.0045 (√(2 / (n : ℝ)) * lowMixtureWidth n) (√((2 / (n : ℝ)) * 0.18)) ≤
      lowMixtureWidth n / √(0.18 * (1 - 0.0045)) := by
    rw [h3]
    apply div_le_div_of_nonneg_left hw.le (by positivity)
    nlinarith [sqrt_nonneg (0.18 * (1 - (0.0045 : ℝ)))]
  unfold lowMixtureI
  exact add_le_add (add_le_add le_rfl h2) h3'

theorem lowScaleFactor {n : ℕ} (hn : 8000 ≤ n) :
    cEw (√(2 / (n : ℝ)) * lowMixtureWidth n) (√((2 / (n : ℝ)) * 0.18)) * √(2 / (n : ℝ)) =
      (2 + 2 * lowMixtureWidth n / √(0.18 : ℝ)) / √(0.18 : ℝ) := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hγ : (0 : ℝ) < 2 / n := by positivity
  unfold cEw
  rw [sqrt_mul hγ.le]
  field_simp
  <;> ring

theorem lowLocationFactor {n : ℕ} (hn : 8000 ≤ n) {e : ℝ} (he : 0 < e) :
    √(2 * e * lowMixtureChi n) / √((2 / (n : ℝ)) * 0.18) / √e =
      √((n : ℝ) * lowMixtureChi n / 0.18) := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hχ := lowMixtureChi_pos n
  rw [div_div, ← sqrt_mul (by positivity), ← sqrt_div (by positivity : 0 ≤ 2 * e * lowMixtureChi n)]
  congr 1
  field_simp
  <;> ring

theorem lowMixtureE_pos {n j : ℕ} (hn : 8000 ≤ n) (hj : j ≤ 12) : 0 < lowMixtureE n j := by
  have := lowMixtureI_pos (j := j) hn
  have := lowLatitudeT_pos hn hj
  have := (lowMixtureWidth_bound hn).1
  unfold lowMixtureE
  positivity

theorem lowMixtureLocation_pos {n j : ℕ} (hn : 8000 ≤ n) (hj : j ≤ 12) :
    0 < lowMixtureLocation n j := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have := lowMixtureChi_pos n
  have := lowMixtureI_pos (j := j) hn
  have := lowLatitudeT_pos hn hj
  unfold lowMixtureLocation
  positivity

end BstLean.BlueprintLow

/- Component: Part291AgentHighMoments.lean -/

namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169

theorem agentHighConditionalMomentsBand {n : ℕ} (hn : LowBand n) (c : Ret n)
    (hb : 0 < normSq (bR c))
    (hL : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((paperDesignP n).tau0 c))
    (hCA : normSq c.2.1.2 ≤ 2 * eR c * lowMixtureChi n)
    {j : ℕ} (hj : 1 ≤ j) (hj12 : j ≤ 12) :
    let split := lowPaperSplit (paperDesignP n) c
    (∫ a in keptIx (paperDesignP n) c split,
      condMom split (epsF (paperDesignP n) c split) (2 * j) a ∂muI n) ≤ lowMixtureE n j ^ (2 * j) ∧
    (∫ a in keptIx (paperDesignP n) c split,
      condMom split (delF (paperDesignP n) c split) (2 * j) a ∂muI n) ≤ lowMixtureLocation n j ^ (2 * j) := by
  have hn8 := hn.1
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn.1
  have he : 0 < eR c := div_pos hb (by positivity)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have hχ := lowMixtureChi_pos n
  have hw := (lowMixtureWidth_bound hn.1).1
  have hT := lowLatitudeT_pos hn.1 hj12
  have hloc := agentLatitudeLocation hn c hb hL hj hj12
  have hres := agentLatitudeResidual hn c hL hj hj12
  have hcentre : BstLean.Part188.centreEnergy (Part289.statedDesign2 n) c = eR c := rfl
  rw [lowLocationMoment_eq, hcentre] at hloc
  rw [lowResidualMoment_eq] at hres
  have hh := paper_high_conditional_moments (by omega) (paperDesignP n) c
    (show 0 ≤ lowMixtureWidth n / √(eR c) by positivity)
    (show 0 < √(2 / (n : ℝ)) * lowMixtureWidth n by positivity)
    (show 0 < √((2 / (n : ℝ)) * 0.18) by positivity)
    (by norm_num : (0 : ℝ) < 0.0045) (by norm_num) hCA
  have hI := lowMixtureI_majorizes (j := j) hn.1
  have hcE : 0 ≤ cEw (√(2 / (n : ℝ)) * lowMixtureWidth n) (√((2 / (n : ℝ)) * 0.18)) := by
    unfold cEw
    positivity
  have hiota := (iotaP_pos (by norm_num : (0.0045 : ℝ) < 1) (2 * j)).le
  have hc2 : 0 ≤ c2η 0.0045 := sqrt_nonneg _
  have hc3 : 0 ≤ c3η 0.0045 (√(2 / (n : ℝ)) * lowMixtureWidth n) (√((2 / (n : ℝ)) * 0.18)) := by
    unfold c3η
    positivity
  have hId : iotaP 0.0045 (2 * j) + c2η 0.0045 ≤ lowMixtureI n j :=
    (le_add_of_nonneg_right hc3).trans hI
  constructor
  · apply (hh.1 j (by omega) _ (by positivity) hres).trans
    apply pow_le_pow_left₀ (by positivity)
    calc
      _ = (cEw (√(2 / (n : ℝ)) * lowMixtureWidth n) (√((2 / (n : ℝ)) * 0.18)) * √(2 / (n : ℝ))) *
          ((iotaP 0.0045 (2 * j) + c2η 0.0045 +
            c3η 0.0045 (√(2 / (n : ℝ)) * lowMixtureWidth n) (√((2 / (n : ℝ)) * 0.18))) * lowLatitudeT n j) := by ring
      _ ≤ (cEw (√(2 / (n : ℝ)) * lowMixtureWidth n) (√((2 / (n : ℝ)) * 0.18)) * √(2 / (n : ℝ))) *
          (lowMixtureI n j * lowLatitudeT n j) := by gcongr
      _ = lowMixtureE n j := by rw [lowScaleFactor hn.1]; unfold lowMixtureE; ring
  · apply (hh.2 j (by omega) _ (by positivity) hloc).trans
    apply pow_le_pow_left₀ (by positivity)
    calc
      _ = (√(2 * eR c * lowMixtureChi n) / √((2 / (n : ℝ)) * 0.18) / √(eR c)) *
          ((iotaP 0.0045 (2 * j) + c2η 0.0045) * lowLatitudeT n j) := by ring_nf
      _ ≤ (√(2 * eR c * lowMixtureChi n) / √((2 / (n : ℝ)) * 0.18) / √(eR c)) *
          (lowMixtureI n j * lowLatitudeT n j) := by gcongr
      _ = lowMixtureLocation n j := by rw [lowLocationFactor hn.1 he]; unfold lowMixtureLocation; ring

end BstLean.BlueprintLow

/- Component: Part291ConditionalWindow.lean -/

namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part188

theorem agentSplitPremisesBand {n : ℕ} (hn : LowBand n) (c : Ret n)
    (he : 0 < centreEnergy (paperDesignP n) c)
    (hCA : normSq c.2.1.2 ≤ 2 * eR c * lowMixtureChi n) :
    let split := lowPaperSplit (paperDesignP n) c
    let K := keptIx (paperDesignP n) c split
    0 ≤ lowMixtureEpsilon n ∧ lowMixtureEpsilon n < 1 ∧
    (∀ a ∈ K, 0 ≤ removed (stdGauss (Fin (n - 1))) split.good a ∧
      removed (stdGauss (Fin (n - 1))) split.good a < 1) ∧
    (∀ a ∈ K, (2 / (n : ℝ)) * 0.18 ≤ split.S0 a ∧ ∀ v ∈ slice split a,
      |sA (paperDesignP n) c a v / split.S0 a - 1| ≤ lowMixtureEpsilon n ∧
      |lA (paperDesignP n) c a v - split.lam0 a| ≤ 2 * (lowMixtureWidth n / √(eR c)) ∧
      normSq c.2.1.2 / split.S0 a * (lA (paperDesignP n) c a v - split.lam0 a) ^ 2 ≤ lowMixtureL n) ∧
    (∀ a ∈ K,
      (∫ v in slice split a, (lA (paperDesignP n) c a v - split.lam0 a) ∂stdGauss (Fin (n - 1))) = 0 ∧
      (∫ v in slice split a, (sA (paperDesignP n) c a v / split.S0 a - 1) ∂stdGauss (Fin (n - 1))) = 0) := by
  have hn8 := hn.1
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn.1
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have he' : 0 < eR c := he
  have hχ := lowMixtureChi_pos n
  have hw := (lowMixtureWidth_bound hn.1).1
  have hε := lowMixtureEpsilon_bound hn.1
  have hsmall : eps0 (√(2 / (n : ℝ)) * lowMixtureWidth n) (√((2 / (n : ℝ)) * 0.18)) < 1 := by
    rw [lowPaperSplit_epsilon hn.1]
    linarith [hε.2]
  have h := paperSplitPremises (by omega) (paperDesignP n) c
    (show 0 ≤ lowMixtureWidth n / √(eR c) by positivity)
    (show 0 < √(2 / (n : ℝ)) * lowMixtureWidth n by positivity)
    (show 0 < √((2 / (n : ℝ)) * 0.18) by positivity)
    (by norm_num : (0 : ℝ) < 0.0045) (by norm_num) hCA hsmall
  have hs : √((2 / (n : ℝ)) * 0.18) ^ 2 = (2 / (n : ℝ)) * 0.18 := sq_sqrt (by positivity)
  have hL : (√(2 * eR c * lowMixtureChi n) * (2 * (lowMixtureWidth n / √(eR c))) /
      √((2 / (n : ℝ)) * 0.18)) ^ 2 = lowMixtureL n := by
    rw [div_pow, mul_pow, sq_sqrt (by positivity), mul_pow, div_pow, sq_sqrt he'.le, hs]
    unfold lowMixtureL
    field_simp
    <;> ring
  rcases h with ⟨h0, h1, hβ, hwin, hcent⟩
  refine ⟨hε.1, by change eps0 _ _ < 1; linarith [hε.2], hβ, ?_, hcent⟩
  intro a ha
  obtain ⟨hS, hv⟩ := hwin a ha
  rw [hs] at hS
  refine ⟨hS, fun v hv' => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hv v hv'
  rw [lowPaperSplit_epsilon hn.1] at h1
  rw [hL] at h3
  exact ⟨h1, h2, h3⟩

end BstLean.BlueprintLow

/- Component: Part291HighOrderComparison.lean -/

namespace BstLean.BlueprintLow
open Real Set
open BstLean.Part162 BstLean.Part195

theorem lowMixtureI_lower {n j : ℕ} (hn : 8000 ≤ n) : 1 ≤ lowMixtureI n j := by
  have h : (1 : ℝ) ≤ iotaP 0.0045 (2 * j) := by
    unfold iotaP
    exact one_le_rpow (by norm_num) (by positivity)
  have hw := (lowMixtureWidth_bound hn).1
  unfold lowMixtureI
  linarith [div_nonneg (sqrt_nonneg (0.0045 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1 - 0.0045),
    div_nonneg hw.le (sqrt_nonneg (0.18 * (1 - (0.0045 : ℝ))))]

theorem lowMixtureI_four_upper {n : ℕ} (hn : 8000 ≤ n) : lowMixtureI n 4 ≤ 1.08 := by
  have hi : iotaP 0.0045 (2 * 4) ≤ (1.001 : ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1.001)
    rw [iotaP_pow (by norm_num : (0.0045 : ℝ) < 1) (by norm_num : (8 : ℕ) ≠ 0)]
    norm_num
  have hs : √(0.0045 : ℝ) ≤ 0.067083 := sqrt_le_iff.mpr (by norm_num)
  have hd : (0.4233 : ℝ) ≤ √(0.18 * (1 - (0.0045 : ℝ))) := le_sqrt_of_sq_le (by norm_num)
  have hw := (lowMixtureWidth_bound hn).2
  unfold lowMixtureI
  calc
    _ ≤ (1.001 : ℝ) + 0.067083 / (1 - 0.0045) + 0.0036715 / 0.4233 := by gcongr
    _ ≤ (1.08 : ℝ) := by norm_num

theorem rotation_six_lower : (3.3 : ℝ) ≤ rotationConstant 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (rotationConstant_nonneg 6)
  rw [show (12 : ℕ) = 2 * 6 by norm_num, rotationConstant_pow (by norm_num) (by norm_num), gmom_even]
  have hpi : (3.141592 : ℝ) ≤ π := pi_gt_d6.le
  calc
    _ ≤ (3.141592 / 2 : ℝ) ^ (2 * 6) * (∏ j ∈ Finset.range 6, (2 * j + 1 : ℝ)) := by
      norm_num [Finset.prod_range_succ]
    _ ≤ _ := by gcongr

theorem lowLatitude_I_order {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureI n 4 * lowLatitudeT n 4 ≤ lowMixtureI n 6 * lowLatitudeT n 6 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hi4 := lowMixtureI_four_upper hn
  have hi6 := lowMixtureI_lower (j := 6) hn
  have hi40 := (lowMixtureI_pos (j := 4) hn).le
  have hi60 := (lowMixtureI_pos (j := 6) hn).le
  have hr4 := BstLean.Part252.rotation_four
  have hr6 := rotation_six_lower
  have hr40 := rotationConstant_nonneg 4
  have hr60 := rotationConstant_nonneg 6
  unfold lowLatitudeT
  norm_num only [Nat.cast_ofNat]
  have h8 : (2 : ℝ) * 4 = 8 := by norm_num
  have h12 : (2 : ℝ) * 6 = 12 := by norm_num
  simp only [h8, h12] at *
  have hroot : √((1521 / 500 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1 - 8))) ≤
      √((1521 / 500 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1 - 12))) := by
    apply sqrt_le_sqrt
    apply div_le_div_of_nonneg_left (by norm_num) (mul_pos (by linarith) (by linarith))
    nlinarith
  calc
    _ ≤ 1.08 * ((285 / 100 : ℝ) * √((1521 / 500 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1 - 12)))) :=
      mul_le_mul hi4 (mul_le_mul hr4 hroot (sqrt_nonneg _) (by norm_num))
        (mul_nonneg hr40 (sqrt_nonneg _)) (by norm_num)
    _ ≤ 1 * ((3.3 : ℝ) * √((1521 / 500 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1 - 12)))) := by
      nlinarith [sqrt_nonneg ((1521 / 500 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1 - 12)))]
    _ ≤ _ := mul_le_mul hi6 (mul_le_mul_of_nonneg_right hr6 (sqrt_nonneg _))
      (mul_nonneg (by norm_num) (sqrt_nonneg _)) hi60

theorem lowMixtureHigh_order {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureE n 4 ≤ lowMixtureE n 6 ∧ lowMixtureLocation n 4 ≤ lowMixtureLocation n 6 := by
  have h := lowLatitude_I_order hn
  have hw := (lowMixtureWidth_bound hn).1
  constructor
  · unfold lowMixtureE
    convert mul_le_mul_of_nonneg_left h
      (show 0 ≤ (2 + 2 * lowMixtureWidth n / √(0.18 : ℝ)) / √(0.18 : ℝ) by positivity) using 1 <;> ring
  · unfold lowMixtureLocation
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (sqrt_nonneg ((n : ℝ) * lowMixtureChi n / 0.18))

theorem lowMixtureT_order {n : ℕ} (hn : 8000 ≤ n) : lowMixtureT n 4 ≤ lowMixtureT n 6 := by
  obtain ⟨he, hl⟩ := lowMixtureHigh_order hn
  have he0 := (lowMixtureE_pos hn (by norm_num : 4 ≤ 12)).le
  have hl0 := (lowMixtureLocation_pos hn (by norm_num : 4 ≤ 12)).le
  have hl60 := hl0.trans hl
  have hε := lowMixtureEpsilon_bound hn
  have hk : 0 ≤ lowMixtureK n := by
    unfold lowMixtureK lowMixtureEpsilon
    exact inv_nonneg.mpr (by nlinarith [hε.1, hε.2])
  unfold lowMixtureT tK
  gcongr

end BstLean.BlueprintLow

/- Component: Part291AgentChi.lean -/

namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part188 BstLean.Part242

theorem lowMixturePrice_majorant {n : ℕ} (hn : 8000 ≤ n) :
    priceC (lowMixtureK n) n (√(lowMixtureL n)) (lowMixtureEpsilon n)
      (exp (lowMixtureK n * ((n : ℝ) * lowMixtureEpsilon n ^ 2 / 2 +
        lowMixtureL n * (1 + lowMixtureEpsilon n))))
      (lowMixtureA n) (lowMixtureD n (lowMixtureChi n))
      (lowMixtureE n 4) (lowMixtureLocation n 4) (lowMixtureE n 6) (lowMixtureLocation n 6) ≤
        lowMixtureQ n := by
  have hL := lowMixtureL_nonneg n
  have hA := (lowMixtureA_pos hn).le
  have hD := (lowMixtureD_pos hn).le
  have heq : √(lowMixtureL n) * √(lowMixtureA n * lowMixtureD n (lowMixtureChi n)) =
      √(lowMixtureL n * lowMixtureA n * lowMixtureD n (lowMixtureChi n)) := by
    rw [← sqrt_mul hL, mul_assoc]
  have hε := lowMixtureEpsilon_bound hn
  have hk : 0 ≤ lowMixtureK n := by
    unfold lowMixtureK lowMixtureEpsilon
    exact inv_nonneg.mpr (by nlinarith [hε.1, hε.2])
  have h40 : 0 ≤ lowMixtureT n 4 := tK_nonneg hk (Nat.cast_nonneg n) (sqrt_nonneg _)
    (lowMixtureE_pos hn (by norm_num : 4 ≤ 12)).le (lowMixtureLocation_pos hn (by norm_num : 4 ≤ 12)).le
  have h46 := lowMixtureT_order hn
  have h60 := h40.trans h46
  have htail : lowMixtureT n 4 ^ 2 * lowMixtureT n 6 ^ 3 ≤ lowMixtureT n 6 ^ 5 := by
    calc
      _ ≤ lowMixtureT n 6 ^ 2 * lowMixtureT n 6 ^ 3 := by gcongr
      _ = _ := by ring
  unfold priceC lowMixtureQ lowMixtureT2
  rw [heq]
  change _ + lowMixtureT n 4 ^ 2 * lowMixtureT n 6 ^ 3 / 120 + _ ≤
    _ + lowMixtureT n 6 ^ 5 / 120 + _
  dsimp only [lowMixtureT] at htail ⊢
  linarith

theorem agentChiBand {n : ℕ} (hn : LowBand n) (c : Ret n)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP n).tau0 c) (hb : 0 < normSq (bR c))
    (hI : WFInterfaces (paperDesignP n) c agentDirectionCap (agentEnergyMomentCap / n) agentParallelCap)
    (hE : centreEnergy (paperDesignP n) c ≤ agentEnergyCap)
    (hL : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((paperDesignP n).tau0 c))
    (hcA : 0 < normSq c.2.1.2)
    (hCA : normSq c.2.1.2 ≤ 2 * eR c * lowMixtureChi n) :
    let split := lowPaperSplit (paperDesignP n) c
    IntegrableOn (chiK (paperDesignP n) c split) (keptIx (paperDesignP n) c split) (muI n) ∧
    (∫ a in keptIx (paperDesignP n) c split, chiK (paperDesignP n) c split a ∂muI n) ≤ lowMixtureQ n := by
  have hn8 := hn.1
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn.1
  have he : 0 < eR c := div_pos hb (by positivity)
  have hw := (lowMixtureWidth_bound hn.1).1
  obtain ⟨hε0, hε1, hβ, hwin, hcent⟩ := agentSplitPremisesBand hn c he hCA
  obtain ⟨hA2, hA3, hD2, hD3⟩ := agentConditionalNormsBand hn c hc hτ hb hI hE hL
    (lowMixtureChi_pos n).le hCA
  obtain ⟨he4, hd4⟩ := agentHighConditionalMomentsBand hn c hb hL hCA (j := 4) (by norm_num) (by norm_num)
  obtain ⟨he6, hd6⟩ := agentHighConditionalMomentsBand hn c hb hL hCA (j := 6) (by norm_num) (by norm_num)
  have H := conditional_chi_integral (paperDesignP n) c (lowPaperSplit (paperDesignP n) c)
    hε0 hε1 (show 0 ≤ 2 * (lowMixtureWidth n / √(eR c)) by positivity)
    (sqrt_nonneg (lowMixtureL n)) (show 0 < (2 / (n : ℝ)) * 0.18 by positivity) hcA
    (fun a ha => by simpa only [sq_sqrt (lowMixtureL_nonneg n)] using hwin a ha) hcent
    hA2.nonneg hD2.nonneg
    (lowMixtureE_pos hn.1 (by norm_num : 4 ≤ 12)).le (lowMixtureLocation_pos hn.1 (by norm_num : 4 ≤ 12)).le
    (lowMixtureE_pos hn.1 (by norm_num : 6 ≤ 12)).le (lowMixtureLocation_pos hn.1 (by norm_num : 6 ≤ 12)).le
    hA2.squareIntegral.2 hD2.squareIntegral.2 he4 hd4 he6 hd6
  refine ⟨H.1, H.2.trans ?_⟩
  rw [sq_sqrt (lowMixtureL_nonneg n)]
  exact lowMixturePrice_majorant hn.1

end BstLean.BlueprintLow

/- Component: Part291ConditionalHQ.lean -/

namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part188 BstLean.Part242

theorem agentHQBand {n : ℕ} (hn : LowBand n) (c : Ret n)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP n).tau0 c) (hb : 0 < normSq (bR c))
    (hI : WFInterfaces (paperDesignP n) c agentDirectionCap (agentEnergyMomentCap / n) agentParallelCap)
    (hE : centreEnergy (paperDesignP n) c ≤ agentEnergyCap)
    (hL : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((paperDesignP n).tau0 c))
    (hCA : normSq c.2.1.2 ≤ 2 * eR c * lowMixtureChi n) :
    let split := lowPaperSplit (paperDesignP n) c
    LBound ((muI n).restrict (keptIx (paperDesignP n) c split)) 3
      (fun a => BstLean.Part207.hqL n (lowMixtureEpsilon n)
        (condMom split (epsF (paperDesignP n) c split) 2 a)
        (condMom split (delF (paperDesignP n) c split) 2 a)) (lowMixtureHQ n) := by
  obtain ⟨hA2, hA3, hD2, hD3⟩ := agentConditionalNormsBand hn c hc hτ hb hI hE hL
    (lowMixtureChi_pos n).le hCA
  have hε : lowMixtureEpsilon n < 1 := by
    have := (lowMixtureEpsilon_bound hn.1).2
    change eps0 _ _ < 1
    linarith
  exact HQ_L3 n hε (lowMixtureA_pos hn.1) (lowMixtureD_pos hn.1) hA3 hD3
    (condMom_nonneg _ _ _) (condMom_nonneg _ _ _)

end BstLean.BlueprintLow

/- Component: Part291ConditionalDisplacement.lean -/

namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part188 BstLean.Part242

/-- The two displacement terms use different denominators. The location
term keeps the actual conditional mean, while the scale term uses the cut. -/
theorem normalized_displacement {n : ℕ} (hn : 8000 ≤ n) (c : Ret n)
    (he : 0 < eR c) {χ : ℝ} (hCA : normSq c.2.1.2 ≤ 2 * eR c * χ)
    {a : Ix n} (ha : a ∈ keptIx (paperDesignP n) c (lowPaperSplit (paperDesignP n) c)) :
    let split := lowPaperSplit (paperDesignP n) c
    let ν := stdGauss (Fin (n - 1))
    let β := removed ν split.good a
    let Z := goodMeanSq ν (slice split a) (fun v => zLatitude c (a, v))
    hellG2 n ((split.lam0 a - split.lamb a) ^ 2 * normSq c.2.1.2)
      (split.S0 a) (split.Sb a) ≤
      β * (((n : ℝ) * χ / (2 * (1 - 0.0045))) *
          (conditionalVariance ν (fun v => fLatitude c (a, v)) / Z) +
        ((n : ℝ) / (8 * (1 - 0.0045) ^ 2 * 0.18 ^ 2)) *
          conditionalVariance ν (fun v => zLatitude c (a, v) ^ 2)) := by
  dsimp only
  let D := paperDesignP n
  let split := lowPaperSplit D c
  let ν := stdGauss (Fin (n - 1))
  let γ := 2 / (n : ℝ)
  let Z := goodMeanSq ν (slice split a) (fun v => zLatitude c (a, v))
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts (by omega) D c
    (by norm_num : (0 : ℝ) < 0.0045) (by norm_num) ha
  have hs : sgA D c a = fun v => √γ * zLatitude c (a, v) := by
    funext v
    unfold zLatitude
    change _ = √γ * (_ / √γ)
    field_simp
    rfl
  have hs2 : (fun v => sgA D c a v ^ 2) = fun v => γ * zLatitude c (a, v) ^ 2 := by
    funext v
    have hh := congrFun hs v
    rw [hh, mul_pow, sq_sqrt hγ.le]
  have hf : (fun v => fLatitude c (a, v)) = fun v => √(eR c) * lA D c a v := by
    funext v
    exact fX_eq_lam c _
  have hZ : goodMeanSq ν (slice split a) (sgA D c a) = γ * Z := by
    rw [hs, goodMeanSq_scale, sq_sqrt hγ.le]
  have hV : conditionalVariance ν (fun v => sgA D c a v ^ 2) =
      γ ^ 2 * conditionalVariance ν (fun v => zLatitude c (a, v) ^ 2) := by
    rw [hs2, BstLean.Part252.conditionalVariance_scale]
  have hF : conditionalVariance ν (fun v => fLatitude c (a, v)) =
      eR c * conditionalVariance ν (lA D c a) := by
    rw [hf, BstLean.Part252.conditionalVariance_scale, sq_sqrt he.le]
  have h := idx_disp_good_mean n (measurableSet_slice split a) hm
    (measurable_lA_left D c a) (measurable_sgA_left D c a)
    (abs_lA_le (by omega) D c a) (abs_sgA_le (by omega) D c a)
    (show 0 < √(γ * 0.18) by positivity) (fun v hv => (hGψ v hv).2)
    hm1 (by norm_num : (0.0045 : ℝ) < 1) (normSq_nonneg c.2.1.2)
  have hβ : 1 - ν.real (slice split a) = removed ν split.good a := by
    rw [slice_real, sub_sub_cancel]
  change hellG2 n _ _ _ ≤ _ at h
  rw [hβ] at h
  change split.S0 a = ∫ v, sgA D c a v ^ 2 ∂nrm ν (slice split a) at hS
  change split.lam0 a = ∫ v, lA D c a v ∂nrm ν (slice split a) at hl
  have hleft : hellG2 n ((∫ v, lA D c a v ∂nrm ν (slice split a) - ∫ v, lA D c a v ∂ν) ^ 2 * normSq c.2.1.2)
      (∫ v, sgA D c a v ^ 2 ∂nrm ν (slice split a)) (∫ v, sgA D c a v ^ 2 ∂ν) =
      hellG2 n ((split.lam0 a - split.lamb a) ^ 2 * normSq c.2.1.2) (split.S0 a) (split.Sb a) := by
    rw [← hl, ← hS]
    rfl
  rw [hleft] at h
  change _ ≤ removed ν split.good a *
    (normSq c.2.1.2 * conditionalVariance ν (lA D c a) /
      (2 * (1 - 0.0045) * goodMeanSq ν (slice split a) (sgA D c a)) +
      n * conditionalVariance ν (fun v => sgA D c a v ^ 2) /
      (8 * (1 - 0.0045) ^ 2 * √(γ * 0.18) ^ 4)) at h
  rw [hZ, hV, show √(γ * 0.18) ^ 4 = γ ^ 2 * 0.18 ^ 2 by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_sqrt (by positivity), mul_pow]] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (removed_nonneg _ _ _))
  rw [hF]
  apply add_le_add
  · calc
      _ ≤ (2 * eR c * χ) * conditionalVariance ν (lA D c a) /
          (2 * (1 - 0.0045) * (γ * Z)) := by
            apply div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hCA (integral_nonneg fun _ => sq_nonneg _))
            have : 0 ≤ Z := sq_nonneg _
            positivity
      _ = _ := by dsimp [γ]; field_simp <;> ring
  · apply le_of_eq
    field_simp <;> ring

end BstLean.BlueprintLow

/- Component: Part291LatitudeSquareVariance.lean -/

namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part188 BstLean.Part242 BstLean.Part248

/-- The displacement scale variance needs latitude order eight, not order
twelve. Both moments are on the original product measure. -/
theorem agentSquareVarianceBand {n : ℕ} (hn : LowBand n) (c : Ret n)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP n).tau0 c) (hb : 0 < normSq (bR c))
    (hI : WFInterfaces (paperDesignP n) c agentDirectionCap (agentEnergyMomentCap / n) agentParallelCap)
    (hL : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((paperDesignP n).tau0 c)) :
    LBound (muI n) 2
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v) ^ 2))
      ((2 * (1 + agentEnergyMomentCap / n) * lowLatitudeT n 4) ^ 2) := by
  have hn8 := hn.1
  let ν := stdGauss (Fin (n - 1))
  obtain ⟨M, hM⟩ := bounded_zLatitude (by omega) c hb.ne'
  have hen := energy_latitude (by omega) c hc hτ hI.energy
  have hz : LBound ((muI n).prod ν) 8 (zLatitude c) (1 + agentEnergyMomentCap / n) :=
    z_norm_order _ (by simp [ν]) (q := 8) (by omega) (by omega)
      (measurable_zLatitude c) (zLatitude_nonneg c)
      (fun q => by rw [zLatitude_sq (by omega) c hb.ne']; nlinarith [sq_nonneg (fLatitude c q)]) hen
  have hc8 := lowLatitude_residual_norm hn c hL (q := 4) (by omega) (by omega)
  have hsd := conditional_squareSD (muI n) ν hM hz hc8
  have hh : LBound (muI n) 2 (fun a => squareSD ν (zLatitude c) a * squareSD ν (zLatitude c) a)
      ((2 * (1 + agentEnergyMomentCap / n) * lowLatitudeT n 4) *
        (2 * (1 + agentEnergyMomentCap / n) * lowLatitudeT n 4)) := hsd.mul hsd
  have heq : (fun a => squareSD ν (zLatitude c) a * squareSD ν (zLatitude c) a) =
      fun a => conditionalVariance ν (fun v => zLatitude c (a, v) ^ 2) := by
    funext a
    unfold squareSD conditionalVariance
    rw [← sq, sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
  rw [heq] at hh
  simpa only [pow_two] using hh

end BstLean.BlueprintLow

/- Component: Part291DisplacementIntegral.lean -/

namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part188 BstLean.Part242

theorem agentDisplacementFromRemoval {n : ℕ} (hn : LowBand n) (c : Ret n)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP n).tau0 c) (hb : 0 < normSq (bR c))
    (hI : WFInterfaces (paperDesignP n) c agentDirectionCap (agentEnergyMomentCap / n) agentParallelCap)
    (hE : centreEnergy (paperDesignP n) c ≤ agentEnergyCap)
    (hL : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((paperDesignP n).tau0 c))
    {χ B : ℝ} (hχ : 0 ≤ χ) (hCA : normSq c.2.1.2 ≤ 2 * eR c * χ) (hB0 : 0 ≤ B)
    (hB : (∫ a, removed (stdGauss (Fin (n - 1)))
      (lowPaperSplit (paperDesignP n) c).good a ∂muI n) ≤ B) :
    let split := lowPaperSplit (paperDesignP n) c
    (∫ a in keptIx (paperDesignP n) c split,
      hellG2 n ((split.lam0 a - split.lamb a) ^ 2 * normSq c.2.1.2)
        (split.S0 a) (split.Sb a) ∂muI n) ≤
      √B / (1 - 0.0045) * (lowMixtureD n χ / 2 +
        n * (2 * (1 + agentEnergyMomentCap / n) * lowLatitudeT n 4) ^ 2 / (4 * 0.18 ^ 2)) := by
  dsimp only
  let split := lowPaperSplit (paperDesignP n) c
  let ν := stdGauss (Fin (n - 1))
  let K := keptIx (paperDesignP n) c split
  let ρ := (muI n).restrict K
  let β := removed ν split.good
  let v := fun a => conditionalVariance ν (fun v => fLatitude c (a, v))
  let R := fun a => 1 / goodMeanSq ν (slice split a) (fun v => zLatitude c (a, v))
  let s := fun a => conditionalVariance ν (fun v => zLatitude c (a, v) ^ 2)
  let S := (2 * (1 + agentEnergyMomentCap / n) * lowLatitudeT n 4) ^ 2
  let c1 := (n : ℝ) * χ / (2 * (1 - 0.0045))
  let c2 := (n : ℝ) / (8 * (1 - 0.0045) ^ 2 * 0.18 ^ 2)
  have hn8 := hn.1
  have he : 0 < eR c := div_pos hb (by exact_mod_cast (show 0 < n by omega))
  have mK : MeasurableSet K := measurableSet_keptSet _ split.mgood (measurableSet_bulkIx _ c) _
  have hm : ρ univ ≤ 1 := (Measure.restrict_le_self univ).trans (by simp)
  have hβ : LBound ρ 2 β (√B) :=
    (removal_L2 (muI n) (measurable_removed ν split.mgood)
      (removed_nonneg _ _) (removed_le_one _ _) hB0 hB).restrict K
  have hv12 := ((lowLatitude_variances hn c he hL).1).restrict K
  have hv : LBound ρ 4 v (lowLatitudeV n) := hv12.lower (by norm_num) (by norm_num) (by norm_num) hm
  have hR := agentMixtureReciprocalBand hn c hc hτ hb hI hE hL
  have hs := (agentSquareVarianceBand hn c hc hτ hb hI hL).restrict K
  have hvr : LBound ρ 2 (fun a => v a * R a) (lowLatitudeV n * lowMixtureReciprocal n) := hv.mul hR
  have hprod : LBound ρ (↑(1 : ℕ) : ℝ≥0∞) (fun a => β a * (v a * R a))
      (√B * (lowLatitudeV n * lowMixtureReciprocal n)) :=
    by simpa only [Nat.cast_one] using
      (LBound.mul (p := 2) (q := 2) (r := 1) hβ hvr)
  have hprodM : BstLean.Part223.MomentBound ρ 1 (fun a => β a * (v a * R a))
      (√B * (lowLatitudeV n * lowMixtureReciprocal n)) := hprod.toMoment (by norm_num)
  have hlocM : BstLean.Part223.MomentBound ρ 1
      (fun a => c1 * (β a * (v a * R a)))
      (c1 * (√B * (lowLatitudeV n * lowMixtureReciprocal n))) :=
    BstLean.Part223.MomentBound.scale (a := c1) hprodM (by positivity)
  have hloc : LBound ρ 1 (fun a => c1 * (β a * (v a * R a)))
      (c1 * (√B * (lowLatitudeV n * lowMixtureReciprocal n))) :=
    by simpa only [Nat.cast_one] using (LBound.ofMoment (by norm_num) hlocM)
  have hsprod : LBound ρ (↑(1 : ℕ) : ℝ≥0∞) (fun a => β a * s a) (√B * S) :=
    by simpa only [Nat.cast_one] using
      (LBound.mul (p := 2) (q := 2) (r := 1) hβ hs)
  have hsprodM : BstLean.Part223.MomentBound ρ 1 (fun a => β a * s a) (√B * S) :=
    hsprod.toMoment (by norm_num)
  have hscaleM : BstLean.Part223.MomentBound ρ 1 (fun a => c2 * (β a * s a))
      (c2 * (√B * S)) := BstLean.Part223.MomentBound.scale (a := c2) hsprodM (by positivity)
  have hscale : LBound ρ 1 (fun a => c2 * (β a * s a)) (c2 * (√B * S)) :=
    by simpa only [Nat.cast_one] using (LBound.ofMoment (by norm_num) hscaleM)
  have hsum := hloc.add (by norm_num) hscale
  have hH : IntegrableOn (fun a => hellG2 n ((split.lam0 a - split.lamb a) ^ 2 * normSq c.2.1.2)
      (split.S0 a) (split.Sb a)) K (muI n) := by
    have mH := (measurable_hellG2 n).comp
      ((((split.mlam0.sub split.mlamb).pow_const 2).mul_const (normSq c.2.1.2)).prodMk
        (split.mS0.prodMk split.mSb))
    refine (intB mH (M := 2) fun a => ?_).integrableOn
    change |hellG2 n ((split.lam0 a - split.lamb a) ^ 2 * normSq c.2.1.2)
      (split.S0 a) (split.Sb a)| ≤ 2
    rw [abs_of_nonneg (hellG2_nonneg n (mul_nonneg (sq_nonneg _) (normSq_nonneg _)) _ _)]
    exact hellG2_le_two n _ _ _
  have hsumAbs : (∫ a in K,
      |c1 * (β a * (v a * R a)) + c2 * (β a * s a)| ∂muI n) ≤
      c1 * (√B * (lowLatitudeV n * lowMixtureReciprocal n)) + c2 * (√B * S) := by
    simpa only [ρ] using (LBound.integralAbs hsum).2
  have hiSigned : IntegrableOn
      (fun a => c1 * (β a * (v a * R a)) + c2 * (β a * s a)) K (muI n) := by
    change Integrable
      (fun a => c1 * (β a * (v a * R a)) + c2 * (β a * s a)) ((muI n).restrict K)
    exact (LBound.integralAbs hsum).1
  have hiAbs : IntegrableOn
      (fun a => |c1 * (β a * (v a * R a)) + c2 * (β a * s a)|) K (muI n) := hiSigned.abs
  have hsumUpper : (∫ a in K,
      c1 * (β a * (v a * R a)) + c2 * (β a * s a) ∂muI n) ≤
      c1 * (√B * (lowLatitudeV n * lowMixtureReciprocal n)) + c2 * (√B * S) := by
    calc
      _ ≤ ∫ a in K,
          |c1 * (β a * (v a * R a)) + c2 * (β a * s a)| ∂muI n := by
        apply setIntegral_mono_on hiSigned hiAbs mK
        intro a ha
        exact le_abs_self _
      _ ≤ _ := hsumAbs
  have hmajor : (∫ a in K, hellG2 n ((split.lam0 a - split.lamb a) ^ 2 * normSq c.2.1.2)
      (split.S0 a) (split.Sb a) ∂muI n) ≤
      c1 * (√B * (lowLatitudeV n * lowMixtureReciprocal n)) + c2 * (√B * S) := by
    apply le_trans (setIntegral_mono_on hH hiSigned mK ?_) hsumUpper
    intro a ha
    have h := normalized_displacement hn.1 c he hCA ha
    refine h.trans (le_of_eq ?_)
    dsimp [β, v, R, s, c1, c2]
    ring
  refine hmajor.trans ?_
  have hD0 : 0 ≤ lowMixtureD n χ := by
    unfold lowMixtureD mixD
    have := hv.nonneg
    have := hR.nonneg
    positivity
  have hloccap : c1 * (√B * (lowLatitudeV n * lowMixtureReciprocal n)) ≤
      √B / (1 - 0.0045) * (lowMixtureD n χ / 2) := by
    have heq : c1 * (√B * (lowLatitudeV n * lowMixtureReciprocal n)) =
        √B * (lowMixtureD n χ / 2) := by dsimp [c1, lowMixtureD, mixD]; ring
    rw [heq]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact le_div_self (sqrt_nonneg _) (by norm_num) (by norm_num)
  have hscap : c2 * (√B * S) ≤ √B / (1 - 0.0045) * ((n : ℝ) * S / (4 * 0.18 ^ 2)) := by
    dsimp [c2]
    have hS : 0 ≤ S := sq_nonneg _
    have hcoef : (1 : ℝ) / (8 * (1 - 0.0045) ^ 2 * 0.18 ^ 2) ≤
        1 / (4 * (1 - 0.0045) * 0.18 ^ 2) := by norm_num
    have hfac : 0 ≤ (n : ℝ) * √B * S :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (sqrt_nonneg B)) hS
    calc
      _ = ((n : ℝ) * √B * S) *
          (1 / (8 * (1 - 0.0045) ^ 2 * 0.18 ^ 2)) := by ring
      _ ≤ ((n : ℝ) * √B * S) * (1 / (4 * (1 - 0.0045) * 0.18 ^ 2)) :=
        mul_le_mul_of_nonneg_left hcoef hfac
      _ = _ := by ring
  calc
    _ ≤ √B / (1 - 0.0045) * (lowMixtureD n χ / 2) +
        √B / (1 - 0.0045) * ((n : ℝ) * S / (4 * 0.18 ^ 2)) := add_le_add hloccap hscap
    _ = _ := by dsimp [S]; ring

end BstLean.BlueprintLow

/- Component: Part291ConditionalCentering.lean -/

namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169 BstLean.Part188

/-- Both conditional errors have zero mean under the normalized good-slice law. -/
theorem agentConditionalCenteringBand {n : ℕ} (hn : LowBand n) (c : Ret n)
    (he : 0 < centreEnergy (paperDesignP n) c)
    (hCA : normSq c.2.1.2 ≤ 2 * eR c * lowMixtureChi n)
    {a : Ix n} (ha : a ∈ keptIx (paperDesignP n) c (lowPaperSplit (paperDesignP n) c)) :
    let split := lowPaperSplit (paperDesignP n) c
    let ν := nrm (stdGauss (Fin (n - 1))) (slice split a)
    (∫ v, sA (paperDesignP n) c a v / split.S0 a - 1 ∂ν) = 0 ∧
    (∫ v, √(normSq c.2.1.2 / split.S0 a) *
      (lA (paperDesignP n) c a v - split.lam0 a) ∂ν) = 0 := by
  dsimp only
  let split := lowPaperSplit (paperDesignP n) c
  let μ := stdGauss (Fin (n - 1))
  have hs := agentSplitPremisesBand hn c he hCA
  have hcent := hs.2.2.2.2 a ha
  have hm : 0 < μ.real (slice split a) := by
    rw [slice_real]
    exact sub_pos.mpr (hs.2.2.1 a ha).2
  have hS := measurableSet_slice split a
  constructor
  · rw [integral_nrm μ hS hm, integral_indicator hS, hcent.2, mul_zero]
  · rw [integral_const_mul, integral_nrm μ hS hm, integral_indicator hS,
      hcent.1, mul_zero, mul_zero]

end BstLean.BlueprintLow

/- Component: Part291ComparisonFields.lean -/

namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169 BstLean.Part188
open BstLean.Part242

/-- The four actual integral comparisons from blueprint node 18. The outside
measure remains the original latitude measure restricted to kept slices. -/
structure AgentComparisonFields {n : ℕ} (c : Ret n) : Prop where
  removal_integrable : Integrable (removed (stdGauss (Fin (n - 1)))
    (lowPaperSplit (paperDesignP n) c).good) (muI n)
  removal_bound : (∫ a, removed (stdGauss (Fin (n - 1)))
    (lowPaperSplit (paperDesignP n) c).good a ∂muI n) ≤ lowMixtureB n
  chi_integrable : IntegrableOn
    (chiK (paperDesignP n) c (lowPaperSplit (paperDesignP n) c))
    (keptIx (paperDesignP n) c (lowPaperSplit (paperDesignP n) c)) (muI n)
  chi_bound : (∫ a in keptIx (paperDesignP n) c (lowPaperSplit (paperDesignP n) c),
    chiK (paperDesignP n) c (lowPaperSplit (paperDesignP n) c) a ∂muI n) ≤ lowMixtureQ n
  hq_norm : LBound ((muI n).restrict (keptIx (paperDesignP n) c (lowPaperSplit (paperDesignP n) c))) 3
    (fun a => BstLean.Part207.hqL n (lowMixtureEpsilon n)
      (condMom (lowPaperSplit (paperDesignP n) c)
        (epsF (paperDesignP n) c (lowPaperSplit (paperDesignP n) c)) 2 a)
      (condMom (lowPaperSplit (paperDesignP n) c)
        (delF (paperDesignP n) c (lowPaperSplit (paperDesignP n) c)) 2 a)) (lowMixtureHQ n)
  displacement_integrable : IntegrableOn (fun a =>
    hellG2 n (((lowPaperSplit (paperDesignP n) c).lam0 a -
      (lowPaperSplit (paperDesignP n) c).lamb a) ^ 2 * normSq c.2.1.2)
      ((lowPaperSplit (paperDesignP n) c).S0 a) ((lowPaperSplit (paperDesignP n) c).Sb a))
    (keptIx (paperDesignP n) c (lowPaperSplit (paperDesignP n) c)) (muI n)
  displacement_bound : (∫ a in keptIx (paperDesignP n) c (lowPaperSplit (paperDesignP n) c),
    hellG2 n (((lowPaperSplit (paperDesignP n) c).lam0 a -
      (lowPaperSplit (paperDesignP n) c).lamb a) ^ 2 * normSq c.2.1.2)
      ((lowPaperSplit (paperDesignP n) c).S0 a) ((lowPaperSplit (paperDesignP n) c).Sb a) ∂muI n) ≤
    √(lowMixtureB n) / (1 - 0.0045) * (lowMixtureD n (lowMixtureChi n) / 2 +
      n * (2 * (1 + agentEnergyMomentCap / n) * lowLatitudeT n 4) ^ 2 / (4 * 0.18 ^ 2))

theorem agentComparisonFieldsBand {n : ℕ} (hn : LowBand n) (c : Ret n)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP n).tau0 c) (hb : 0 < normSq (bR c))
    (hI : WFInterfaces (paperDesignP n) c agentDirectionCap (agentEnergyMomentCap / n) agentParallelCap)
    (hE : centreEnergy (paperDesignP n) c ≤ agentEnergyCap)
    (hL : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((paperDesignP n).tau0 c))
    (hcA : 0 < normSq c.2.1.2)
    (hCA : normSq c.2.1.2 ≤ 2 * eR c * lowMixtureChi n) : AgentComparisonFields c := by
  let split := lowPaperSplit (paperDesignP n) c
  have hrem := agentRemovalBand hn c hc hτ hb hI hE hL
  have hchi := agentChiBand hn c hc hτ hb hI hE hL hcA hCA
  refine ⟨?_, hrem, hchi.1, hchi.2,
    agentHQBand hn c hc hτ hb hI hE hL hCA, ?_,
    agentDisplacementFromRemoval hn c hc hτ hb hI hE hL
      (lowMixtureChi_pos n).le hCA (lowMixtureB_nonneg n) hrem⟩
  · apply intB (measurable_removed _ split.mgood) (M := 1)
    intro a
    rw [abs_of_nonneg (removed_nonneg _ _ _)]
    exact removed_le_one _ _ _
  · have mH := (measurable_hellG2 n).comp
      ((((split.mlam0.sub split.mlamb).pow_const 2).mul_const (normSq c.2.1.2)).prodMk
        (split.mS0.prodMk split.mSb))
    refine (intB mH (M := 2) fun a => ?_).integrableOn
    change |hellG2 n ((split.lam0 a - split.lamb a) ^ 2 * normSq c.2.1.2)
      (split.S0 a) (split.Sb a)| ≤ 2
    rw [abs_of_nonneg (hellG2_nonneg n (mul_nonneg (sq_nonneg _) (normSq_nonneg _)) _ _)]
    exact hellG2_le_two n _ _ _

end BstLean.BlueprintLow
