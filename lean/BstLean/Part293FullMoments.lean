import BstLean.Part293LowNormalization
import BstLean.Part248Supply
import BstLean.Part252VarianceMoment

/-! Full latitude moments for the fixed bias caps use the existing paid events. -/
namespace BstLean.Part293
open Real MeasureTheory Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part188 BstLean.Part242 BstLean.Part248
open BstLean.Part293.Model

theorem fullMean_low_bound {n : ℕ} (c : Ret n)
    (hI : WFInterfaces (paperDesignP n) c agentDirectionCap
      (agentEnergyMomentCap / n) agentParallelCap)
    (hE : centreEnergy (paperDesignP n) c ≤ agentEnergyCap) :
    |fullMean c| ≤ lowMixtureMean n := by
  have hlo := (abs_le.mp hI.parallel.2).1
  have hhi := (abs_le.mp hI.parallel.2).2
  have hs := sqrt_le_sqrt hE
  have hs0 := sqrt_nonneg (centreEnergy (paperDesignP n) c)
  apply abs_le.mpr
  constructor <;> dsimp [fullMean, lowMixtureMean] <;>
    linarith [sqrt_nonneg agentEnergyCap, sqrt_nonneg (agentParallelCap / n)]

theorem full_location_caps {n : ℕ} (hn : 8000 ≤ n) (c : Ret n)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP n).tau0 c) (hb : 0 < normSq (bR c))
    (hI : WFInterfaces (paperDesignP n) c agentDirectionCap
      (agentEnergyMomentCap / n) agentParallelCap)
    (hE : centreEnergy (paperDesignP n) c ≤ agentEnergyCap) (K : Set (Ix n)) :
    LBound ((muI n).restrict K) 8 (fbR c) 0.85428 ∧
      LBound ((muI n).restrict K) 24 (fbR c) 0.86139 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have hx1 : 1 / (n : ℝ) ≤ 1 / 8000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have hmu := fullMean_low_bound c hI hE
  have hdir p (hp : 1 ≤ p) (hp12 : p ≤ 12) :=
    direction_latitude (by omega) c hc hτ hb hp hp12 hI.direction
  have hs : agentDirectionCap / (n : ℝ) = (1 / n) * (27323 / 250000 : ℝ) := by
    norm_num [agentDirectionCap] <;> ring
  constructor
  · have h := FB_network (by omega) c 4 (by omega) K hmu
      (by convert (hdir 4 (by omega) (by omega)) using 1 <;> norm_num)
    norm_num only [Nat.cast_ofNat] at h
    have hcap : lowMixtureMean n + BstLean.Part195.rotationConstant 4 *
        √(agentDirectionCap / n) ≤ (0.85428 : ℝ) := by
      rw [lowMean_normalized, hs, ← Envelope.F8_formula]
      exact (Envelope.F8_bounds _ hx0 hx1).2.trans (by norm_num)
    exact ⟨h.measurable, by norm_num, h.bound.trans (ENNReal.ofReal_le_ofReal hcap)⟩
  · have h := FB_network (by omega) c 12 (by omega) K hmu
      (by convert (hdir 12 (by omega) (by omega)) using 1 <;> norm_num)
    norm_num only [Nat.cast_ofNat] at h
    have hcap : lowMixtureMean n + BstLean.Part195.rotationConstant 12 *
        √(agentDirectionCap / n) ≤ (0.86139 : ℝ) := by
      rw [lowMean_normalized, hs, ← Envelope.F24_formula]
      exact (Envelope.F24_bounds _ hx0 hx1).2.trans (by norm_num)
    exact ⟨h.measurable, by norm_num, h.bound.trans (ENNReal.ofReal_le_ofReal hcap)⟩

theorem full_variance_cap {n : ℕ} (hn : 8000 ≤ n) (c : Ret n)
    (he : 0 < eR c)
    (hk : BstLean.Part160.agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (3.042 / n))) (K : Set (Ix n)) :
    LBound ((muI n).restrict K) 2 (fun a => (n : ℝ) * VR c a) 0.0003804 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hcap : (3.042 : ℝ) / ((n : ℝ) - 3) ≤ 0.0003804 := by
    rw [div_le_iff₀ (show (0 : ℝ) < (n : ℝ) - 3 by linarith)]
    linarith
  have h := BstLean.Part252.variance_moment_of_latitude (by omega) c he
    (by norm_num : (0 : ℝ) < 3.042) hk K
  obtain ⟨MV, hV⟩ := bdd_VR (by omega) c
  have hi := intOn_of_bdd (((measurable_VR c).const_mul (n : ℝ)).pow_const 2)
    (bdd_pow (bdd_nmul hV) 2) K
  apply LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
  refine ⟨(measurable_VR c).const_mul _, by norm_num, ?_⟩
  simp only [sq_abs]
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun a => sq_nonneg ((n : ℝ) * VR c a))]
  apply ENNReal.ofReal_le_ofReal
  exact h.trans (pow_le_pow_left₀ (div_nonneg (by norm_num) (by linarith)) hcap 2)

end BstLean.Part293
