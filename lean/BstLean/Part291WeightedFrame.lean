import BstLean.Part291FrameNetwork
import BstLean.Part291Rectangles
import BstLean.Part291SchurSelection
import BstLean.Part291LocalEnergyNetwork
import BstLean.Part291Arithmetic

namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part169 BstLean.Part188

theorem frameNoiseUpper_range (j : Fin 160) :
    frameNoiseUpper j ∈ Icc (0.46 : ℝ) 0.54 := by
  have hj : (j.val : ℝ) ≤ 159 := by exact_mod_cast (show j.val ≤ 159 by omega)
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  unfold frameNoiseUpper
  constructor <;> linarith

/-- Blueprint node 40: one uniform band, with six dimension intervals and
160 noise intervals. The Schur event selects one cell and pays 1/4000. -/
theorem weightedFrameBand {n : ℕ} (hn : LowBand n) (c : Ret n)
    (hw : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc (0.472 : ℝ) 0.528)
    (hc : 0 < normSq c.1.2) (hτ : 0 < (paperDesignP n).tau0 c)
    (hC : c.2.1.1 ∈ agentCentreEvent c.1.2 ((paperDesignP n).tau0 c))
    (hS : ((c.1.2,(paperDesignP n).tau0 c),c.2.1.1) ∈ lowSchurBandEvent n)
    (v : Fin (mA n) → ℝ) (hv : normSq v = 1) :
    (n : ℝ) * ∫ ξ, (∑ j, eDir ((BstLean.Part289.statedDesign2 n).bA c.1 c.2.1.1)
      (hStand (BstLean.Part289.statedDesign2 n) c ξ) j * v j) ^ 2
      ∂stdGauss (Fin n) < weightedFrameCap := by
  have hn8 := hn.1
  have hw' : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc (0.46 : ℝ) 0.54 :=
    ⟨by linarith [hw.1],by linarith [hw.2]⟩
  obtain ⟨i,hi⟩ := frame_dimension_cover hn
  obtain ⟨j,hj,hjS⟩ := lowSchurBandEvent_select hw' hS
  let R := lowRectangleBand i j
  have hEnc := R.enclosures n hi _ hj
  obtain ⟨hb,hI,_,_⟩ := agentCentreFieldsBand hn hw hc hτ hC
  have hD_bA : (BstLean.Part289.statedDesign2 n).bA = (paperDesignP n).bA := rfl
  have hD_tau : (BstLean.Part289.statedDesign2 n).tau0 = (paperDesignP n).tau0 := by
    rw [BstLean.Part289.statedDesign2_tau0, BstLean.Part272.statedDesign_tau0]
  have hcoord : BstLean.Part188.centreCoordinate (BstLean.Part289.statedDesign2 n) c =
      BstLean.Part188.centreCoordinate (paperDesignP n) c := by
    funext ξ
    simp only [BstLean.Part188.centreCoordinate, BstLean.Part157.hStand, hD_bA, hD_tau]
  have hIpaper : WFInterfaces (paperDesignP n) c agentDirectionCap
      (agentEnergyMomentCap / n) agentParallelCap := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [BstLean.Part188.DirectionMoment, hcoord] using hI.direction
    · simpa [BstLean.Part188.EnergyMoment, BstLean.Part188.inputEnergy,
        BstLean.Part157.hStand, BstLean.Part289.statedDesign2_tau0,
        BstLean.Part272.statedDesign_tau0] using hI.energy
    · simpa [BstLean.Part188.ParallelCentre, BstLean.Part188.centreEnergy,
        BstLean.Part188.centreCoordinate, BstLean.Part157.hStand,
        BstLean.Part289.statedDesign2_tau0, BstLean.Part272.statedDesign_tau0,
        hD_bA] using hI.parallel
  have hfull := agentLocalCentreBand hn (frameNoiseUpper_range j)
    ⟨hw'.1,hj.2⟩ hc hτ hC (R.centre n hi)
  have henergy := agentLocalEnergyBand hn hw hj.1 hτ hC (R.energy_source n hn8)
  have hX := agentXi4Band hn8 c.1.2 hτ hC
  have S := lowTISupplyBand hn8 j
  have hcov0 := lowFrame_covariance hn8 (paperDesignP n) c S hj hτ hjS hX
  have hcov : COV_at (paperDesignP n) c R.cov := by
    intro w
    apply (hcov0 w).trans
    gcongr
    exact hEnc.covariance
  have hSchur := lowFrame_weightedSchur hn8 (paperDesignP n) c S hj hτ hb
    (BstLean.Part263.paper_centre_nonneg c) hIpaper henergy hEnc.gap hjS hX
  have hTest := weightedTests_from_interfaces (by omega : 50 ≤ n) (paperDesignP n) c hτ hb
    (BstLean.Part263.paper_centre_nonneg c) hIpaper henergy hcov hfull R.nonneg.2.2.1 R.nonneg.1
    R.nonneg.2.2.2.1 (by norm_num : (0 : ℝ) < 0.0045) (by norm_num : (0.0045 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 0.216) hEnc.gap
    (fun w => (hSchur w).trans (mul_le_mul_of_nonneg_right hEnc.projected (normSq_nonneg w))) v hv
  have hGB0 : 0 ≤ frameGB n ((1 - 0.0045) ^ 2) 0.216 agentDirectionCap
      (agentEnergyMomentCap / n) R.cov R.full := by
    unfold frameGB
    have hf := R.nonneg.1
    have hc0 := R.nonneg.2.2.1
    norm_num [agentDirectionCap,agentEnergyMomentCap]
    positivity
  have hm0 : 0 ≤ rwWeightMean ((1 - 0.0045) ^ 2) 0.216 (lowFrameMean n R.energy)
      (√(agentDirectionCap / n)) := by
    have hy : 0 < (1 - 0.0045) ^ 2 - lowFrameMean n R.energy ^ 2 :=
      lt_trans (by norm_num) hEnc.gap
    unfold rwWeightMean lowFrameMean
    positivity
  have hpaper :
      (n : ℝ) * ∫ ξ,
        (∑ j, eDir ((paperDesignP n).bA c.1 c.2.1.1)
          (hStand (paperDesignP n) c ξ) j * v j) ^ 2
          ∂stdGauss (Fin n) < weightedFrameCap := by
    apply weighted_unit_test_of_certificate (by omega : 6 ≤ n)
      (paperDesignP n) c v hv hτ (by simpa only [hD_bA] using hb)
      (by norm_num) R.nonneg.2.2.2.1 hGB0 R.nonneg.2.2.1
      (by norm_num [agentDirectionCap]; positivity) (sqrt_nonneg _) hTest R.scalar le_rfl hEnc.cap_energy
      _ hEnc.variance hEnc.bad_input
    dsimp only
    have hm0' : 0 ≤ rwWeightMean ((1 - 0.0045) ^ 2) 0.216
        (√R.energy + √(agentParallelCap / n)) (√(agentDirectionCap / n)) := by
      simpa [lowFrameMean] using hm0
    have hmw : rwWeightMean ((1 - 0.0045) ^ 2) 0.216
        (√R.energy + √(agentParallelCap / n)) (√(agentDirectionCap / n)) ≤ R.W2 := by
      simpa [lowFrameMean] using hEnc.weight_mean
    rw [sq_sqrt hm0']
    exact mul_le_mul_of_nonneg_right hmw R.nonneg.1
  simpa [BstLean.Part157.hStand, hD_bA, hD_tau] using hpaper

def lowFrameRetained (n : ℕ) : Set (Ret n) := {c |
  BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc (0.472 : ℝ) 0.528 ∧
  0 < normSq c.1.2 ∧ 0 < (paperDesignP n).tau0 c ∧
  c.2.1.1 ∈ agentCentreEvent c.1.2 ((paperDesignP n).tau0 c) ∧
  ((c.1.2,(paperDesignP n).tau0 c),c.2.1.1) ∈ lowSchurBandEvent n}

theorem weightedFrameBand_hyp {n : ℕ} (hn : LowBand n) :
    FRAME_A_hyp (BstLean.Part289.statedDesign2 n) (weightedFrameCap / n) (lowFrameRetained n) := by
  apply frameA_of_WF_tests (by have := hn.1; omega)
  intro c hc v hv
  exact (weightedFrameBand hn c hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2 v hv).le

end BstLean.BlueprintLow
