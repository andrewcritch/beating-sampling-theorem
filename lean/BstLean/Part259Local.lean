import BstLean.Part255Covariance
import BstLean.Part253Bridge

namespace BstLean.Part259
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part188
open BstLean.Part169 (paperDesignP)
open BstLean.Part249
open BstLean.Part182 (Dq)

open BstLean.Part253 (centreGroup)

def LocalCovarianceOn {n : ℕ} (E : Set (AgFam n)) (cells : Fin 60 → Set ℝ)
    (caps : Fin 60 → ℝ) : Prop :=
  ∀ (i : Fin 60) (θ : ℝ), 10 ≤ i.val ∧ i.val ≤ 52 → θ ∈ cells i →
    ∀ (c : Ret n),
    BstLean.Part150.thetaC c.1.2 ((BstLean.Part169.paperDesignP n).tau0 c) = θ →
    0 < (BstLean.Part169.paperDesignP n).tau0 c →
    c ∈ agentEv (BstLean.Part169.paperDesignP n) E →
    BstLean.Part153.Xi4 c.2.1.1.1 c.2.1.1.2 c.1.2
      ((BstLean.Part169.paperDesignP n).tau0 c) ≤ (13 / 10) * (2 / (n : ℝ)) / n →
    ∀ v : Fin (mA n) → ℝ,
    Dq c.2.1.1.1 c.2.1.1.2 c.1.2 ((BstLean.Part169.paperDesignP n).tau0 c) v ≤
      caps i * (2 / (n : ℝ)) / n * normSq v

noncomputable def covarianceGood {n : ℕ} (event : Set (AgFam n)) : Set (Ret n) :=
  agentEv (paperDesignP n) event ∩
    agentEv (paperDesignP n) (BstLean.Part245.MomentM12 n)

theorem covarianceGood_measurable {n : ℕ} {event : Set (AgFam n)}
    (hevent : MeasurableSet event) : MeasurableSet (covarianceGood event) :=
  (measurableSet_agentEv _ hevent).inter
    (measurableSet_agentEv _ (BstLean.Part245.measurableSet_MomentM12 _))

theorem covarianceGood_charge {n : ℕ} (hn : 11883 ≤ n) {event : Set (AgFam n)}
    (hpayment : (retDist (paperCentres n)).real
      (agentEv (paperDesignP n) event)ᶜ ≤ (1/4000 : ℝ)) :
    (retDist (paperCentres n)).real (covarianceGood event)ᶜ ≤ (3/10000 : ℝ) := by
  unfold covarianceGood
  rw [compl_inter]
  exact (measureReal_union_le _ _).trans
    ((add_le_add hpayment (BstLean.Part245.moment_M12_ret hn
      (paperDesignP n) (paperDesign_tauWorld _ _ _ _))).trans (by norm_num))

structure LocalFrameInputs (n : ℕ) (event : Set (AgFam n)) (cell : Fin 60 → Set ℝ) (capTable : Fin 60 → ℝ)
    (c : Ret n) (cf : ℝ) where
  cov_le : LocalCovarianceOn event cell capTable
  index : Fin 60
  index_needed : 10 ≤ index.val ∧ index.val ≤ 52
  member : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ cell index
  cutoff : Fin 60 → ℝ
  centreAllowance : Fin 10 → ℝ
  massAllowance : Fin 60 → ℝ
  M : ℝ
  H : ℝ
  xiP : ℝ
  E : ℝ
  u : ℝ
  order : ℕ
  order_pos : 1 ≤ order
  order_le : order ≤ 12
  scale_pos : 0 < (paperDesignP n).tau0 c
  centre_pos : 0 < normSq ((paperDesignP n).bA c.1 c.2.1.1)
  centre_nonneg : ∀ j, 0 ≤ (paperDesignP n).bA c.1 c.2.1.1 j
  interfaces : WFInterfaces (paperDesignP n) c M H xiP
  centre_energy : centreEnergy (paperDesignP n) c ≤ E
  u_pos : 0 < u
  u_lt : u < 1
  cutoff_pos : 0 < cutoff index
  cutoff_lt : cutoff index < (1 - u) ^ 2
  gap_pos : 0 < √((1 - u) ^ 2 - cutoff index) - (√E + √(xiP / n))
  covariance_nonneg : 0 ≤ capTable index
  full_centre : CENTRE_at (paperDesignP n) c (centreAllowance (centreGroup index))
  mass_scalar : BstLean.Part222.massBoundOrder n order M H xiP E u (cutoff index) ≤
    massAllowance index
  frame_scalar : (capTable index + centreAllowance (centreGroup index)) / cutoff index +
    massAllowance index ≤ cf

theorem covariance_from_contract {n : ℕ} (hn : 6 ≤ n) {event : Set (AgFam n)} {cell : Fin 60 → Set ℝ} {capTable : Fin 60 → ℝ}
    (C : LocalCovarianceOn event cell capTable) {c : Ret n} {i : Fin 60}
    (hneeded : 10 ≤ i.val ∧ i.val ≤ 52)
    (hτ : 0 < (paperDesignP n).tau0 c)
    (hi : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ cell i)
    (hc : c ∈ covarianceGood event) :
    COV_at (paperDesignP n) c (capTable i) := by
  exact BstLean.Part199.cov_of_scalar hn (paperDesignP n) c hτ le_rfl
    (C i _ hneeded hi c rfl hτ hc.1 (hc.2 hτ))

theorem frame_from_inputs {n : ℕ} (hn : 50 ≤ n) {event : Set (AgFam n)} {cell : Fin 60 → Set ℝ} {capTable : Fin 60 → ℝ}
    {c : Ret n} {cf : ℝ} (F : LocalFrameInputs n event cell capTable c cf)
    (hc : c ∈ covarianceGood event) :
    ∀ v : Fin (mA n) → ℝ,
      ∫ ξ, (∑ j, BstLean.Part134.eDir ((paperDesignP n).bA c.1 c.2.1.1)
        (hStand (paperDesignP n) c ξ) j * v j) ^ 2 ∂BstLean.Part29.stdGauss (Fin n) ≤
      cf / n * ∑ j, v j ^ 2 := by
  exact BstLean.Part222.freeAllowance_frame_order hn F.order_pos F.order_le
    (paperDesignP n) c F.scale_pos F.centre_pos F.centre_nonneg F.interfaces
    F.centre_energy F.u_pos F.u_lt F.cutoff_pos F.cutoff_lt F.gap_pos F.covariance_nonneg
    (covariance_from_contract (by omega) F.cov_le F.index_needed F.scale_pos F.member hc) F.full_centre
    F.mass_scalar F.frame_scalar

end BstLean.Part259
