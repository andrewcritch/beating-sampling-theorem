import BstLean.Part249Bridge
import BstLean.Part222AllowanceOrders

/-! Cell-local covariance inputs. The covariance conclusion is an explicit
contract; this module does not infer it from a uniform scalar certificate. -/
namespace BstLean.Part253
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part188
open BstLean.Part169 (paperDesignP)
open BstLean.Part249

/-- A group consists of six consecutive cells. -/
def centreGroup (i : Fin 60) : Fin 10 := ⟨i.val / 6, by omega⟩

/-- This is the Part254 contract in the normalization used by Part238.
The covariance event is exactly Option B. The moment premise has its existing
separate payment. There is no union over the deterministic cells. -/
def LocalCovariance (cell : Fin 60 → Set ℝ) (capTable : Fin 60 → ℝ) : Prop :=
  ∀ (i : Fin 60) (θ : ℝ), 10 ≤ i.val ∧ i.val ≤ 52 → θ ∈ cell i → ∀ (c : Ret 12225),
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) = θ →
    0 < (paperDesignP 12225).tau0 c →
    c ∈ agentEv (paperDesignP 12225) (optionBSharp 12225) →
    BstLean.Part153.Xi4 c.2.1.1.1 c.2.1.1.2 c.1.2 ((paperDesignP 12225).tau0 c) ≤
      (13 / 10) * (2 / (12225 : ℝ)) / 12225 →
    ∀ v : Fin (mA 12225) → ℝ,
      BstLean.Part182.Dq c.2.1.1.1 c.2.1.1.2 c.1.2 ((paperDesignP 12225).tau0 c) v ≤
        capTable i * (2 / (12225 : ℝ)) / 12225 * normSq v

/-- All bounds refer to the selected retained value. Per-cell cutoffs and
mass allowances are independent of the six-cell centre allowances. -/
structure LocalFrameInputs (cell : Fin 60 → Set ℝ) (capTable : Fin 60 → ℝ)
    (c : Ret 12225) (cf : ℝ) where
  cov_le : LocalCovariance cell capTable
  index : Fin 60
  index_needed : 10 ≤ index.val ∧ index.val ≤ 52
  member : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ cell index
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
  scale_pos : 0 < (paperDesignP 12225).tau0 c
  centre_pos : 0 < normSq ((paperDesignP 12225).bA c.1 c.2.1.1)
  centre_nonneg : ∀ j, 0 ≤ (paperDesignP 12225).bA c.1 c.2.1.1 j
  interfaces : WFInterfaces (paperDesignP 12225) c M H xiP
  centre_energy : centreEnergy (paperDesignP 12225) c ≤ E
  u_pos : 0 < u
  u_lt : u < 1
  cutoff_pos : 0 < cutoff index
  cutoff_lt : cutoff index < (1 - u) ^ 2
  gap_pos : 0 < √((1 - u) ^ 2 - cutoff index) - (√E + √(xiP / 12225))
  covariance_nonneg : 0 ≤ capTable index
  full_centre : CENTRE_at (paperDesignP 12225) c (centreAllowance (centreGroup index))
  mass_scalar : BstLean.Part222.massBoundOrder 12225 order M H xiP E u (cutoff index) ≤
    massAllowance index
  frame_scalar : (capTable index + centreAllowance (centreGroup index)) / cutoff index +
    massAllowance index ≤ cf

theorem covariance_from_contract {cell : Fin 60 → Set ℝ} {capTable : Fin 60 → ℝ}
    (C : LocalCovariance cell capTable) {c : Ret 12225} {i : Fin 60}
    (hneeded : 10 ≤ i.val ∧ i.val ≤ 52)
    (hτ : 0 < (paperDesignP 12225).tau0 c)
    (hi : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ cell i)
    (hc : c ∈ optionBGood (paperDesignP 12225)) :
    COV_at (paperDesignP 12225) c (capTable i) := by
  exact BstLean.Part199.cov_of_scalar (by norm_num) (paperDesignP 12225) c hτ le_rfl
    (C i _ hneeded hi c rfl hτ hc.1 (hc.2 hτ))

theorem frame_from_inputs {cell : Fin 60 → Set ℝ} {capTable : Fin 60 → ℝ}
    {c : Ret 12225} {cf : ℝ} (F : LocalFrameInputs cell capTable c cf)
    (hc : c ∈ optionBGood (paperDesignP 12225)) :
    ∀ v : Fin (mA 12225) → ℝ,
      ∫ ξ, (∑ j, BstLean.Part134.eDir ((paperDesignP 12225).bA c.1 c.2.1.1)
        (hStand (paperDesignP 12225) c ξ) j * v j) ^ 2 ∂BstLean.Part29.stdGauss (Fin 12225) ≤
      cf / 12225 * ∑ j, v j ^ 2 := by
  exact BstLean.Part222.freeAllowance_frame_order (by norm_num) F.order_pos F.order_le
    (paperDesignP 12225) c F.scale_pos F.centre_pos F.centre_nonneg F.interfaces
    F.centre_energy F.u_pos F.u_lt F.cutoff_pos F.cutoff_lt F.gap_pos F.covariance_nonneg
    (covariance_from_contract F.cov_le F.index_needed F.scale_pos F.member hc) F.full_centre
    F.mass_scalar F.frame_scalar

end BstLean.Part253
