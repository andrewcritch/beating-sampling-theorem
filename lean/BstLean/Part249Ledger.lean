import BstLean.Part249Endpoint
import BstLean.Part246Charge

/-! Exact ledger arithmetic and exceptional-factor sensitivity.
The proposed event allowances remain separate from proofs of event probabilities. -/
namespace BstLean.Part249
open BstLean.Part243

noncomputable def frozenLedger : ℝ :=
  proposedHiddenCharge + rowMoment / rowRadius ^ 2 + proposedRetainedCharge +
    rowSamplingAllowance + rowPositiveBase ^ 8 + rowNegativeBase ^ 8

noncomputable def frozenMargin : ℝ :=
  546165083892896458155331973133003703086806247777329886204908623193185811793734595793613475687738296423 /
    167846715481000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

theorem frozen_margin_exact : (1 / 100 : ℝ) - frozenLedger = frozenMargin := by
  norm_num [frozenLedger, frozenMargin, proposedHiddenCharge, proposedRetainedCharge,
    rowMoment, rowRadius, rowSamplingAllowance, rowPositiveBase, rowNegativeBase]

theorem frozen_margin_bounds :
    (3253951573 / 10 ^ 15 : ℝ) < frozenMargin ∧
      frozenMargin < (3253951574 / 10 ^ 15 : ℝ) := by
  norm_num [frozenMargin]

theorem frozen_ledger_closes : frozenLedger < (1 / 100 : ℝ) := by
  have := frozen_margin_bounds.1
  linarith [frozen_margin_exact]

/-- The exceptional factor is multiplied by the fourth-moment coefficient.
It is not an event payment. This identity keeps all other covariance terms fixed. -/
theorem exceptional_increment (base M : ℝ) :
    (base + M * (1032 / 10 ^ 6)) - (base + M * (1028 / 10 ^ 6)) =
      M / 250000 := by ring

theorem exceptional_frame_increment {base M xi d beta frame : ℝ}
    (hM : M ≤ 13 / 10) (hd : (1 / 5 : ℝ) ≤ d)
    (hframe : (base + M * (1028 / 10 ^ 6) + xi) / d + beta ≤ frame) :
    (base + M * (1032 / 10 ^ 6) + xi) / d + beta ≤ frame + 26 / 10 ^ 6 := by
  have hd0 : 0 < d := by linarith
  have hi : M / 250000 / d ≤ (26 / 10 ^ 6 : ℝ) := by
    rw [div_le_iff₀ hd0]
    linarith
  have he : (base + M * (1032 / 10 ^ 6) + xi) / d + beta =
      ((base + M * (1028 / 10 ^ 6) + xi) / d + beta) + M / 250000 / d := by ring
  rw [he]
  linarith

theorem optionB_frame_allowance :
    rowAgentFrame + (26 / 10 ^ 6 : ℝ) = optionBAgentFrame := by
  norm_num [rowAgentFrame, optionBAgentFrame]

theorem optionB_covariance_enclosure :
    (3388 / 10000 : ℝ) < BstLean.Part246.ratCov (67 / 100) (60 / 100) (13 / 10) ∧
    BstLean.Part246.ratCov (67 / 100) (60 / 100) (13 / 10) < (339 / 1000 : ℝ) := by
  norm_num [BstLean.Part246.ratCov]

noncomputable def optionBLedger : ℝ :=
  proposedHiddenCharge + rowMoment / rowRadius ^ 2 + proposedRetainedCharge +
    rowSamplingAllowance + optionBPositiveBase ^ 8 + optionBNegativeBase ^ 8

noncomputable def optionBFailureAllowance : ℝ := 99970869 / 10 ^ 10

theorem optionB_ledger_exact : optionBLedger =
    (6554602325348698533801656310083560230167712420802099280827606217027731966397654194412235235716073534457 /
      655651232347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  norm_num [optionBLedger, proposedHiddenCharge, proposedRetainedCharge, rowMoment,
    rowRadius, rowSamplingAllowance, optionBPositiveBase, optionBNegativeBase]

theorem optionB_ledger_bounds :
    (9997086868 / 10 ^ 12 : ℝ) < optionBLedger ∧
      optionBLedger < (9997086869 / 10 ^ 12 : ℝ) := by
  norm_num [optionBLedger, proposedHiddenCharge, proposedRetainedCharge, rowMoment,
    rowRadius, rowSamplingAllowance, optionBPositiveBase, optionBNegativeBase]

theorem optionB_scalar_ledger {hidden retained : ℝ}
    (h : hidden + retained ≤ rowEventAllowance) :
    hidden + rowMoment / rowRadius ^ 2 + retained + rowSamplingAllowance +
      optionBPositiveBase ^ 8 + optionBNegativeBase ^ 8 ≤ optionBFailureAllowance := by
  have hn : rowMoment / rowRadius ^ 2 + rowSamplingAllowance +
      optionBPositiveBase ^ 8 + optionBNegativeBase ^ 8 ≤
      optionBFailureAllowance - rowEventAllowance := by
    norm_num [rowMoment, rowRadius, optionBPositiveBase, optionBNegativeBase,
      rowSamplingAllowance, optionBFailureAllowance, rowEventAllowance]
  linarith

theorem optionB_budget : optionBFailureAllowance < (1 / 100 : ℝ) := by
  norm_num [optionBFailureAllowance]

/-- Pay the moment event from the existing centre/energy/direction allowance.
The residual allowance is still an input to the network bridge. -/
noncomputable def baseChargeAllowance : ℝ := proposedRetainedCharge - 3 / 10000

theorem base_charge_allocation :
    baseChargeAllowance =
      (495214276589 / 10 ^ 15 - 5 / 100000) + 106144212354 / 10 ^ 15 +
        1052754646384 / 10 ^ 15 + 6144212354 / 10 ^ 15 := by
  norm_num [baseChargeAllowance, proposedRetainedCharge]

theorem base_charge_restored :
    baseChargeAllowance + (3 / 10000 : ℝ) = proposedRetainedCharge := by
  unfold baseChargeAllowance
  ring

end BstLean.Part249
