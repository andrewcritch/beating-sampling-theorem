import BstLean.Part192Interfaces

/-! Charge repricing preserves the scalar data except for the retained charge
and the supplied total budget. The increased ledger is an explicit premise. -/

namespace BstLean.Part265
open BstLean.Part192

/-- The dimension and World parameters identify the scalar row. -/
noncomputable def agentRepriced (_n : ℕ) (_w : WorldParameters)
    (a : AgentParameters) (c : ℝ) : AgentParameters :=
  { a with charge := max a.charge c }

lemma agentRepriced_charge (n : ℕ) (w : WorldParameters)
    (a : AgentParameters) (c : ℝ) :
    (agentRepriced n w a c).charge = max a.charge c := rfl

lemma agentRepriced_charge_ge (n : ℕ) (w : WorldParameters)
    (a : AgentParameters) (c : ℝ) :
    c ≤ (agentRepriced n w a c).charge := le_max_right _ _

/-- The Part262 base price plus the selected covariance and moment price. -/
noncomputable def chargeFloor : ℝ := 1499145 / 10 ^ 9 + 3 / 10000

lemma chargeFloor_eq : chargeFloor = 1799145 / 10 ^ 9 := by
  norm_num [chargeFloor]

lemma chargeFloor_nonneg : 0 ≤ chargeFloor := by
  norm_num [chargeFloor]

/-- An increased charge requires a checked ledger. The new budget can differ
from the original budget, but it remains at most one percent. -/
noncomputable def scalarRepriced {n : ℕ} {w : WorldParameters}
    {a : AgentParameters} (C : ScalarCertificate n w a) (c B : ℝ)
    (hledger : w.hiddenCharge + w.moment / C.worldRadius ^ 2 +
      max C.retainedCharge c + C.samplingCharge + C.upperTail + C.lowerTail ≤ B)
    (hbudget : B ≤ 1 / 100) :
    ScalarCertificate n w (agentRepriced n w a c) :=
  { C with
    retainedCharge := max C.retainedCharge c
    retainedCharge_nonneg := le_trans C.retainedCharge_nonneg (le_max_left _ _)
    totalBudget := B
    ledger := hledger
    budget := hbudget }

theorem scalarCertificate_exists {n : ℕ} {w : WorldParameters}
    {a : AgentParameters} (C : ScalarCertificate n w a) (c : ℝ)
    (hledger : w.hiddenCharge + w.moment / C.worldRadius ^ 2 +
      max C.retainedCharge c + C.samplingCharge + C.upperTail + C.lowerTail ≤
        C.totalBudget) :
    Nonempty (ScalarCertificate n w (agentRepriced n w a c)) :=
  ⟨scalarRepriced C c C.totalBudget hledger C.budget⟩

lemma scalarRepriced_retainedCharge {n : ℕ} {w : WorldParameters}
    {a : AgentParameters} (C : ScalarCertificate n w a) (c B : ℝ)
    (hledger : w.hiddenCharge + w.moment / C.worldRadius ^ 2 +
      max C.retainedCharge c + C.samplingCharge + C.upperTail + C.lowerTail ≤ B)
    (hbudget : B ≤ 1 / 100) :
    (scalarRepriced C c B hledger hbudget).retainedCharge =
      max C.retainedCharge c := rfl

/-- The Agent-to-retained payment comparison survives repricing. -/
lemma scalarRepriced_payment {n : ℕ} {w : WorldParameters}
    {a : AgentParameters} (C : ScalarCertificate n w a) (c B : ℝ)
    (hledger : w.hiddenCharge + w.moment / C.worldRadius ^ 2 +
      max C.retainedCharge c + C.samplingCharge + C.upperTail + C.lowerTail ≤ B)
    (hbudget : B ≤ 1 / 100) (hcharge : a.charge ≤ C.retainedCharge) :
    (agentRepriced n w a c).charge ≤
      (scalarRepriced C c B hledger hbudget).retainedCharge :=
  max_le_max hcharge le_rfl

end BstLean.Part265
