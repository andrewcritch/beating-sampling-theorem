import BstLean.Part156Out
import BstLean.Part156Comp
import BstLean.Part156End
import BstLean.Part156Master
import BstLean.Part156Num
import BstLean.Part156Samp
import BstLean.Part156Final
import BstLean.Part156LB

/-!
# Part 156: the Lean skeleton of the classifier theorem (a CONDITIONAL theorem)

This module imports every file of Part 156.

The headline `BstLean.Part156.classifier_conditional_16384_success` is CONDITIONAL. It is NOT a
Lean proof of the classifier theorem: the hypotheses (GP-W), (GP-A), (REPL), the replacement root
and the three event charges are ASSUMED, on abstract probability spaces. No ReLU network occurs in
Part 156.

* `Part156Out`: the output rule (deterministic).
* `Part156Comp`: the composition bound (CP-R) from (GP-W), (GP-A), (REPL).
* `Part156End`: the two endpoint tails from (CP-R), with the endpoint reduction.
* `Part156Master`: the master inequality.
* `Part156Num`: the numeric ledger at `n = 16 384`.
* `Part156Samp`: the sampling step in root form (unconditional).
* `Part156Final`: the assembly.
* `Part156LB`: the lower bound for rules that see only Boolean samples (unconditional).
-/
