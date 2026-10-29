import BstLean.Part157Defs
import BstLean.Part157Reg
import BstLean.Part157Net
import BstLean.Part157Triple
import BstLean.Part157Prog
import BstLean.Part157Final
import BstLean.Part157Gp
import BstLean.Part157Repl
import BstLean.Part157Hell
import BstLean.Part157Paper
import BstLean.Part157BL
import BstLean.Part157Charges
import BstLean.Part157Mgf
import BstLean.Part157Bridge

/-!
# Part 157: the classifier theorem connected to the actual networks (a CONDITIONAL theorem)

This module imports every file of Part 157.

The headlines `BstLean.Part157.classifier_networks_conditional` (and its forms `…_frame`,
`…_hell`, `classifier_paper_conditional`) are statements about the three random ReLU MLPs of
`MM.md`. They are CONDITIONAL: the named hypotheses are NOT proved in Lean.

* `Part157Defs`: the classifier, the target `pTarget`, measurability (item 1).
* `Part157Reg`, `Part157Net`: the Gaussian regression as a product decomposition (item 2).
* `Part157Triple`: the three networks as retained data and residual matrices (item 3).
* `Part157Prog`: the design, the sampling program, the stand-in probability (items 3, 4).
* `Part157Final`: the named hypotheses and `classifier_networks_conditional` (item 3).
* `Part157Gp`: (GP-W), (GP-A) from one Gaussian inequality and two frame bounds.
* `Part157Repl`: the means over the residual matrices; hypotheses on the retained data only.
* `Part157Hell`: the World root replacement, proved for the Hellinger radius (item 4).
* `Part157Paper`: the centres, `τ₀` and the sampling step of the paper's program (item 4).
* `Part157BL`: the Gaussian inequality for orthonormal vectors (item 5).
* `Part157Charges`: the conditional theorem with free event charges.
* `Part157Mgf`: `GaussFrameMGF` from the inequality (GP); the final form of the theorem.
* `Part157Bridge`: the World frame bound and the hidden charge from Part 136 (exact mean centre).
-/
