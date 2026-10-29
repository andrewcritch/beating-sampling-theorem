import BstLean.Part130Extra
import BstLean.Part130TwoPoint
import BstLean.Part130Cost

/-!
# Part 130: random ReLU MLPs with two hidden layers, definitions and first exact identities

Role: `delegations/statements/p130-spec.md`; report: `delegations/answers/p130-spec-opus.md`.
This file imports every module of Part 130.

* `Part130Defs`: `relu`, `mlp2`, `MlpParam`, `mlpEval`, `gaussMat`, `mlpGauss`, `sphPt`, `muWn`,
  `phiN`, `Bn`, `sdn`, `mA`, `mF`, `mW`, `mlpTriple`.
* `Part130Layer`: one Gaussian matrix under linear maps.
* `Part130Moments`: the moments of one layer.
* `Part130Second`: `mlp_second_moment`, `mlp_fourth_moment`.
* `Part130Sym`: invariance under orthogonal maps; the conditional Gaussian structure.
* `Part130Mean`: `Bn_mean_zero`, `phiN_second_moment`.
* `Part130Kappa`, `Part130Row`: the function `κ` and the row formula.
* `Part130TwoPoint`: `layer_dot_relu`, `mlp_two_point_inner`.
* `Part130Extra`: the entries of `gaussMat`; the widths of the Focus.
* `Part130Cost`: the cost model with `max(0, ·)` as one operation.
-/
