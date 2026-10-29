import BstLean.Part139Tools
import BstLean.Part139Err
import BstLean.Part139Spread
import BstLean.Part139Final
import BstLean.Part139Scale
import BstLean.Part139Sample
import BstLean.Part139Explicit
import BstLean.Part139TwoStage
import BstLean.Part139Two

/-!
# Part 139: the mean over the cheap stand-in is within `sd/2` of `B` (joint probability)

Role: `delegations/statements/p139-spec.md`. Report: `delegations/answers/p139-spec-opus.md`.

Index (namespace `BstLean.Part139`; `S = 4/n`, `Q = κ^{∘6}(0)`, widths of the Focus, `r = 2`):

* `Part139Tools`: `covV_trace`, `covV_frob_le` (covariance of a bounded vector function),
  `qform_sq_integral` (second moment of a Gaussian quadratic form), `kappa6_zero_le''`.
* `Part139Err` (item 1): `gCheap`, `errFixed139`, `errVec139_lint`, `errVec139`, `errVec139_num`,
  `errTail139`.
* `Part139Spread` (item 2): `spread_L2`, `spreadLow_general`, `spreadLow139`, `spreadLow139_num`.
* `Part139Final` (item 3): `okSet`, `standInSucceeds139_formula`, `standInSucceeds139`.
* `Part139Scale`: `eP139_scale`, `eV_scale`, `vSpread_scale`, `standInSucceeds139_rate`,
  `standInSucceeds139_frontier`, `standInSucceeds139_99`.
* `Part139Sample` (item 4): `gSample`, `iid_mean_sq`, `errSample139_lint`, `sampleSucceeds139`.
* `Part139Explicit`: `scale139`, `standInExplicit139`, `standInExplicit139_half`,
  `standInExplicit139_rate`, `sampleExplicit139`.
* `Part139TwoStage`: `twoStage139`, `optA139`, `optA139_explicit`, `optA139_explicit_frontier`.
* `Part139Two` (item 4, the scalar from one input): `errFixedGen`, `cheapFixed2`, `gTwo`,
  `errTwo139_lint`, `standInTwo139_rate`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

open BstLean.Part139

#print axioms covV_trace
#print axioms covV_frob_le
#print axioms qform_sq_integral
#print axioms kappa6_zero_le
#print axioms kappa6_zero_le''
#print axioms measurable_gCheap
#print axioms lint_phi_sq
#print axioms errFixed139
#print axioms errVec139_lint
#print axioms errVec139
#print axioms errVec139_num
#print axioms errTail139
#print axioms gaussRow_qform_sq
#print axioms tr_eq
#print axioms frob_le
#print axioms cond_sq
#print axioms spread_L2
#print axioms lawR_drop
#print axioms spreadLow_general
#print axioms spreadLow139
#print axioms vSpread_le
#print axioms spreadLow139_num
#print axioms bad_prob
#print axioms standInSucceeds139_formula
#print axioms standInSucceeds139
#print axioms eP139_scale
#print axioms eV_scale
#print axioms vSpread_scale
#print axioms standInSucceeds139_rate
#print axioms standInSucceeds139_frontier
#print axioms standInSucceeds139_99
#print axioms iid_mean_sq
#print axioms measurable_gSample
#print axioms errSample139_lint
#print axioms errSampleTail139
#print axioms sampleSucceeds139
#print axioms standInExplicit139
#print axioms standInExplicit139_half
#print axioms standInExplicit139_rate
#print axioms sampleExplicit139
#print axioms twoStage139
#print axioms optA139
#print axioms optA139_explicit
#print axioms optA139_explicit_frontier
#print axioms errFixedGen
#print axioms cheapFixed2
#print axioms measurable_gTwo
#print axioms errTwo139_lint
#print axioms badQ_prob
#print axioms standInTwo139_rate
