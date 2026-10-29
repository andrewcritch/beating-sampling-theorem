import BstLean.Part164Ev
import BstLean.Part164Bnd
import BstLean.Part164End
import BstLean.Part164Num

/-!
# Part 164: the top module

No proof is left open; no `native_decide` or `axiom` is used.

* `Part164Ev`: the norm event `EcA` of `c_A` (charge `2e^{−12}`) and the operator-norm event `Eop2`
  of `A₂` (charge `e^{−25/2}`).
* `Part164Bnd`: `0 < |c_A|² ≤ CAn n` and `∫∫σ⁸ ≤ (E0 n)⁸` on these events.
* `Part164End`: `classifier_paper_free23_cA8`, Part 163's `classifier_paper_free23_psi12e` with
  these three hypotheses removed; room `roomB ≥ 0.003042`.
* `Part164Num`: `CAn n ≤ 1.532` and `E0 n ≤ 4.06·√(2/n)` for `n ≥ 23 000`.
-/

open BstLean.Part164 in
#print axioms EcA_charge
open BstLean.Part164 in
#print axioms Eop2_charge
open BstLean.Part164 in
#print axioms cA_bounds
open BstLean.Part164 in
#print axioms sgA_le_E0
open BstLean.Part164 in
#print axioms sgA8_le
open BstLean.Part164 in
#print axioms hE8_of_good
open BstLean.Part164 in
#print axioms cA_of_good
open BstLean.Part164 in
#print axioms roomB_ge
open BstLean.Part164 in
#print axioms classifier_paper_free23_cA8
open BstLean.Part164 in
#print axioms CAn_le
open BstLean.Part164 in
#print axioms E0_le
open BstLean.Part164 in
#print axioms newEv_charge
