import BstLean.Part166Mk
import BstLean.Part166Th
import BstLean.Part166Fld
import BstLean.Part166Tr
import BstLean.Part166End

/-!
# Part 166: Proposition LG (the order-12 certificates) from Lemma LJ

No proof is left open; no `native_decide` or `axiom` is used.

* `Mk`: `markov12` (Young step + Markov + Tonelli), `integral_le_of_lintegral`.
* `Th`: `chi_mom` (`E|ξ|^{2k} ≤ (N + 2k)^k`), `theta_mom` (`E(1 − s²)^{64} ≤ 0.619^{64}`,
  `n ≥ 80 000`, window).
* `Fld`: the fields `fK`, `sK` and `psiK` at the Agent key; joint measurability.
* `Tr`: `psiA_sig_eq`, `psiA_lam_eq` (transfer to Part 162's `psiA`).
* `End`: `LJ_hyp`, `Scert`, `charge_one`, `cert_charge` (`12·10⁻⁵`), `cert_ret_charge`,
  `certs_of_goodD`, `roomD_ge`, **`classifier_paper_LJ80k`**.
-/

open BstLean.Part166 in
#print axioms markov12
open BstLean.Part166 in
#print axioms integral_le_of_lintegral
open BstLean.Part166 in
#print axioms theta_mom
open BstLean.Part166 in
#print axioms measurable_psiK_f
open BstLean.Part166 in
#print axioms psiA_lam_eq
open BstLean.Part166 in
#print axioms cert_charge
open BstLean.Part166 in
#print axioms cert_ret_charge
open BstLean.Part166 in
#print axioms certs_of_goodD
open BstLean.Part166 in
#print axioms classifier_paper_LJ80k
