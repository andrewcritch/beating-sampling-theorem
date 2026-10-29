import BstLean.Part133Final

/-!
# Part 133: the variance of `J`, and Theorem C

Role: `delegations/statements/p133-spec.md`. This module imports every file of Part 133.

Files: `Part133L2` (bounds of `L²` norms: triangle inequality, Fubini, Jensen), `Part133Four`
(fourth moments of Gaussian layers), `Part133Cos`, `Part133CosB` (the last matrix of `W` and the
normalization), `Part133Relu`, `Part133LinR`, `Part133ReluR` (one-layer and whole-network `L²`
links), `Part133World`, `Part133WorldR` (the World network and the inputs), `Part133Agent` (the
three kernels over `(A, A′, F)`), `Part133Top` (items 1, 2; `varJ_of_bounds`), `Part133Final`
(`kernels_general`, `varJ_general`, `vTot_bound`, **`varJ133`**, **`thmC133`**, **`sep133`**).
Do not use `sorry`, `native_decide` or `axiom`.
-/

open BstLean.Part133 in
#print axioms lin_sq_four
open BstLean.Part133 in
#print axioms lin_dot_var
open BstLean.Part133 in
#print axioms lin_ctp_var
open BstLean.Part133 in
#print axioms lin_cos_L2
open BstLean.Part133 in
#print axioms lin_cos_L2b
open BstLean.Part133 in
#print axioms relu_layer_L2
open BstLean.Part133 in
#print axioms lin_layer_L2r
open BstLean.Part133 in
#print axioms lin_layer_L2s
open BstLean.Part133 in
#print axioms mlp_nrm_mean_lower
open BstLean.Part133 in
#print axioms hid2_dot_L2o
open BstLean.Part133 in
#print axioms KF_L2o
open BstLean.Part133 in
#print axioms mlp_psi_L2r
open BstLean.Part133 in
#print axioms world_cos_L2g
open BstLean.Part133 in
#print axioms sphere_kk_L2r
open BstLean.Part133 in
#print axioms sphere_gW_L2
open BstLean.Part133 in
#print axioms kern_same_L2_of
open BstLean.Part133 in
#print axioms kern_cross_L2_of
open BstLean.Part133 in
#print axioms kern_diag_L2
open BstLean.Part133 in
#print axioms section_L2
open BstLean.Part133 in
#print axioms var_section_le
open BstLean.Part133 in
#print axioms J_L2
open BstLean.Part133 in
#print axioms varJ_of_bounds
open BstLean.Part133 in
#print axioms kernels_general
open BstLean.Part133 in
#print axioms var_P_le_var_k
open BstLean.Part133 in
#print axioms varJ_general
open BstLean.Part133 in
#print axioms vTot_bound
open BstLean.Part133 in
#print axioms varJ133
open BstLean.Part133 in
#print axioms thmC133
open BstLean.Part133 in
#print axioms sep133
