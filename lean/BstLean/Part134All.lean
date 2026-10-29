import BstLean.Part134Split
import BstLean.Part134Mean
import BstLean.Part134Mehler
import BstLean.Part134Frame
import BstLean.Part134Core
import BstLean.Part134Var
import BstLean.Part134Lam

/-!
# Part 134: the stand-in theorem for the World network (paper Theorem S1), index

Role: `delegations/statements/p134-spec.md`. Report: `delegations/answers/p134-spec-opus.md`.

Setting. `W(u) = M₃ h(u)`, `h(u) = hid2 M₁ M₂ u = ReLU(M₂ ReLU(M₁ u))`, `M₃` an `n × m` Gaussian
matrix with entry variance `v = 2/m` (`gaussMat n m v`), `(M₁, M₂)` fixed, `b ∈ ℝ^m` fixed,
`c = M₃ b`, `λ(u) = lam b (h u)`, `r(u) = res b (h u)`, `σ(u) = sig v b (h u)`,
`P = projPerp b`, `ν_c = standIn μ h v b c`, `μ_M = muM μ h M` (`= muWn` for the World network).
The theorems hold for every probability measure `μ` on the inputs and every measurable `h`.

* Item 1 (a), `Part134Split`: decomposition `split_eq`, `s1_decomp`; independence `s1_split`
  (from `stdGauss_indep_of_orth`); disintegration `s1_disint`, `s1_glue`, `cDist_eq`;
  covariances `s1_resid_cov`, `s1_resid_gauss`, `s1_cross_cov`; centred `s1_resid_mean`
  (`Part134Lam`).
* Item 2 (b), `Part134Mean`: `s1_mean_pt`, `s1_mean_cond`, `s1_mean_test`, `s1_mean`,
  `s1_mean_explicit`, `s1_mean_mlp`.
* Tools: the sharp second-order Gebelein inequality `nt_le_sharp`, `mehler2_sharp`
  (`Part134Mehler`); the operator bound `frame_bound`, the tensor comparison `frame_tensor`,
  the pair distribution `pair_law` (`Part134Frame`).
* Item 3 (c): the core `var_core` (`Part134Core`); `s1_var`, `s1_var_total`, `s1_var_standIn`,
  `s1_mse`, `s1_var_mlp`, `s1_mse_mlp` (`Part134Var`); the explicit `λ₁`: `lamOne`,
  `lamOne_frame`, `lamOne_le`, `lamOne_le_one`, `s1_var_lamOne`, `s1_mse_lamOne`,
  `s1_var_mlp_lamOne`; other forms: `s1_var_family`, `s1_poincare` (`Part134Lam`).

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part134

#print axioms split_eq
#print axioms s1_decomp
#print axioms s1_split
#print axioms s1_disint
#print axioms s1_glue
#print axioms cDist_eq
#print axioms s1_resid_cov
#print axioms s1_resid_gauss
#print axioms s1_cross_cov
#print axioms s1_resid_mean
#print axioms s1_mean_pt
#print axioms s1_mean_cond
#print axioms s1_mean_test
#print axioms s1_mean
#print axioms s1_mean_explicit
#print axioms s1_mean_mlp
#print axioms nt_le_sharp
#print axioms mehler2_sharp
#print axioms var_core
#print axioms s1_var
#print axioms s1_var_total
#print axioms s1_var_standIn
#print axioms s1_mse
#print axioms s1_var_mlp
#print axioms s1_mse_mlp
#print axioms lamOne_frame
#print axioms lamOne_le
#print axioms lamOne_le_one
#print axioms lamOne_nonneg
#print axioms eDir_frame_one
#print axioms s1_var_lamOne
#print axioms s1_mse_lamOne
#print axioms s1_var_mlp_lamOne
#print axioms s1_var_family
#print axioms s1_poincare

end BstLean.Part134
