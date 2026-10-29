import BstLean.Part168End

/-!
# Part 168: the plane moment `X_ℓ`, the numerics of Lemma LJ, and the end theorem

No proof is left open; no `native_decide` or `axiom` is used.

* `Part168Pol`: the polar step for the rows of `A₁` in the frame (`polar_core`).
* `Part168Num`: the numerics `K2XY ≤ 4.7` for every `n ≥ 80 000` (`K2_num`).
* `Part168XM`: measurability of the `Xmom` integrand; plane bound; admissibility of `YF`, `YS`.
* `Part168XK`: the coefficients in the frame (`kap_inv`, `kap_le`, `inner_frame`).
* `Part168X`: `Xmom_le`, `X_hyp_proved`.
* `Part168End`: `LJ_proved` (`JM_hyp n 4.7`, no hypothesis) and `classifier_paper_LG80k`.
-/

#print axioms BstLean.Part168.pi_prod_le
#print axioms BstLean.Part168.rows_pol_le
#print axioms BstLean.Part168.polar_core
#print axioms BstLean.Part168.measurable_Xint
#print axioms BstLean.Part168.normSq_planeP_le
#print axioms BstLean.Part168.kap_inv
#print axioms BstLean.Part168.kap_le
#print axioms BstLean.Part168.inner_frame
#print axioms BstLean.Part168.Xframe_le
#print axioms BstLean.Part168.Xmom_le
#print axioms BstLean.Part168.X_hyp_proved
#print axioms BstLean.Part168.rpow_m_le
#print axioms BstLean.Part168.X2_num
#print axioms BstLean.Part168.Y_num'
#print axioms BstLean.Part168.Cg_le
#print axioms BstLean.Part168.Z_num
#print axioms BstLean.Part168.K2_num
#print axioms BstLean.Part168.LJ_proved
#print axioms BstLean.Part168.classifier_paper_LG80k
