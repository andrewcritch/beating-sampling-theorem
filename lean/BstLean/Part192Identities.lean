import BstLean.Part192Interfaces

/-! Part 192: regression and exact program identities.
The residual matrices retain entry variances 2/mW and 2/mA.
These identities also cover the existing zero-centre convention. -/

namespace BstLean.Part192
open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part169

theorem regression_distribution {n : ℕ} (P : Program n) :
    (mlpTriple 2 n).map (fun θ => (ret P.design.toCentres θ, θ)) =
      ((noiseC n).prod ((resW n).prod (resA n))).map
        (fun x => (retVal P.design.toCentres x.1,
          rebuild P.design.toCentres (retVal P.design.toCentres x.1) x.2)) :=
  triple_disint P.design.toCentres

theorem agent_regression {n : ℕ} (P : Program n) (c : Ret n) (ω : ResA n)
    (ξ : Fin n → ℝ) :
    mlpEval (agentOf P.design.toCentres c ω)
      (sphPt (c.1.2 + P.design.tau0 c • ξ)) =
        lam (P.design.bA c.1 c.2.1.1) (hStand P.design c ξ) • c.2.1.2 +
          ω.mulVec (res (P.design.bA c.1 c.2.1.1) (hStand P.design c ξ)) :=
  mlpEval_netOf (P.design.bA c.1) c.2.1.1 c.2.1.2 ω _

theorem world_regression {n : ℕ} (P : Program n) (c : Ret n)
    (ω : ResW n × ResA n) (u : Fin (2 * n) → ℝ) :
    mlpEval (rebuild P.design.toCentres c ω).1 u =
      lam (P.design.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 u) • c.1.2 +
        ω.1.mulVec (res (P.design.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 u)) :=
  mlpEval_netOf P.design.bW c.1.1 c.1.2 ω.1 u

theorem residual_scale {n : ℕ} (P : Program n) (c : Ret n) (ξ : Fin n → ℝ) :
    sig (2 / (mA n : ℝ)) (P.design.bA c.1 c.2.1.1) (hStand P.design c ξ) ^ 2 =
      2 / (mA n : ℝ) * normSq
        (res (P.design.bA c.1 c.2.1.1) (hStand P.design c ξ)) := by
  unfold sig
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (normSq_nonneg _)]

theorem mixture_identity {n : ℕ} (P : Program n) (c : Ret n) (s : ℝ) :
    P.design.mix c s =
      (fPass c (nodeS c (gIdx c s)) / √(normSq (bR c) / (n : ℝ)),
        2 / (n : ℝ) * max (1 / 5) (wPass c (nodeS c (gIdx c s)) -
          fPass c (nodeS c (gIdx c s)) ^ 2)) := by
  rw [P.design_eq]
  exact mixP_eq c s

theorem mean_residual_identity {n : ℕ} (P : Program n) (t : ℝ) (c : Ret n) :
    ∫ ω, PStand P.design t c ω ∂resA n = QStand P.design t c :=
  mean_PStand P.design t c

end BstLean.Part192
#print axioms BstLean.Part192.regression_distribution
#print axioms BstLean.Part192.agent_regression
#print axioms BstLean.Part192.world_regression
#print axioms BstLean.Part192.residual_scale
#print axioms BstLean.Part192.mixture_identity
#print axioms BstLean.Part192.mean_residual_identity
