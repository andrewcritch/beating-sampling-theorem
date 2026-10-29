import BstLean.Part56Defs
import BstLean.Part56RKGErr_Integrability
import BstLean.Part56RKGErr_Kernel
import BstLean.Part56RKGErr_Cauchy
import BstLean.Part56RKGErr_Average

/-!
# Part 56, wave 1: Theorem RK-G, error part

Specification: `delegations/answers/p56-spec-opus.md` §3 (`Part56RKGErr`).
This file reuses the finished orthogonality and floor helpers, as authorized in the resumed task.
Do not use `native_decide` or `axiom` anywhere. Do not edit the statement below.

Proof route (`omRK-opus-prover.md` §4, step 1): `E(B−g)² = E_U Var(B|U)`,
`Var(B|U) = E_{x,y} Cov(F(x), F(y) | U)`; given `U`, the coordinate pairs `(R_i(x), R_i(y))` are
independent with correlation `ρ_R(x,y)`; Lemma MC gives `|Cov| ≤ |ρ_R| S_U(x) S_U(y)`; Cauchy–Schwarz over
`(x, y) ∼ μ⊗μ` and independence of `x, y` give `Var(B|U) ≤ δ E_x S_U(x)²`. Take `E_U`. If `τ(x) = 0`
then `F(x)` is `U`-measurable and the pair contributes `0` (consistent with `rhoR = 0`).
-/

namespace BstLean.Part56

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono frob Tens TSymm Pn NN baseline heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (LemmaR53 GaussPolar53)
open BstLean.Part48 (SBLevel)

/-- **Theorem RK-G, error part**, from Lemma MC and the Gaussian split. -/
theorem propRKGErr56_of (d k : ℕ) (hMC : LemmaMC56) (hS : PropSplit56 d) : PropRKGErr56 d k := by
  by_cases hk : k = 0
  · subst k
    exact rkg56_degree_zero d
  intro n μ hμ v hv f0 T hT
  refine ⟨rkg56_error_integrable (d := d) hμ k f0 T (BstLean.Part53.sg n d) v, ?_⟩
  let ν := stdGauss (CoefIdxD n d)
  let F := fun Z : CoefIdxD n d → ℝ =>
    (BofQ μ k f0 T (BstLean.Part53.sg n d • Z) -
      gLineH μ k f0 T v (BstLean.Part53.sg n d • Z)) ^ 2
  have hF : Integrable F ν := rkg56_error_integrable (d := d) hμ k f0 T
    (BstLean.Part53.sg n d) v
  have hmp := Orth.resampling_measurePreserving hS v hv
  have hr : Integrable (fun p : (CoefIdxD n d → ℝ) × (CoefIdxD n d → ℝ) =>
      F (FloorAux.splitField v p.1 p.2)) (ν.prod ν) :=
    hmp.integrable_comp_of_integrable hF
  have hheat (Z W : CoefIdxD n d → ℝ) :
      gLineH μ k f0 T v (BstLean.Part53.sg n d • FloorAux.splitField v Z W) =
        gLineH μ k f0 T v (BstLean.Part53.sg n d • Z) :=
    Orth.heat_resampling μ k f0 T v hv (BstLean.Part53.sg n d) Z W
  have hpoint : ∀ Z : CoefIdxD n d → ℝ,
      (∫ W, F (FloorAux.splitField v Z W) ∂ν) ≤
        Real.sqrt (deltaSq μ d v) * Sfl μ d k f0 T v (BstLean.Part53.sg n d • Z) := by
    intro Z
    simp only [F, hheat]
    exact RKGErr.conditional_error_bound hMC hμ k f0 T hT v hv Z
  have hle := integral_mono hr.integral_prod_left
    ((RKGErr.Sfl_integrable hS hμ k f0 T v hv).const_mul (Real.sqrt (deltaSq μ d v))) hpoint
  have heq : (∫ Z, ∫ W, F (FloorAux.splitField v Z W) ∂ν ∂ν) = ∫ Z, F Z ∂ν := by
    rw [← integral_prod _ hr]
    dsimp only [ν]
    conv_rhs => rw [← hmp.map_eq]
    exact (integral_map hmp.measurable.aemeasurable
      (hmp.map_eq.symm ▸ hF.aestronglyMeasurable)).symm
  rw [heq, integral_const_mul] at hle
  exact hle

end BstLean.Part56

