import BstLean.Part56Defs
import BstLean.Part56PropD_Assemble

/-!
# Part 56, wave 1: Prop D (`δ² ≤ C_D/(n − 1)` for every rank-one Bingham law)

Specification: `delegations/answers/p56-spec-opus.md` §3 (`Part56PropD`).
This file imports `Part56Defs`, existing Parts ≤ 55, and its own `Part56PropD_*` helper files.
It does not import another Part 56 wave-1 file. Do not use `native_decide` or `axiom` anywhere.
Do not edit the statement below.

Proof route (`omRK-opus-prover.md` §4, Prop D at `r = 1`): polar split `x = s v + ϱ w` under
`lawRK n t v` (`w` uniform on the sphere of `v^⊥`, independent of `s`); `Π_j φ_j(x) = Π_j ψ(x)` with
`ψ = Σ_{i≥1} ϱ^i Φ_{j,i}(s v, w)`; `τ(x) ≥ R_1(x,x) = ϱ²`; projection contracts the Frobenius norm of
`E ψ̂ψ̂ᵀ`; then the Key Lemma, conditionally on `(s, s')`. The bound is uniform in `t ∈ ℝ`.
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

/-- **Prop D**, from the Key Lemma. -/
theorem propD56_of (d : ℕ) (hd : 1 ≤ d) (CK : ℝ) (hK : KeyLemma56 d CK) :
    ∃ CD : ℝ, 0 ≤ CD ∧ PropD56 d CD := by
  classical
  let CD : ℝ := (d : ℝ) * (∑ j ∈ Finset.Icc 1 d, (j : ℝ) ^ 4) * CK
  refine ⟨CD, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg fun j _ => pow_nonneg (Nat.cast_nonneg _) _))
      (keyConstant_nonneg d hd CK hK)
  · intro n hn v hv t
    cases n with
    | zero => omega
    | succ k =>
      obtain ⟨b, hb⟩ := unit_basis_exists (k + 1) (by omega) v hv
      have hb0 : b 0 = WithLp.toLp 2 v := hb
      letI := axialMeasure_probability b v hb0 t
      have hm := lawRK_eq_polar_map b v hb0 t
      unfold deltaSq
      rw [hm, kernel_integral_map _ (polarState v) (measurable_polarState v)
        (fun x y => rhoR d v x y ^ 2) (measurable_rhoSq_PropD d v)]
      have h := mixed_correlation_integral_le d hd CK hK hn v hv (axialMeasure t v)
      simpa only [CD, mul_div_assoc] using h

end BstLean.Part56
