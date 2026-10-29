import Mathlib

/-!
# Part 29, layer L2: the normalization identity

`proofs/option-m/29-explicit-22-at-100.tex`, Lemma (exact normalization). For a nonzero `Z` and
`M = Z / ‖Z‖`, a centred quadratic form of `M` equals a trace-free quadratic form of `Z` divided by
`‖Z‖²`. Together with the floor `sd ≥ √Y(Z) / ‖Z‖²`, the factor `‖Z‖²` cancels in the ratio error/sd.
-/

namespace BstLean.Part29

open Matrix

variable {D : ℕ}

/-- The normalization identity: with `M = Z / √(Z·Z)`,
`Mᵀ A M − tr A / D = Zᵀ (A − (tr A / D) I) Z / (Z·Z)`. -/
theorem normalize (A : Matrix (Fin D) (Fin D) ℝ) (Z : Fin D → ℝ) (hZ : Z ≠ 0) :
    let M : Fin D → ℝ := (1 / Real.sqrt (Z ⬝ᵥ Z)) • Z
    M ⬝ᵥ (A *ᵥ M) - A.trace / D = (Z ⬝ᵥ ((A - (A.trace / D) • (1 : Matrix (Fin D) (Fin D) ℝ)) *ᵥ Z)) / (Z ⬝ᵥ Z) := by
  intro M
  have hpos : 0 < Z ⬝ᵥ Z := by
    rcases Function.ne_iff.mp hZ with ⟨i, hi⟩
    have : 0 < Z i * Z i := mul_self_pos.mpr hi
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ Z j * Z j := fun j _ => mul_self_nonneg _
    calc 0 < Z i * Z i := this
      _ ≤ ∑ j, Z j * Z j := Finset.single_le_sum hnn (Finset.mem_univ i)
      _ = Z ⬝ᵥ Z := rfl
  have hs : Real.sqrt (Z ⬝ᵥ Z) ^ 2 = Z ⬝ᵥ Z := Real.sq_sqrt hpos.le
  have hsne : Real.sqrt (Z ⬝ᵥ Z) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  simp only [M, mulVec_smul, dotProduct_smul, smul_dotProduct, sub_mulVec, smul_mulVec,
    one_mulVec, dotProduct_sub, smul_eq_mul]
  field_simp
  simp only [hs]
  ring
