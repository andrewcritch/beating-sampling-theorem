import BstLean.Part56MC_Noise

namespace BstLean.Part56

open MeasureTheory
open BstLean.Part29 (stdGauss)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def wickSpan : Submodule ℝ (MvPolynomial ι ℝ) :=
  Submodule.span ℝ (Set.range (mc56_wickWord (ι := ι)))

private lemma word_mem (w : List ι) : mc56_wickWord w ∈ wickSpan (ι := ι) :=
  Submodule.subset_span ⟨w, rfl⟩

private lemma raise_mem (i : ι) (p : MvPolynomial ι ℝ) (hp : p ∈ wickSpan) :
    MvPolynomial.X i * p - MvPolynomial.pderiv i p ∈ wickSpan := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w, rfl⟩ := hp
    exact word_mem (i :: w)
  | zero => simp
  | add p q hp hq ihp ihq =>
    simpa only [mul_add, map_add, add_sub_add_comm] using wickSpan.add_mem ihp ihq
  | smul r p hp ih =>
    simpa only [mul_smul_comm, Derivation.map_smul, smul_sub] using wickSpan.smul_mem r ih

private lemma deriv_word_mem (i : ι) (w : List ι) :
    MvPolynomial.pderiv i (mc56_wickWord w) ∈ wickSpan := by
  induction w with
  | nil => simp [mc56_wickWord]
  | cons j w ih =>
    rw [mc56_wickWord, map_sub, MvPolynomial.pderiv_mul, BstLean.Part41.pderiv_comm']
    have he : MvPolynomial.pderiv i (MvPolynomial.X j) * mc56_wickWord w +
        MvPolynomial.X j * MvPolynomial.pderiv i (mc56_wickWord w) -
          MvPolynomial.pderiv j (MvPolynomial.pderiv i (mc56_wickWord w)) =
        MvPolynomial.pderiv i (MvPolynomial.X j) * mc56_wickWord w +
          (MvPolynomial.X j * MvPolynomial.pderiv i (mc56_wickWord w) -
            MvPolynomial.pderiv j (MvPolynomial.pderiv i (mc56_wickWord w))) := by ring
    rw [he]
    apply wickSpan.add_mem _ (raise_mem j _ ih)
    by_cases h : i = j
    · subst j; simpa using word_mem (ι := ι) w
    · simpa [h] using (wickSpan.zero_mem : (0 : MvPolynomial ι ℝ) ∈ wickSpan)

private lemma deriv_mem (i : ι) (p : MvPolynomial ι ℝ) (hp : p ∈ wickSpan) :
    MvPolynomial.pderiv i p ∈ wickSpan := by
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w, rfl⟩ := hp; exact deriv_word_mem i w
  | zero => simp
  | add p q hp hq ihp ihq => simpa only [map_add] using wickSpan.add_mem ihp ihq
  | smul r p hp ih => simpa only [Derivation.map_smul] using wickSpan.smul_mem r ih

theorem mc56_wickWord_span : Submodule.span ℝ (Set.range (mc56_wickWord (ι := ι))) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  change p ∈ wickSpan
  induction p using MvPolynomial.induction_on with
  | C c =>
    have h := wickSpan.smul_mem c (word_mem (ι := ι) [])
    simpa [mc56_wickWord, Algebra.smul_def] using h
  | add p q hp hq => exact wickSpan.add_mem hp hq
  | mul_X p i hp =>
    have h := wickSpan.add_mem (raise_mem i p hp) (deriv_mem i p hp)
    simpa only [sub_add_cancel, mul_comm] using h

elab "mc56WordOrthogonalImported" : term => do
  let env ← Lean.getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
    name.toString == "_private.BstLean.Part41Contam.0.BstLean.Part41.wickWord_orthogonal")
    | throwError "Part41Contam.wickWord_orthogonal is unavailable"
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

elab "mc56WordImported" : term => do
  let env ← Lean.getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
    name.toString == "_private.BstLean.Part41Contam.0.BstLean.Part41.wickWord")
    | throwError "Part41Contam.wickWord is unavailable"
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

private lemma word_eq_imported (w : List ι) : mc56_wickWord w = mc56WordImported w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change _ = MvPolynomial.X i * mc56WordImported w -
      MvPolynomial.pderiv i (mc56WordImported w)
    rw [mc56_wickWord, ih]

theorem mc56_wickWord_orthogonal (w v : List ι) (h : w.length ≠ v.length) :
    ∫ x, MvPolynomial.eval x (mc56_wickWord w) * MvPolynomial.eval x (mc56_wickWord v)
      ∂stdGauss ι = 0 := by
  have ho := mc56WordOrthogonalImported w v h
  change (∫ x, MvPolynomial.eval x (_) ∂stdGauss ι) = 0 at ho
  simp only [MvPolynomial.eval_mul] at ho
  simpa only [word_eq_imported] using ho

end BstLean.Part56
