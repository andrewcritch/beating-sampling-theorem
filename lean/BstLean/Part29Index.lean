import BstLean.Part29Gauss

/-!
# Part 29, final assembly: the coefficient space and the Gaussian on it

The raw coefficients of the quadratic map `m` are indexed by `CoefIdx n`: constants `Fin n`, linear
coefficients `Fin n × Fin n` (output, input), and quadratic coefficients `(i, j, k)` with `i ≤ j` (the monomial
`x_i x_j` in output `k`). `M` uniform on its coefficient sphere is `Z / ‖Z‖` with `Z` standard Gaussian on
`CoefIdx n`. This file supplies the facts about that Gaussian that the assembly uses, over a general
`Fintype` index: the moments, the centred quadratic-form bound, and the marginal on a subset of coordinates.
-/

namespace BstLean.Part29

open MeasureTheory ProbabilityTheory

/-- The raw coefficient index of a quadratic map `ℝⁿ → ℝⁿ`. -/
abbrev CoefIdx (n : ℕ) := Fin n ⊕ (Fin n × Fin n) ⊕ {p : Fin n × Fin n × Fin n // p.1 ≤ p.2.1}

/-- `|CoefIdx n| = n · N`, `N = (n+1)(n+2)/2` the number of monomials of degree at most two. -/
theorem card_coefIdx (n : ℕ) : 2 * Fintype.card (CoefIdx n) = n * ((n + 1) * (n + 2)) := by
  classical
  let e : {p : Fin n × Fin n × Fin n // p.1 ≤ p.2.1} ≃
      (Σ j : Fin n, {i : Fin n // i ≤ j}) × Fin n :=
    { toFun := fun p => (⟨p.1.2.1, ⟨p.1.1, p.2⟩⟩, p.1.2.2)
      invFun := fun p => ⟨(p.1.2.1, p.1.1, p.2), p.1.2.2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  have hc (j : Fin n) : Fintype.card {i : Fin n // i ≤ j} = j.val + 1 := by
    rw [Fintype.card_subtype]
    change (Finset.univ.filter (fun i : Fin n => i ≤ j)).card = _
    rw [show Finset.univ.filter (fun i : Fin n => i ≤ j) = Finset.Iic j by
      ext i; simp]
    exact Fin.card_Iic j
  have ht : 2 * (∑ j : Fin n, (j.val + 1)) = n * (n + 1) := by
    clear hc e
    rw [show (∑ j : Fin n, (j.val + 1)) = ∑ j ∈ Finset.range n, (j + 1) from
      Fin.sum_univ_eq_sum_range (fun j => j + 1) n]
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ]; nlinarith
  have he := Fintype.card_congr e
  simp only [Fintype.card_prod, Fintype.card_sigma, Fintype.card_fin, hc] at he
  simp only [CoefIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [he]
  nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard Gaussian on `ι → ℝ`. -/
noncomputable def stdGauss (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => gaussianReal 0 1

instance : IsProbabilityMeasure (stdGauss ι) := by unfold stdGauss; infer_instance

/-- The quadratic form over a general index. -/
def qformι (B : Matrix ι ι ℝ) (z : ι → ℝ) : ℝ := ∑ i, ∑ j, B i j * z i * z j

private lemma qform_reindex (e : ι ≃ Fin (Fintype.card ι)) (B : Matrix ι ι ℝ)
    (z : Fin (Fintype.card ι) → ℝ) :
    qformι B (fun i => z (e i)) = qform (fun i j => B (e.symm i) (e.symm j)) z := by
  unfold qformι qform
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [← e.sum_comp]
  simp

private lemma gauss_reindex (e : ι ≃ Fin (Fintype.card ι)) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e.symm)
      (stdGauss (Fin (Fintype.card ι))) (stdGauss ι) :=
  measurePreserving_piCongrLeft (fun _ : ι => gaussianReal 0 1) e.symm

private lemma gauss_reindex_apply (e : ι ≃ Fin (Fintype.card ι))
    (z : Fin (Fintype.card ι) → ℝ) :
    (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e.symm) z = fun i => z (e i) := by
  funext i
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

/-- **The centred quadratic-form bound** over a general index: for symmetric `A`,
`E (Zᵀ (A − (tr A / |ι|) I) Z)² ≤ 2 ‖A‖_F²`. -/
theorem stdGauss_centred_sq_le (hι : 0 < Fintype.card ι) (A : Matrix ι ι ℝ) (hA : A.IsSymm) :
    ∫ z, qformι (A - ((∑ k, A k k) / Fintype.card ι) • (1 : Matrix ι ι ℝ)) z ^ 2 ∂(stdGauss ι) ≤
      2 * ∑ i, ∑ j, A i j ^ 2 := by
  classical
  let e := Fintype.equivFin ι
  let A' : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ :=
    fun i j => A (e.symm i) (e.symm j)
  have hs : A'.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact hA.apply _ _
  have h := gauss_centred_sq_le hι (stdGauss _) gaussMoments_std A' hs
  rw [← (gauss_reindex e).integral_comp' (fun z =>
    qformι (A - ((∑ k, A k k) / Fintype.card ι) • 1) z ^ 2)]
  have ht : (∑ k, A k k) = ∑ k, A' k k := by
    exact (e.symm.sum_comp (fun k => A k k)).symm
  have hb : (fun i j => (A - ((∑ k, A k k) / Fintype.card ι) • 1)
      (e.symm i) (e.symm j)) = A' - ((∑ k, A' k k) / Fintype.card ι) •
        (1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ) := by
    ext i j
    change A (e.symm i) (e.symm j) -
      ((∑ k, A k k) / Fintype.card ι) * (if e.symm i = e.symm j then 1 else 0) =
      A (e.symm i) (e.symm j) -
      ((∑ k, A' k k) / Fintype.card ι) * (if i = j then 1 else 0)
    simp [ht]
  simp only [gauss_reindex_apply, qform_reindex, hb]
  have hf : (∑ i, ∑ j, A i j ^ 2) = ∑ i, ∑ j, A' i j ^ 2 := by
    rw [← e.symm.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    exact (e.symm.sum_comp (fun j => A (e.symm i) j ^ 2)).symm
  rw [hf]
  exact h

/-- Integrability of the square of a quadratic form under the standard Gaussian. -/
theorem stdGauss_qform_sq_integrable (B : Matrix ι ι ℝ) :
    Integrable (fun z => qformι B z ^ 2) (stdGauss ι) := by
  classical
  let e := Fintype.equivFin ι
  rw [← (gauss_reindex e).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp only [Function.comp_def, gauss_reindex_apply, qform_reindex]
  let B' : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ :=
    fun i j => B (e.symm i) (e.symm j)
  have hm := (gaussMoments_std (D := Fintype.card ι)).int4
  have hex (z : Fin (Fintype.card ι) → ℝ) : qform B' z ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l, (B' i j * B' k l) * (z i * z j * z k * z l) := by
    simp only [qform, pow_two, Finset.sum_mul, Finset.mul_sum]
    congr 1; ext i; congr 1; ext j; congr 1; ext k; congr 1; ext l; ring
  change Integrable (fun z => qform B' z ^ 2) (stdGauss _)
  simp_rw [hex]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
      (hm i j k l).const_mul _))))

/-- **The marginal on a subset of coordinates** is the standard Gaussian there: for an injection
`e : κ → ι`, restricting `z` along `e` pushes `stdGauss ι` forward to `stdGauss κ`. -/
theorem stdGauss_map_restrict {κ : Type*} [Fintype κ] (e : κ → ι) (he : Function.Injective e) :
    (stdGauss ι).map (fun z : ι → ℝ => z ∘ e) = stdGauss κ := by
  classical
  have h := (iIndepFun_pi (μ := fun _ : ι => gaussianReal 0 1)
    (X := fun _ => fun x : ℝ => x) (fun _ => measurable_id.aemeasurable)).precomp he
  have hm := h.map_fun_eq_pi_map (fun k => (measurable_pi_apply (e k)).aemeasurable)
  simpa only [stdGauss, Function.comp_def,
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) _).map_eq] using hm

end BstLean.Part29
