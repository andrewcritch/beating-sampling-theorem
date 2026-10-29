import BstLean.Part217Moment

/-! Active row maxima and the conditional direction estimate. -/
namespace BstLean.Part217
open MeasureTheory Real Set
open scoped ENNReal

def squaredNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := ∑ i, v i ^ 2

noncomputable def activeMaximum {m : ℕ} (hm : 0 < m)
    (D : Fin m → Bool) (R : Fin m → ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ fun i => if D i then R i else 0

lemma activeMaximum_nonneg {m : ℕ} (hm : 0 < m) (D : Fin m → Bool)
    {R : Fin m → ℝ} (hR : ∀ i, 0 ≤ R i) : 0 ≤ activeMaximum hm D R := by
  have h0 : 0 ≤ (if D ⟨0, hm⟩ then R ⟨0, hm⟩ else 0) := by
    split
    · exact hR _
    · exact le_rfl
  exact h0.trans (Finset.le_sup' (fun i => if D i then R i else 0)
    (Finset.mem_univ ⟨0, hm⟩))

lemma activeMaximum_all_false {m : ℕ} (hm : 0 < m) (R : Fin m → ℝ) :
    activeMaximum hm (fun _ => false) R = 0 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    exact le_rfl
  · exact Finset.le_sup' (fun _ : Fin m => (0 : ℝ)) (Finset.mem_univ ⟨0, hm⟩)

lemma activeMaximum_le {m : ℕ} (hm : 0 < m) {D : Fin m → Bool}
    {R : Fin m → ℝ} {a : ℝ} (ha : 0 ≤ a) (h : ∀ i, D i = true → R i ≤ a) :
    activeMaximum hm D R ≤ a := by
  apply Finset.sup'_le
  intro i _
  cases hD : D i
  · simpa [hD] using ha
  · simpa [hD] using h i hD

lemma activeMaximum_gt_iff {m : ℕ} (hm : 0 < m) (D : Fin m → Bool)
    (R : Fin m → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    a < activeMaximum hm D R ↔ ∃ i, D i = true ∧ a < R i := by
  constructor
  · intro h
    by_contra hn
    have hb : ∀ i, D i = true → R i ≤ a := by
      intro i hi
      exact le_of_not_gt (fun hr => hn ⟨i, hi, hr⟩)
    exact (not_lt_of_ge (activeMaximum_le hm ha hb)) h
  · rintro ⟨i, hi, hr⟩
    have hl := Finset.le_sup' (fun j => if D j then R j else 0) (Finset.mem_univ i)
    have hl' : R i ≤ activeMaximum hm D R := by simpa [activeMaximum, hi] using hl
    exact hr.trans_le hl'

/-- The coefficient can depend on every gate and every row length. -/
theorem active_coefficient_energy {m : ℕ} (hm : 0 < m) (D : Fin m → Bool)
    {R c : Fin m → ℝ} (hR : ∀ i, 0 ≤ R i)
    (hoff : ∀ i, D i = false → c i = 0) {B : ℝ} (hB : squaredNorm c ≤ B) :
    squaredNorm (fun i => c i * R i) ≤ activeMaximum hm D R ^ 2 * B := by
  calc
    squaredNorm (fun i => c i * R i) ≤
        (∑ i, activeMaximum hm D R ^ 2 * c i ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      change (c i * R i) ^ 2 ≤ activeMaximum hm D R ^ 2 * c i ^ 2
      cases hi : D i
      · simp only [hoff i hi, zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
      · have hr : R i ≤ activeMaximum hm D R := by
          have := Finset.le_sup' (fun j => if D j then R j else 0) (Finset.mem_univ i)
          simpa [activeMaximum, hi] using this
        simpa [mul_pow, mul_comm] using
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hR i) hr 2) (sq_nonneg (c i))
    _ = activeMaximum hm D R ^ 2 * squaredNorm c := by rw [← Finset.mul_sum]; rfl
    _ ≤ activeMaximum hm D R ^ 2 * B := mul_le_mul_of_nonneg_left hB (sq_nonneg _)

theorem activeMaximum_union_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ} (hm : 0 < m)
    (D : Ω → Fin m → Bool) (R : Ω → Fin m → ℝ) {a q : ℝ} (ha : 0 ≤ a)
    (hrow : ∀ i, μ.real {ω | D ω i = true ∧ a < R ω i} ≤ q) :
    μ.real {ω | a < activeMaximum hm (D ω) (R ω)} ≤ m * q := by
  have he : {ω | a < activeMaximum hm (D ω) (R ω)} =
      ⋃ i, {ω | D ω i = true ∧ a < R ω i} := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, activeMaximum_gt_iff hm _ _ ha]
  rw [he]
  exact (measureReal_iUnion_fintype_le _).trans (by
    calc ∑ i : Fin m, μ.real {ω | D ω i = true ∧ a < R ω i} ≤ ∑ _i : Fin m, q :=
          Finset.sum_le_sum fun i _ => hrow i
      _ = m * q := by simp)

theorem independent_gate_tail {Ω : Type*} [MeasurableSpace Ω]
    (nu : Measure Bool) (mu : Measure Ω) [IsProbabilityMeasure nu] [IsProbabilityMeasure mu]
    (hgate : nu.real {b | b = true} = 1 / 2) (R : Ω → ℝ) (a : ℝ) :
    (nu.prod mu).real {z | z.1 = true ∧ a < R z.2} =
      (1 / 2) * mu.real {ω | a < R ω} := by
  change (nu.prod mu).real ({b | b = true} ×ˢ {ω | a < R ω}) = _
  rw [measureReal_prod_prod, hgate]

theorem activeMaximum_shifted_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ} (hm : 0 < m)
    (D : Ω → Fin m → Bool) (R : Ω → Fin m → ℝ) {a t c rate : ℝ} (ha : 0 ≤ a)
    (hbase : (m : ℝ) / 2 * exp (-rate) ≤ 1)
    (hrow : ∀ i v, 0 < v → μ.real {ω | D ω i = true ∧ a + v < R ω i} ≤
      (1 / 2) * exp (-rate - t * v - c * v ^ 2 / 2)) :
    ∀ v : ℝ, 0 < v → μ.real {ω | a + v < activeMaximum hm (D ω) (R ω)} ≤
      exp (-t * v - c * v ^ 2 / 2) := by
  intro v hv
  have hu := activeMaximum_union_tail hm D R (show 0 ≤ a + v by linarith)
    (fun i => hrow i v hv)
  refine hu.trans ?_
  have he : exp (-rate - t * v - c * v ^ 2 / 2) =
      exp (-rate) * exp (-t * v - c * v ^ 2 / 2) := by
    rw [← exp_add]
    congr 1
    ring
  rw [he]
  calc (m : ℝ) * ((1 / 2) * (exp (-rate) * exp (-t * v - c * v ^ 2 / 2))) =
      ((m : ℝ) / 2 * exp (-rate)) * exp (-t * v - c * v ^ 2 / 2) := by ring
    _ ≤ 1 * exp (-t * v - c * v ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hbase (exp_pos _).le
    _ = _ := one_mul _

end BstLean.Part217
