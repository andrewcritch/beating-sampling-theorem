import BstLean.Part213Rows

/-! General Gaussian polynomial row supplies. The radius squared has the
same two-dimensional Gaussian distribution as in Part186. -/
namespace BstLean.Part213
open MeasureTheory ProbabilityTheory Real
open BstLean.Part186.RA
open BstLean.Part29 (stdGauss gaussMom)

/-- The exact moment of the squared plane radius. -/
noncomputable def radiusMoment (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1),
    gaussMom (2 * i) * (j.choose i : ℝ) * gaussMom (2 * (j - i))

lemma radiusMoment_eq (j : ℕ) : radiusMoment j = ∫ p, RR p ^ j ∂ρ2 :=
  (int_RR_pow j).2.symm

lemma radiusMoment_nonneg (j : ℕ) : 0 ≤ radiusMoment j := by
  rw [radiusMoment_eq]
  exact integral_nonneg fun p => pow_nonneg (RR_nonneg p) j

/-- This bound is valid for every positive row order. -/
noncomputable def polynomialRowBound (c0 c1 c2 : ℝ) (k : ℕ) : ℝ :=
  (c0 + c1 + c2) ^ k * (2 ^ (2 * k - 1) * (1 + radiusMoment (2 * k))) +
    (c0 + 2 * c1 + 8 * c2) ^ k

lemma polynomialRowBound_nonneg {c0 c1 c2 : ℝ}
    (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (k : ℕ) :
    0 ≤ polynomialRowBound c0 c1 c2 k := by
  unfold polynomialRowBound
  have := radiusMoment_nonneg (2 * k)
  positivity

/-- All absolute powers of a centred polynomial row are integrable and bounded. -/
theorem polynomial_centred_moment {c0 c1 c2 : ℝ}
    (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (fun p => |qp c0 c1 c2 (RR p) - (c0 + 2 * c1 + 8 * c2)| ^ k) ρ2 ∧
    (∫ p, |qp c0 c1 c2 (RR p) - (c0 + 2 * c1 + 8 * c2)| ^ k ∂ρ2) ≤
      polynomialRowBound c0 c1 c2 k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  let K := c0 + c1 + c2
  let μ := c0 + 2 * c1 + 8 * c2
  have hμ : 0 ≤ μ := by dsimp [μ]; positivity
  have hmaj := fun p => cen_pow_le h0 h1 h2 hμ (RR_nonneg p) j
  have hi := int_maj (2 * j + 2) (K ^ (j + 1) * 2 ^ (2 * j + 1)) (μ ^ (j + 1))
  have ip : Integrable (fun p => |qp c0 c1 c2 (RR p) - μ| ^ (j + 1)) ρ2 := by
    refine hi.1.mono'
      (((measurable_qpRR c0 c1 c2).sub measurable_const).abs.pow_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    dsimp [K]
    linarith [hmaj p]
  refine ⟨ip, ?_⟩
  refine (integral_mono ip hi.1 (fun p => by dsimp [K]; linarith [hmaj p])).trans ?_
  rw [hi.2]
  unfold polynomialRowBound
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, radiusMoment_eq]
  have he : 2 * (j + 1) = 2 * j + 2 := by omega
  rw [he]
  dsimp [K, μ]
  exact le_of_eq (by ring)

lemma polynomial_centred_integrable (c0 c1 c2 : ℝ)
    (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (k : ℕ) :
    Integrable (fun p => (qp c0 c1 c2 (RR p) - (c0 + 2 * c1 + 8 * c2)) ^ k) ρ2 := by
  by_cases hk : k = 0
  · simp only [hk, pow_zero]; exact integrable_const _
  have hi := (polynomial_centred_moment h0 h1 h2 (show 1 ≤ k by omega)).1
  refine hi.mono'
    (((measurable_qpRR c0 c1 c2).sub measurable_const).pow_const k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  simp only [Real.norm_eq_abs, abs_pow]
  exact le_refl _

/-- The binomial envelope supplies every even moment of the centred row sum. -/
theorem polynomial_centred_sum {m p : ℕ} {c0 c1 c2 : ℝ}
    (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) :
    ∫⁻ y, ENNReal.ofReal ((∑ j : Fin m,
      (qp c0 c1 c2 (RR (y j)) - (c0 + 2 * c1 + 8 * c2))) ^ (2 * p))
        ∂(Measure.pi fun _ : Fin m => ρ2) ≤
      ENNReal.ofReal (rowEnvelope (polynomialRowBound c0 c1 c2) m (2 * p)) := by
  refine centred_rows_even ρ2 (polynomialRowBound_nonneg h0 h1 h2)
    (fun _ p => qp c0 c1 c2 (RR p) - (c0 + 2 * c1 + 8 * c2)) ?_ ?_ ?_ ?_
  · intro j
    exact (measurable_qpRR c0 c1 c2).sub measurable_const
  · intro j k _
    exact polynomial_centred_integrable c0 c1 c2 h0 h1 h2 k
  · intro j
    rw [integral_sub int_qpRR.1 (integrable_const _), int_qpRR.2]
    simp
  · intro j k hk _
    exact (polynomial_centred_moment h0 h1 h2 (by omega)).2

#print axioms polynomial_centred_moment
#print axioms polynomial_centred_sum
end BstLean.Part213
