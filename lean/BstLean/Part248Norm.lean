import BstLean.Part248Reciprocal

/-! Minkowski converts finite deficit moments to retained reciprocal bounds. -/
namespace BstLean.Part248
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part242

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma norm_sum {q : ℕ} (hq : 1 ≤ q) (s : Finset ℕ)
    {f : ℕ → X → ℝ} {B : ℕ → ℝ} (h : ∀ j ∈ s, LBound μ q (f j) (B j)) :
    LBound μ q (fun x => ∑ j ∈ s, f j x) (∑ j ∈ s, B j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨measurable_const, le_rfl, by simp [eLpNorm_zero]⟩
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self _ _)).add (by exact_mod_cast hq)
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

noncomputable def reciprocalEstimate (k : ℕ) (d Y0 : ℝ) (B : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.range k, B j ^ j / Y0 ^ (j + 1)) + B k ^ k / (d * Y0 ^ k)

/-- The expansion uses order `j*q` for its term of degree `j`.
Restriction retains the original mass and adds no event charge. -/
theorem R_norm {q k : ℕ} (hq : 1 ≤ q) {K : Set X} (hK : MeasurableSet K)
    (hmass : μ univ ≤ 1) {Y : X → ℝ} (mY : Measurable Y)
    {d Y0 : ℝ} (hd : 0 < d) (hY0 : 0 < Y0) (hfloor : ∀ x ∈ K, d ≤ Y x)
    {B : ℕ → ℝ}
    (hD : ∀ j, 1 ≤ j → j ≤ k →
      LBound μ ((q * j : ℕ) : ℝ≥0∞) (fun x => max 0 (Y0 - Y x)) (B j)) :
    LBound (μ.restrict K) q (fun x => 1 / Y x) (reciprocalEstimate k d Y0 B) := by
  have hq0 : q ≠ 0 := by omega
  have hm : (μ.restrict K) univ ≤ 1 := (Measure.restrict_le_self univ).trans hmass
  have hp : ∀ j, j ≤ k → LBound (μ.restrict K) q
      (fun x => (max 0 (Y0 - Y x)) ^ j) (B j ^ j) := by
    intro j hj
    by_cases hz : j = 0
    · subst j
      simp only [pow_zero]
      exact LBound.const hq0 hm zero_le_one
    · exact LBound.ofMoment hq0
        (((hD j (by omega) hj).restrict K).toMoment (mul_ne_zero hq0 hz)).power
  have hs : LBound (μ.restrict K) q
      (fun x => ∑ j ∈ Finset.range k, (max 0 (Y0 - Y x)) ^ j / Y0 ^ (j + 1))
      (∑ j ∈ Finset.range k, B j ^ j / Y0 ^ (j + 1)) := by
    apply norm_sum hq
    intro j hj
    have hh := (hp j (Nat.le_of_lt (Finset.mem_range.mp hj))).scale hq0
      (show 0 ≤ (Y0 ^ (j + 1))⁻¹ by positivity)
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have hr := (hp k le_rfl).scale hq0
    (show 0 ≤ (d * Y0 ^ k)⁻¹ by positivity)
  have hb : LBound (μ.restrict K) q (fun x => expansion k d Y0 (max 0 (Y0 - Y x)))
      (reciprocalEstimate k d Y0 B) := by
    simpa only [expansion, reciprocalEstimate, div_eq_mul_inv, mul_comm] using
      hs.add (by exact_mod_cast hq) hr
  apply hb.mono (measurable_const.div mY)
  apply (ae_restrict_iff' hK).mpr
  exact Filter.Eventually.of_forall fun x hx => by
    have hy := hd.trans_le (hfloor x hx)
    have hh := R k hd hY0 (hfloor x hx)
    change |1 / Y x| ≤ |expansion k d Y0 (max 0 (Y0 - Y x))|
    rw [abs_of_pos (one_div_pos.mpr hy), abs_of_nonneg ((one_div_pos.mpr hy).le.trans hh)]
    exact hh

#print axioms norm_sum
#print axioms R_norm
end BstLean.Part248
