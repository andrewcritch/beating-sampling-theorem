import BstLean.Part239Centering
import BstLean.Part213Partition

/-! General even row bounds use the exact nonnegative-row centering correction. -/
namespace BstLean.Part239
open MeasureTheory ProbabilityTheory Real
open BstLean.Part213

/-- The binomial envelope has an exact integer recurrence. -/
def rowAssignmentCount : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | m + 1, k => ∑ i ∈ Finset.range (k + 1),
      k.choose i * (if i = 1 then 0 else 1) * rowAssignmentCount m (k - i)

theorem rowAssignmentCount_cast (m k : ℕ) :
    (rowAssignmentCount m k : ℝ) = rowEnvelope (fun _ => 1) m k := by
  induction m generalizing k with
  | zero => by_cases hk : k = 0 <;> simp [rowAssignmentCount, rowEnvelope, hk]
  | succ m ih =>
    simp only [rowAssignmentCount, rowEnvelope, Nat.cast_sum, Nat.cast_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [ih]
    have hw : ((if i = 1 then 0 else 1 : ℕ) : ℝ) = rowWeight (fun _ => 1) i := by
      rcases i with _ | _ | i <;> simp [rowWeight]
    rw [hw]

/-- The scalar correction bounds every centred row by its source moment. -/
theorem nonnegative_rows_even {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) [IsProbabilityMeasure ρ] {m p : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (f : Fin m → X → ℝ) (hm : ∀ j, Measurable (f j))
    (h0 : ∀ j x, 0 ≤ f j x) (hf : ∀ j, Integrable (f j) ρ)
    (hi : ∀ j k, k ≤ 2 * p → Integrable (fun x => f j x ^ k) ρ)
    (hc : ∀ j k, k ≤ 2 * p →
      Integrable (fun x => (f j x - ∫ y, f j y ∂ρ) ^ k) ρ)
    (hM : ∀ j k, 2 ≤ k → k ≤ 2 * p → ∫ x, f j x ^ k ∂ρ ≤ B ^ k) :
    ∫⁻ y, ENNReal.ofReal ((∑ j, (f j (y j) - ∫ x, f j x ∂ρ)) ^ (2 * p))
      ∂(Measure.pi fun _ : Fin m => ρ) ≤
      ENNReal.ofReal ((rowAssignmentCount m (2 * p) : ℝ) * B ^ (2 * p)) := by
  have hr := centred_rows_even ρ (fun k => pow_nonneg hB k)
    (fun j x => f j x - ∫ y, f j y ∂ρ)
    (fun j => (hm j).sub_const _) hc
    (fun j => by rw [integral_sub (hf j) (integrable_const _)]; simp)
    (fun j k hk hkp => ?_)
  · rw [rowEnvelope_scale hB] at hr
    rw [rowAssignmentCount_cast]
    simpa only [mul_comm] using hr
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    have hcen := centering_moment ρ (h0 j) (hf j) n (hi j _ hkp)
      (by simpa only [Real.norm_eq_abs, abs_pow] using (hc j _ hkp).norm)
    exact hcen.trans ((sub_le_self _ (pow_nonneg (integral_nonneg (h0 j)) _)).trans
      (hM j _ (by omega) hkp))

#print axioms rowAssignmentCount_cast
#print axioms nonnegative_rows_even
end BstLean.Part239
