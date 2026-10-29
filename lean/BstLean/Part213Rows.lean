import BstLean.Part186RA2

/-! General finite-order moments of independent centred rows.
The binomial recurrence retains the zero first moment. All rows use one
probability distribution. No event restriction enters the row product. -/
namespace BstLean.Part213
open MeasureTheory ProbabilityTheory Real

/-- Row moment weights retain the zero first moment. -/
noncomputable def rowWeight (b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | k + 2 => b (k + 2)

/-- The finite binomial envelope for a sum of `m` centred rows. -/
noncomputable def rowEnvelope (b : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, k => if k = 0 then 1 else 0
  | m + 1, k => ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * rowWeight b i * rowEnvelope b m (k - i)

lemma rowWeight_nonneg {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k) (i : ℕ) :
    0 ≤ rowWeight b i := by
  rcases i with _ | _ | i <;> simp [rowWeight, hb]

lemma rowEnvelope_nonneg {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k) (m k : ℕ) :
    0 ≤ rowEnvelope b m k := by
  induction m generalizing k with
  | zero => simp only [rowEnvelope]; split <;> norm_num
  | succ m ih =>
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (rowWeight_nonneg hb i)) (ih _)

variable {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ]

/-- Independent centred rows admit a binomial bound at every finite order.
The rows can differ. The common bounds `b` refer to whole rows. -/
theorem centred_rows_moment {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k) (K : ℕ) :
    ∀ (m : ℕ) (φ : Fin m → X → ℝ), (∀ j, Measurable (φ j)) →
    (∀ j k, k ≤ K → Integrable (fun x => φ j x ^ k) ρ) →
    (∀ j, ∫ x, φ j x ∂ρ = 0) →
    (∀ j k, 2 ≤ k → k ≤ K → ∫ x, |φ j x| ^ k ∂ρ ≤ b k) →
    ∀ k ≤ K,
      Integrable (fun y : Fin m → X => (∑ j, φ j (y j)) ^ k)
        (Measure.pi fun _ => ρ) ∧
      |∫ y, (∑ j, φ j (y j)) ^ k ∂(Measure.pi fun _ => ρ)| ≤ rowEnvelope b m k := by
  intro m
  induction m with
  | zero =>
    intro φ _ _ _ _ k _
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    refine ⟨integrable_const _, ?_⟩
    by_cases hk : k = 0 <;> simp [rowEnvelope, hk, zero_pow]
  | succ m ih =>
    intro φ hm hi h0 hB k hk
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => X) 0
    have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (m + 1) => ρ)
        (ρ.prod (Measure.pi fun _ : Fin m => ρ)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => ρ) 0
    let ψ : Fin m → X → ℝ := fun j => φ j.succ
    have ihψ := ih ψ (fun j => hm _) (fun j i hi' => hi _ i hi')
      (fun j => h0 _) (fun j i h2 hi' => hB _ i h2 hi')
    let a : X → ℝ := φ 0
    let z : (Fin m → X) → ℝ := fun y => ∑ j, ψ j (y j)
    let g : X × (Fin m → X) → ℝ := fun p => (a p.1 + z p.2) ^ k
    have hfg : (fun y : Fin (m + 1) → X => (∑ j, φ j (y j)) ^ k) = g ∘ e := by
      funext y
      simp [g, a, z, ψ, e, Fin.sum_univ_succ, Fin.insertNthEquiv, Fin.tail]
    have hexp : ∀ p : X × (Fin m → X), g p = ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (a p.1 ^ i * z p.2 ^ (k - i)) := fun p => by
      dsimp [g]; rw [add_pow]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hiT : ∀ i ∈ Finset.range (k + 1), Integrable (fun p : X × (Fin m → X) =>
        (k.choose i : ℝ) * (a p.1 ^ i * z p.2 ^ (k - i)))
          (ρ.prod (Measure.pi fun _ => ρ)) := by
      intro i hi'
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
      exact ((hi 0 i (hik.trans hk)).mul_prod (ihψ (k - i) (by omega)).1).const_mul _
    have hgi : Integrable g (ρ.prod (Measure.pi fun _ => ρ)) :=
      (integrable_finsetSum _ hiT).congr
        (Filter.Eventually.of_forall fun p => (hexp p).symm)
    have hval : ∫ p, g p ∂(ρ.prod (Measure.pi fun _ => ρ)) =
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ((∫ x, a x ^ i ∂ρ) * ∫ y, z y ^ (k - i) ∂(Measure.pi fun _ => ρ)) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hexp), integral_finsetSum _ hiT]
      exact Finset.sum_congr rfl fun i _ => by
        rw [integral_const_mul,
          integral_prod_mul (fun x => a x ^ i) (fun y => z y ^ (k - i))]
    refine ⟨?_, ?_⟩
    · rw [hfg]
      exact (hmp.integrable_comp_emb e.measurableEmbedding).mpr hgi
    · rw [hfg]
      change |∫ y, g (e y) ∂(Measure.pi fun _ : Fin (m + 1) => ρ)| ≤ _
      rw [hmp.integral_comp' g, hval]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      unfold rowEnvelope
      refine Finset.sum_le_sum fun i hi' => ?_
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
      have hw : |∫ x, a x ^ i ∂ρ| ≤ rowWeight b i := by
        rcases i with _ | _ | i
        · simp [rowWeight]
        · simp [rowWeight, a, h0 0]
        · refine (abs_integral_le_integral_abs).trans ?_
          simpa only [abs_pow, a, rowWeight] using hB 0 (i + 2) (by omega) (by omega)
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hw (ihψ (k - i) (by omega)).2 (abs_nonneg _)
          (rowWeight_nonneg hb i)) (Nat.cast_nonneg _)

/-- Even orders have a nonnegative power, so the same envelope bounds the moment. -/
theorem centred_rows_even {m p : ℕ} {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    (φ : Fin m → X → ℝ) (hm : ∀ j, Measurable (φ j))
    (hi : ∀ j k, k ≤ 2 * p → Integrable (fun x => φ j x ^ k) ρ)
    (h0 : ∀ j, ∫ x, φ j x ∂ρ = 0)
    (hB : ∀ j k, 2 ≤ k → k ≤ 2 * p → ∫ x, |φ j x| ^ k ∂ρ ≤ b k) :
    ∫⁻ y, ENNReal.ofReal ((∑ j, φ j (y j)) ^ (2 * p))
      ∂(Measure.pi fun _ : Fin m => ρ) ≤ ENNReal.ofReal (rowEnvelope b m (2 * p)) := by
  obtain ⟨hI, hM⟩ := centred_rows_moment ρ hb (2 * p) m φ hm hi h0 hB (2 * p) le_rfl
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun y => (Even.pow_nonneg ⟨p, by omega⟩ _))]
  exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hM)

#print axioms centred_rows_moment
#print axioms centred_rows_even
end BstLean.Part213
