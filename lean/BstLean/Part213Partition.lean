import BstLean.Part213Rows

/-! Finite-order singleton-free partition majorants for RA16.
These polynomials bound row assignments; they do not assert the exact
falling-factorial correction reserved for S32. -/
namespace BstLean.Part213
open MeasureTheory ProbabilityTheory Real

/-- Partition polynomials through order sixteen. -/
noncomputable def partitionBound (x : ℝ) : ℕ → ℝ
  | 0 => 1 * x ^ 0
  | 1 => 0
  | 2 => 1 * x ^ 1
  | 3 => 1 * x ^ 1
  | 4 => 1 * x ^ 1 + 3 * x ^ 2
  | 5 => 1 * x ^ 1 + 10 * x ^ 2
  | 6 => 1 * x ^ 1 + 25 * x ^ 2 + 15 * x ^ 3
  | 7 => 1 * x ^ 1 + 56 * x ^ 2 + 105 * x ^ 3
  | 8 => 1 * x ^ 1 + 119 * x ^ 2 + 490 * x ^ 3 + 105 * x ^ 4
  | 9 => 1 * x ^ 1 + 246 * x ^ 2 + 1918 * x ^ 3 + 1260 * x ^ 4
  | 10 => 1 * x ^ 1 + 501 * x ^ 2 + 6825 * x ^ 3 + 9450 * x ^ 4 + 945 * x ^ 5
  | 11 => 1 * x ^ 1 + 1012 * x ^ 2 + 22935 * x ^ 3 + 56980 * x ^ 4 + 17325 * x ^ 5
  | 12 => 1 * x ^ 1 + 2035 * x ^ 2 + 74316 * x ^ 3 + 302995 * x ^ 4 + 190575 * x ^ 5 + 10395 * x ^ 6
  | 13 => 1 * x ^ 1 + 4082 * x ^ 2 + 235092 * x ^ 3 + 1487200 * x ^ 4 + 1636635 * x ^ 5 + 270270 * x ^ 6
  | 14 => 1 * x ^ 1 + 8177 * x ^ 2 + 731731 * x ^ 3 + 6914908 * x ^ 4 + 12122110 * x ^ 5 + 4099095 * x ^ 6 + 135135 * x ^ 7
  | 15 => 1 * x ^ 1 + 16368 * x ^ 2 + 2252341 * x ^ 3 + 30950920 * x ^ 4 + 81431350 * x ^ 5 + 47507460 * x ^ 6 + 4729725 * x ^ 7
  | 16 => 1 * x ^ 1 + 32751 * x ^ 2 + 6879678 * x ^ 3 + 134779645 * x ^ 4 + 510880370 * x ^ 5 + 466876410 * x ^ 6 + 94594500 * x ^ 7 + 2027025 * x ^ 8
  | _ => 0

lemma partitionBound_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ partitionBound x k := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp [partitionBound] <;> positivity

/-- Adding one centred row preserves the partition polynomial upper bound. -/
lemma partitionBound_step {k : ℕ} (hk : k ≤ 16) {x : ℝ} (hx : 0 ≤ x) :
    ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * rowWeight (fun _ => 1) i *
      partitionBound x (k - i) ≤ partitionBound (x + 1) k := by
  lift x to NNReal using hx
  interval_cases k <;>
    simp [Finset.sum_range_succ, partitionBound, rowWeight, Nat.choose] <;>
    (rw [← sub_nonneg]; ring_nf; positivity)

/-- There are at most k/2 nonsingleton blocks. -/
lemma partitionBound_upper {k : ℕ} (hk : k ≤ 16) {x : ℝ} (hx : 1 ≤ x) :
    partitionBound x k ≤ partitionBound 1 k * x ^ (k / 2) := by
  interval_cases k
  · simp [partitionBound]
  · simp [partitionBound]
  · simp [partitionBound]
  · simp [partitionBound]
  · have h1 : x ^ 1 ≤ x ^ 2 := pow_le_pow_right₀ hx (by decide)
    simp only [partitionBound, one_pow] 
    nlinarith only [h1]
  · have h1 : x ^ 1 ≤ x ^ 2 := pow_le_pow_right₀ hx (by decide)
    simp only [partitionBound, one_pow] 
    nlinarith only [h1]
  · have h1 : x ^ 1 ≤ x ^ 3 := pow_le_pow_right₀ hx (by decide)
    have h2 : x ^ 2 ≤ x ^ 3 := pow_le_pow_right₀ hx (by decide)
    simp only [partitionBound, one_pow] 
    nlinarith only [h1, h2]
  · have h1 : x ^ 1 ≤ x ^ 3 := pow_le_pow_right₀ hx (by decide)
    have h2 : x ^ 2 ≤ x ^ 3 := pow_le_pow_right₀ hx (by decide)
    simp only [partitionBound, one_pow] 
    nlinarith only [h1, h2]
  · have h1 : x ^ 1 ≤ x ^ 4 := pow_le_pow_right₀ hx (by decide)
    have h2 : x ^ 2 ≤ x ^ 4 := pow_le_pow_right₀ hx (by decide)
    have h3 : x ^ 3 ≤ x ^ 4 := pow_le_pow_right₀ hx (by decide)
    simp only [partitionBound, one_pow] 
    nlinarith only [h1, h2, h3]
  · have h1 : x ^ 1 ≤ x ^ 4 := pow_le_pow_right₀ hx (by decide)
    have h2 : x ^ 2 ≤ x ^ 4 := pow_le_pow_right₀ hx (by decide)
    have h3 : x ^ 3 ≤ x ^ 4 := pow_le_pow_right₀ hx (by decide)
    simp only [partitionBound, one_pow] 
    nlinarith only [h1, h2, h3]
  · have h1 : x ^ 1 ≤ x ^ 5 := pow_le_pow_right₀ hx (by decide)
    have h2 : x ^ 2 ≤ x ^ 5 := pow_le_pow_right₀ hx (by decide)
    have h3 : x ^ 3 ≤ x ^ 5 := pow_le_pow_right₀ hx (by decide)
    have h4 : x ^ 4 ≤ x ^ 5 := pow_le_pow_right₀ hx (by decide)
    simp only [partitionBound, one_pow] 
    nlinarith only [h1, h2, h3, h4]
  · have h1 : x ^ 1 ≤ x ^ 5 := pow_le_pow_right₀ hx (by decide)
    have h2 : x ^ 2 ≤ x ^ 5 := pow_le_pow_right₀ hx (by decide)
    have h3 : x ^ 3 ≤ x ^ 5 := pow_le_pow_right₀ hx (by decide)
    have h4 : x ^ 4 ≤ x ^ 5 := pow_le_pow_right₀ hx (by decide)
    simp only [partitionBound, one_pow] 
    nlinarith only [h1, h2, h3, h4]
  · have h1 : x ^ 1 ≤ x ^ 6 := pow_le_pow_right₀ hx (by decide)
    have h2 : x ^ 2 ≤ x ^ 6 := pow_le_pow_right₀ hx (by decide)
    have h3 : x ^ 3 ≤ x ^ 6 := pow_le_pow_right₀ hx (by decide)
    have h4 : x ^ 4 ≤ x ^ 6 := pow_le_pow_right₀ hx (by decide)
    have h5 : x ^ 5 ≤ x ^ 6 := pow_le_pow_right₀ hx (by decide)
    simp only [partitionBound, one_pow] 
    nlinarith only [h1, h2, h3, h4, h5]
  · have h1 : x ^ 1 ≤ x ^ 6 := pow_le_pow_right₀ hx (by decide)
    have h2 : x ^ 2 ≤ x ^ 6 := pow_le_pow_right₀ hx (by decide)
    have h3 : x ^ 3 ≤ x ^ 6 := pow_le_pow_right₀ hx (by decide)
    have h4 : x ^ 4 ≤ x ^ 6 := pow_le_pow_right₀ hx (by decide)
    have h5 : x ^ 5 ≤ x ^ 6 := pow_le_pow_right₀ hx (by decide)
    simp only [partitionBound, one_pow] 
    nlinarith only [h1, h2, h3, h4, h5]
  · have h1 : x ^ 1 ≤ x ^ 7 := pow_le_pow_right₀ hx (by decide)
    have h2 : x ^ 2 ≤ x ^ 7 := pow_le_pow_right₀ hx (by decide)
    have h3 : x ^ 3 ≤ x ^ 7 := pow_le_pow_right₀ hx (by decide)
    have h4 : x ^ 4 ≤ x ^ 7 := pow_le_pow_right₀ hx (by decide)
    have h5 : x ^ 5 ≤ x ^ 7 := pow_le_pow_right₀ hx (by decide)
    have h6 : x ^ 6 ≤ x ^ 7 := pow_le_pow_right₀ hx (by decide)
    simp only [partitionBound, one_pow] 
    nlinarith only [h1, h2, h3, h4, h5, h6]
  · have h1 : x ^ 1 ≤ x ^ 7 := pow_le_pow_right₀ hx (by decide)
    have h2 : x ^ 2 ≤ x ^ 7 := pow_le_pow_right₀ hx (by decide)
    have h3 : x ^ 3 ≤ x ^ 7 := pow_le_pow_right₀ hx (by decide)
    have h4 : x ^ 4 ≤ x ^ 7 := pow_le_pow_right₀ hx (by decide)
    have h5 : x ^ 5 ≤ x ^ 7 := pow_le_pow_right₀ hx (by decide)
    have h6 : x ^ 6 ≤ x ^ 7 := pow_le_pow_right₀ hx (by decide)
    simp only [partitionBound, one_pow] 
    nlinarith only [h1, h2, h3, h4, h5, h6]
  · have h1 : x ^ 1 ≤ x ^ 8 := pow_le_pow_right₀ hx (by decide)
    have h2 : x ^ 2 ≤ x ^ 8 := pow_le_pow_right₀ hx (by decide)
    have h3 : x ^ 3 ≤ x ^ 8 := pow_le_pow_right₀ hx (by decide)
    have h4 : x ^ 4 ≤ x ^ 8 := pow_le_pow_right₀ hx (by decide)
    have h5 : x ^ 5 ≤ x ^ 8 := pow_le_pow_right₀ hx (by decide)
    have h6 : x ^ 6 ≤ x ^ 8 := pow_le_pow_right₀ hx (by decide)
    have h7 : x ^ 7 ≤ x ^ 8 := pow_le_pow_right₀ hx (by decide)
    simp only [partitionBound, one_pow] 
    nlinarith only [h1, h2, h3, h4, h5, h6, h7]

lemma partitionBound_eight : partitionBound 1 8 = 715 := by norm_num [partitionBound]
lemma partitionBound_sixteen : partitionBound 1 16 = 1216070380 := by
  norm_num [partitionBound]

/-- The general binomial envelope is below the partition bound through order sixteen. -/
theorem rowEnvelope_partition (m : ℕ) {k : ℕ} (hk : k ≤ 16) :
    rowEnvelope (fun _ => 1) m k ≤ partitionBound (m : ℝ) k := by
  induction m generalizing k with
  | zero =>
    interval_cases k <;> norm_num [rowEnvelope, partitionBound]
  | succ m ih =>
    rw [rowEnvelope]
    calc
      _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * rowWeight (fun _ => 1) i *
          partitionBound (m : ℝ) (k - i) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (ih (by omega : k - i ≤ 16))
          (mul_nonneg (Nat.cast_nonneg _) (rowWeight_nonneg (fun _ => by norm_num) i))
      _ ≤ partitionBound (m + 1 : ℕ) k := by
        simpa only [Nat.cast_succ] using partitionBound_step hk (Nat.cast_nonneg m)

/-- Scaling each row scales the entire moment by the same power. -/
theorem rowEnvelope_scale {B : ℝ} (hB : 0 ≤ B) (m k : ℕ) :
    rowEnvelope (fun i => B ^ i) m k = B ^ k * rowEnvelope (fun _ => 1) m k := by
  induction m generalizing k with
  | zero => by_cases hk : k = 0 <;> simp [rowEnvelope, hk]
  | succ m ih =>
    rw [rowEnvelope, rowEnvelope, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [ih]
    have hw : rowWeight (fun i => B ^ i) i = B ^ i * rowWeight (fun _ => 1) i := by
      rcases i with _ | _ | i <;> simp [rowWeight]
    rw [hw]
    have hp : B ^ i * B ^ (k - i) = B ^ k := by rw [← pow_add, Nat.add_sub_of_le hik]
    calc
      _ = (k.choose i : ℝ) * rowWeight (fun _ => 1) i *
          (B ^ i * B ^ (k - i)) * rowEnvelope (fun _ => 1) m (k - i) := by ring
      _ = _ := by rw [hp]; ring

/-- This is the paper's nonsingleton row-sum factor through order sixteen. -/
theorem centred_rows_partition16 {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) [IsProbabilityMeasure ρ] {m p : ℕ}
    (hm : 1 ≤ m) (hp : 2 * p ≤ 16) {B : ℝ} (hB : 0 ≤ B)
    (φ : Fin m → X → ℝ) (hφ : ∀ j, Measurable (φ j))
    (hi : ∀ j k, k ≤ 2 * p → Integrable (fun x => φ j x ^ k) ρ)
    (h0 : ∀ j, ∫ x, φ j x ∂ρ = 0)
    (hM : ∀ j k, 2 ≤ k → k ≤ 2 * p → ∫ x, |φ j x| ^ k ∂ρ ≤ B ^ k) :
    ∫⁻ y, ENNReal.ofReal ((∑ j, φ j (y j)) ^ (2 * p))
      ∂(Measure.pi fun _ : Fin m => ρ) ≤
      ENNReal.ofReal (partitionBound 1 (2 * p) * (m : ℝ) ^ p * B ^ (2 * p)) := by
  refine (centred_rows_even ρ (fun k => pow_nonneg hB k) φ hφ hi h0 hM).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [rowEnvelope_scale hB]
  have h1 := rowEnvelope_partition m hp
  have h2 := partitionBound_upper hp (show (1 : ℝ) ≤ m by exact_mod_cast hm)
  rw [show 2 * p / 2 = p by omega] at h2
  calc
    B ^ (2 * p) * rowEnvelope (fun _ => 1) m (2 * p)
      ≤ B ^ (2 * p) * (partitionBound 1 (2 * p) * (m : ℝ) ^ p) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (pow_nonneg hB _)
    _ = _ := by ring

#print axioms partitionBound_step
#print axioms rowEnvelope_partition
#print axioms centred_rows_partition16
end BstLean.Part213
