import BstLean.Part56Low_Heat
import BstLean.Part53Floor_Correction

namespace BstLean.Part56.LowCoefficients

open BstLean.Part41 BstLean.Part53 BstLean.Part53.FloorHeat

variable {n : ℕ}

noncomputable def normSum (k : ℕ) (A : Tens n) : ℝ :=
  ∑ c ∈ Finset.Icc 1 k, frob (A c)

noncomputable def weightBound (d k : ℕ) : ℝ :=
  1 + ∑ c ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k + 1),
    heatWeight c i ((d : ℝ) + 1) ^ 2

lemma normSum_nonneg (k : ℕ) (A : Tens n) : 0 ≤ normSum k A := by
  classical
  exact Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun w _ => sq_nonneg _

lemma weightBound_pos (d k : ℕ) : 0 < weightBound d k := by
  have h : 0 ≤ ∑ c ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k + 1),
      heatWeight c i ((d : ℝ) + 1) ^ 2 :=
    Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun i _ => sq_nonneg _
  unfold weightBound
  linarith

lemma weight_le_bound (d k c i : ℕ) (hc : c ≤ k) (hi : i ≤ k)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ (d : ℝ) + 1) :
    heatWeight c i (-v) ^ 2 ≤ weightBound d k := by
  classical
  have hpow : (-v) ^ (2 * i) = v ^ (2 * i) := by
    rw [pow_mul, pow_mul]
    simp
  have hw : heatWeight c i (-v) ^ 2 ≤ heatWeight c i ((d : ℝ) + 1) ^ 2 := by
    rw [FloorCorrection.heatWeight_sq, FloorCorrection.heatWeight_sq, hpow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv0 hv1 _)
      (sq_nonneg _)
  have hi' := Finset.single_le_sum (s := Finset.range (k + 1))
    (fun j _ => sq_nonneg (heatWeight c j ((d : ℝ) + 1))) (show i ∈ Finset.range (k + 1) by simp; omega)
  have hc' := Finset.single_le_sum (s := Finset.range (k + 1))
    (f := fun j => ∑ i ∈ Finset.range (k + 1), heatWeight j i ((d : ℝ) + 1) ^ 2)
    (fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg _)
    (show c ∈ Finset.range (k + 1) by simp; omega)
  unfold weightBound
  linarith

lemma coefficient_le_sum (k c : ℕ) (hc0 : 1 ≤ c) (hc1 : c ≤ k) (A : Tens n) :
    frob (A c) ≤ normSum k A := by
  classical
  unfold normSum
  exact Finset.single_le_sum (f := fun j => frob (A j))
    (fun j _ => Finset.sum_nonneg fun w _ => sq_nonneg _)
    (show c ∈ Finset.Icc 1 k by simp [hc0, hc1])

lemma inverse_coefficient_bound (d k c : ℕ) (hn : 1 ≤ n) (hc0 : 1 ≤ c) (hc1 : c ≤ k)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ (d : ℝ) + 1) (A : Tens n) :
    frob (A c) ≤ (k + 1 : ℝ) ^ 2 * weightBound d k *
      (n : ℝ) ^ ((k - 1) / 2) * normSum k (heatA k v A) := by
  classical
  let S := (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)
  let B := heatA k v A
  have hW := (weightBound_pos d k).le
  let R := weightBound d k * (n : ℝ) ^ ((k - 1) / 2) * normSum k B
  have hR : 0 ≤ R := by
    exact mul_nonneg (mul_nonneg (weightBound_pos d k).le (by positivity)) (normSum_nonneg k B)
  have hterm (i : ℕ) (hi : i ∈ S) :
      heatWeight c i (-v) ^ 2 * (n : ℝ) ^ i * frob (B (c + 2 * i)) ≤ R := by
    have his := Finset.mem_filter.mp hi
    have hik : i ≤ k := by have := Finset.mem_range.mp his.1; omega
    have hw := weight_le_bound d k c i hc1 hik v hv0 hv1
    have hd := inverse_heat_dimension_bound56 hn k c i hc0 his.2
    have hf := coefficient_le_sum k (c + 2 * i) (by omega) his.2 B
    exact mul_le_mul (mul_le_mul hw hd (by positivity) (weightBound_pos d k).le) hf
      (Finset.sum_nonneg fun w _ => sq_nonneg _) (by positivity)
  calc
    frob (A c) ≤ (k + 1 : ℝ) * ∑ i ∈ S,
        heatWeight c i (-v) ^ 2 * (n : ℝ) ^ i * frob (B (c + 2 * i)) :=
      inverse_heat_frob_bound56 k c hc1 v A
    _ ≤ (k + 1 : ℝ) * ∑ i ∈ S, R := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _ ≤ (k + 1 : ℝ) * ∑ i ∈ Finset.range (k + 1), R := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => hR)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; dsimp [R, B]; ring

lemma inverse_normSum_bound (d k : ℕ) (hn : 1 ≤ n) (v : ℝ)
    (hv0 : 0 ≤ v) (hv1 : v ≤ (d : ℝ) + 1) (A : Tens n) :
    normSum k A ≤ (k + 1 : ℝ) ^ 3 * weightBound d k *
      (n : ℝ) ^ ((k - 1) / 2) * normSum k (heatA k v A) := by
  classical
  have hW := (weightBound_pos d k).le
  let R := (k + 1 : ℝ) ^ 2 * weightBound d k *
      (n : ℝ) ^ ((k - 1) / 2) * normSum k (heatA k v A)
  have hR : 0 ≤ R := mul_nonneg (by positivity) (normSum_nonneg _ _)
  have hsubset : Finset.Icc 1 k ⊆ Finset.range (k + 1) := by intro c hc; simp only [Finset.mem_Icc] at hc; simp; omega
  calc
    _ ≤ ∑ c ∈ Finset.Icc 1 k, R := by
      apply Finset.sum_le_sum
      intro c hc
      exact inverse_coefficient_bound d k c hn (Finset.mem_Icc.mp hc).1
        (Finset.mem_Icc.mp hc).2 v hv0 hv1 A
    _ ≤ ∑ c ∈ Finset.range (k + 1), R :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => hR)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; dsimp [R]; ring


end BstLean.Part56.LowCoefficients
