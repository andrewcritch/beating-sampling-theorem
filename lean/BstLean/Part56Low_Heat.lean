import BstLean.Part56Defs
import BstLean.Part53Floor_Heat
import BstLean.Part53Error_Heat
import BstLean.Part53Elem

namespace BstLean.Part56

open BstLean.Part41 (Tens frob)
open BstLean.Part53 (heatA)
open BstLean.Part53.FloorHeat

variable {n : ℕ}

lemma inverse_heat56 (k c : ℕ) (hc : c ≤ k) (v : ℝ) (A : Tens n) :
    heatA k (-v) (heatA k v A) c = A c := by
  rw [heatA_add, neg_add_cancel, BstLean.Part53.error53_heat_zero k c hc]

lemma heat_frob_bound56 (k c : ℕ) (v : ℝ) (A : Tens n) :
    frob (heatA k v A c) ≤
      (k + 1 : ℝ) * ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
        heatWeight c i v ^ 2 * (n : ℝ) ^ i * frob (A (c + 2 * i)) := by
  classical
  let S := (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)
  have hcard : (S.card : ℝ) ≤ k + 1 := by
    have hh : S.card ≤ (Finset.range (k + 1)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    simpa using (Nat.cast_le (α := ℝ)).mpr hh
  have hsq (z : Fin c → Fin n) :
      (heatA k v A c z) ^ 2 ≤
        (k + 1 : ℝ) * ∑ i ∈ S, (heatWeight c i v * traceFamily i A c z) ^ 2 := by
    change (∑ i ∈ S, heatWeight c i v * traceFamily i A c z) ^ 2 ≤ _
    have hh := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ))
      (fun i => heatWeight c i v * traceFamily i A c z)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hcard
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  calc
    _ ≤ ∑ z : Fin c → Fin n,
        (k + 1 : ℝ) * ∑ i ∈ S, (heatWeight c i v * traceFamily i A c z) ^ 2 :=
      Finset.sum_le_sum (fun z _ => hsq z)
    _ = (k + 1 : ℝ) * ∑ i ∈ S, heatWeight c i v ^ 2 * frob (traceFamily i A c) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [mul_pow, ← Finset.mul_sum]
      rfl
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      rw [traceFamily_frob]
      have hh := BstLean.Part53.lemmaTr53 n (c + 2 * i) i (A (c + 2 * i)) (by omega)
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hh (sq_nonneg (heatWeight c i v))

lemma inverse_heat_frob_bound56 (k c : ℕ) (hc : c ≤ k) (v : ℝ) (A : Tens n) :
    frob (A c) ≤
      (k + 1 : ℝ) * ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
        heatWeight c i (-v) ^ 2 * (n : ℝ) ^ i * frob (heatA k v A (c + 2 * i)) := by
  simpa only [inverse_heat56 k c hc v A] using
    heat_frob_bound56 k c (-v) (heatA k v A)

lemma inverse_heat_dimension_bound56 (hn : 1 ≤ n) (k c i : ℕ)
    (hc : 1 ≤ c) (hi : c + 2 * i ≤ k) :
    (n : ℝ) ^ i ≤ (n : ℝ) ^ ((k - 1) / 2) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact pow_le_pow_right₀ hnR (by omega)

end BstLean.Part56
