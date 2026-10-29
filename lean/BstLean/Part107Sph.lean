import BstLean.Part107Defs

/-!
# Part 107: the statistics of `t = u·u′` on the sphere (`SphStat107`)
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

/-- The two-fold sphere average of `f(u·u′)` is at most the moment sum of a polynomial that
dominates `f` on `[−1, 1]`. -/
lemma sph_outer (N : ℕ) (hN : 1 ≤ N) (f : ℝ → ℝ) (hf0 : ∀ t, 0 ≤ f t) (b : ℕ → ℝ) (K : ℕ)
    (hfb : ∀ t : ℝ, |t| ≤ 1 → f t ≤ ∑ k ∈ Finset.range K, b k * t ^ k) :
    ∫ u, ∫ u', f (dot u u') ∂uniformSphere N ∂uniformSphere N ≤
      ∑ k ∈ Finset.range K, b k * sphMom N k := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  have hin : ∀ᵐ u ∂uniformSphere N,
      ∫ u', f (dot u u') ∂uniformSphere N ≤ ∑ k ∈ Finset.range K, b k * sphMom N k := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere N] with u hu
    have hu1 : dot u u = 1 := by rw [dot_self_eq, hu]
    have hI : Integrable (fun u' => ∑ k ∈ Finset.range K, b k * dot u u' ^ k)
        (uniformSphere N) :=
      integrable_finsetSum _ fun k _ => (integrable_dot_pow N hN u k).const_mul _
    calc ∫ u', f (dot u u') ∂uniformSphere N
        ≤ ∫ u', ∑ k ∈ Finset.range K, b k * dot u u' ^ k ∂uniformSphere N := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => hf0 _) hI ?_
          filter_upwards [BstLean.Part29.uniformSphere_ae_sphere N] with u' hu'
          exact hfb _ (abs_dot_le_one u u' hu1 (by rw [dot_self_eq, hu']))
      _ = ∑ k ∈ Finset.range K, b k * sphMom N k := by
          rw [integral_finsetSum _ fun k _ => (integrable_dot_pow N hN u k).const_mul _]
          simp_rw [integral_const_mul, sphere_dot_pow N hN u hu1]
  calc ∫ u, ∫ u', f (dot u u') ∂uniformSphere N ∂uniformSphere N
      ≤ ∫ _u, (∑ k ∈ Finset.range K, b k * sphMom N k) ∂uniformSphere N :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => hf0 _)
          (integrable_const _) hin
    _ = ∑ k ∈ Finset.range K, b k * sphMom N k := by simp

lemma pow_le_four {t : ℝ} (ht : |t| ≤ 1) (j : ℕ) : t ^ (4 + 2 * j) ≤ t ^ 4 := by
  have h2 : t ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one t).mpr ht
  rw [pow_add, pow_mul]
  have : (t ^ 2) ^ j ≤ 1 := pow_le_one₀ (sq_nonneg t) h2
  nlinarith [pow_nonneg (sq_nonneg t) 2, show t ^ 4 = (t ^ 2) ^ 2 by ring]

lemma sphMom_two (N : ℕ) : sphMom N 2 = 1 / (N : ℝ) := by
  simp only [sphMom, BstLean.Part29.gaussMom, BstLean.Part36.rhoD]
  norm_num [Finset.prod_range_succ, Nat.doubleFactorial, Nat.even_iff]

lemma sphMom_four (N : ℕ) : sphMom N 4 = 3 / ((N : ℝ) * ((N : ℝ) + 2)) := by
  simp only [sphMom, BstLean.Part29.gaussMom, BstLean.Part36.rhoD]
  norm_num [Finset.prod_range_succ, Nat.doubleFactorial, Nat.even_iff]

lemma sphMom_zero (N : ℕ) : sphMom N 0 = 1 := by
  simp [sphMom, BstLean.Part29.gaussMom, BstLean.Part36.rhoD]

lemma sphMom_odd (N j : ℕ) (hj : ¬ Even j) : sphMom N j = 0 := by
  simp [sphMom, hj]

/-- The moment sum of a polynomial with even part `c₀ + c₂ t² + c₄ t⁴`. -/
lemma momsum (N : ℕ) (b : ℕ → ℝ) (K : ℕ) (hK : 5 ≤ K)
    (hev : ∀ k, 5 ≤ k → k < K → Even k → b k = 0) :
    ∑ k ∈ Finset.range K, b k * sphMom N k =
      b 0 + b 2 * (1 / (N : ℝ)) + b 4 * (3 / ((N : ℝ) * ((N : ℝ) + 2))) := by
  have hz : ∀ k ∈ Finset.range K, k ∉ ({0, 2, 4} : Finset ℕ) → b k * sphMom N k = 0 := by
    intro k hkK hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    by_cases he : Even k
    · have : 5 ≤ k := by
        rcases he with ⟨m, rfl⟩
        omega
      rw [hev k this (Finset.mem_range.mp hkK) he, zero_mul]
    · rw [sphMom_odd N k he, mul_zero]
  have hsub : ({0, 2, 4} : Finset ℕ) ⊆ Finset.range K := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_subset hsub hz]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    sphMom_zero, sphMom_two, sphMom_four]
  ring

/-- The coefficient lists. -/
noncomputable def bl (l : List ℝ) (c : ℝ) (k : ℕ) : ℝ := l.getD k 0 / c

theorem sphStat107 : SphStat107 := by
  intro N dA hN hdA
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨?_, ?_, ?_⟩
  · rcases hdA with rfl | rfl
    · refine (sph_outer N hN (fun t => rW (2 * 3) t ^ 2) (fun _ => sq_nonneg _)
        (bl [1, 2, 3, 4, 21, 6, 0, 6, 0, 4, 0, 2, 0] 49) 13 ?_).trans ?_
      · intro t ht
        have h0 := pow_le_four ht 1
        have h1 := pow_le_four ht 2
        have h2 := pow_le_four ht 3
        have h3 := pow_le_four ht 4
        simp only [rW, bl, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_zero,
          List.getD_cons_succ] at *
        norm_num at *
        rw [div_pow]
        have key : (1 + t + t ^ 2 + t ^ 3 + t ^ 4 + t ^ 5 + t ^ 6) ^ 2 =
            1 + 2 * t + 3 * t ^ 2 + 4 * t ^ 3 + 5 * t ^ 4 + 6 * t ^ 5 + 7 * t ^ 6 + 6 * t ^ 7 +
              5 * t ^ 8 + 4 * t ^ 9 + 3 * t ^ 10 + 2 * t ^ 11 + t ^ 12 := by ring
        rw [key]
        linarith
      · rw [momsum N _ 13 (by norm_num) (by
          intro k h5 hK he
          interval_cases k <;> first | (exfalso; revert he; decide) | simp [bl])]
        simp only [bl, delN, Sof, List.getD_cons_zero, List.getD_cons_succ]
        norm_num
        apply le_of_eq
        field_simp
        ring
    · refine (sph_outer N hN (fun t => rW (2 * 4) t ^ 2) (fun _ => sq_nonneg _)
        (bl [1, 2, 3, 4, 37, 6, 0, 8, 0, 8, 0, 6, 0, 4, 0, 2, 0] 81) 17 ?_).trans ?_
      · intro t ht
        have h0 := pow_le_four ht 1
        have h1 := pow_le_four ht 2
        have h2 := pow_le_four ht 3
        have h3 := pow_le_four ht 4
        have h4 := pow_le_four ht 5
        have h5 := pow_le_four ht 6
        simp only [rW, bl, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_zero,
          List.getD_cons_succ] at *
        norm_num at *
        rw [div_pow]
        have key : (1 + t + t ^ 2 + t ^ 3 + t ^ 4 + t ^ 5 + t ^ 6 + t ^ 7 + t ^ 8) ^ 2 =
            1 + 2 * t + 3 * t ^ 2 + 4 * t ^ 3 + 5 * t ^ 4 + 6 * t ^ 5 + 7 * t ^ 6 + 8 * t ^ 7 +
              9 * t ^ 8 + 8 * t ^ 9 + 7 * t ^ 10 + 6 * t ^ 11 + 5 * t ^ 12 + 4 * t ^ 13 +
              3 * t ^ 14 + 2 * t ^ 15 + t ^ 16 := by ring
        rw [key]
        linarith
      · rw [momsum N _ 17 (by norm_num) (by
          intro k h5 hK he
          interval_cases k <;> first | (exfalso; revert he; decide) | simp [bl])]
        simp only [bl, delN, Sof, List.getD_cons_zero, List.getD_cons_succ]
        norm_num
        apply le_of_eq
        field_simp
        ring
  · have gen : ∀ a c : ℝ, 0 < a → 0 < c →
        1 / 49 * a + 17 / 49 * (3 * c) ≤ (3 * a + 63 * c) / 49 ∧
        1 / 81 * a + 31 / 81 * (3 * c) ≤ (3 * a + 111 * c) / 81 := by
      intro a c ha hc
      constructor <;> linarith
    rcases hdA with rfl | rfl
    · refine (sph_outer N hN (fun t => (rW (2 * 3) t - 1 / (2 * ((3 : ℕ) : ℝ) + 1)) ^ 2)
        (fun _ => sq_nonneg _)
        (bl [0, 0, 1, 2, 17, 4, 0, 6, 0, 4, 0, 2, 0] 49) 13 ?_).trans ?_
      · intro t ht
        have h0 := pow_le_four ht 1
        have h1 := pow_le_four ht 2
        have h2 := pow_le_four ht 3
        have h3 := pow_le_four ht 4
        simp only [rW, bl, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_zero,
          List.getD_cons_succ] at *
        norm_num at *
        rw [← sub_div, div_pow]
        have key : (1 + t + t ^ 2 + t ^ 3 + t ^ 4 + t ^ 5 + t ^ 6 - 1) ^ 2 =
            t ^ 2 + 2 * t ^ 3 + 3 * t ^ 4 + 4 * t ^ 5 + 5 * t ^ 6 + 6 * t ^ 7 +
              5 * t ^ 8 + 4 * t ^ 9 + 3 * t ^ 10 + 2 * t ^ 11 + t ^ 12 := by ring
        rw [key]
        linarith
      · rw [momsum N _ 13 (by norm_num) (by
          intro k h5 hK he
          interval_cases k <;> first | (exfalso; revert he; decide) | simp [bl])]
        simp only [bl, delN, Sof, List.getD_cons_zero, List.getD_cons_succ]
        norm_num
        have h := gen ((N : ℝ)⁻¹) (((N : ℝ) * ((N : ℝ) + 2))⁻¹) (by positivity) (by positivity)
        convert h.1 using 1 <;> ring
    · refine (sph_outer N hN (fun t => (rW (2 * 4) t - 1 / (2 * ((4 : ℕ) : ℝ) + 1)) ^ 2)
        (fun _ => sq_nonneg _)
        (bl [0, 0, 1, 2, 31, 4, 0, 6, 0, 8, 0, 6, 0, 4, 0, 2, 0] 81) 17 ?_).trans ?_
      · intro t ht
        have h0 := pow_le_four ht 1
        have h1 := pow_le_four ht 2
        have h2 := pow_le_four ht 3
        have h3 := pow_le_four ht 4
        have h4 := pow_le_four ht 5
        have h5 := pow_le_four ht 6
        simp only [rW, bl, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_zero,
          List.getD_cons_succ] at *
        norm_num at *
        rw [← sub_div, div_pow]
        have key : (1 + t + t ^ 2 + t ^ 3 + t ^ 4 + t ^ 5 + t ^ 6 + t ^ 7 + t ^ 8 - 1) ^ 2 =
            t ^ 2 + 2 * t ^ 3 + 3 * t ^ 4 + 4 * t ^ 5 + 5 * t ^ 6 + 6 * t ^ 7 + 7 * t ^ 8 +
              8 * t ^ 9 + 7 * t ^ 10 + 6 * t ^ 11 + 5 * t ^ 12 + 4 * t ^ 13 +
              3 * t ^ 14 + 2 * t ^ 15 + t ^ 16 := by ring
        rw [key]
        linarith
      · rw [momsum N _ 17 (by norm_num) (by
          intro k h5 hK he
          interval_cases k <;> first | (exfalso; revert he; decide) | simp [bl])]
        simp only [bl, delN, Sof, List.getD_cons_zero, List.getD_cons_succ]
        norm_num
        have h := gen ((N : ℝ)⁻¹) (((N : ℝ) * ((N : ℝ) + 2))⁻¹) (by positivity) (by positivity)
        convert h.2 using 1 <;> ring
  · refine (sph_outer N hN (fun t => if 1 / 10 < |t| then (1 : ℝ) else 0)
      (fun t => by split_ifs <;> norm_num) (fun k => if k = 16 then 10 ^ 16 else 0) 17 ?_).trans ?_
    · intro t _
      rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun k hk => by
        have := Finset.mem_range.mp hk
        simp [show k ≠ 16 by omega])]
      simp only [ite_true, zero_add]
      split_ifs with h
      · have h1 : (1 : ℝ) < 10 * |t| := by linarith
        have h2 : (1 : ℝ) ≤ (10 * |t|) ^ 16 := one_le_pow₀ h1.le
        have h3 : (10 * |t|) ^ 16 = 10 ^ 16 * t ^ 16 := by
          rw [mul_pow, (by decide : Even 16).pow_abs t]
        linarith
      · positivity
    · rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun k hk => by
        have := Finset.mem_range.mp hk
        simp [show k ≠ 16 by omega])]
      simp

#print axioms sphStat107

end BstLean.Part107
