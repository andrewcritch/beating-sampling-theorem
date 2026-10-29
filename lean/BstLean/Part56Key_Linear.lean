import BstLean.Part56Key_Normalized

namespace BstLean.Part56

open MeasureTheory BstLean.Part29
open scoped ENNReal

def dot56 {n : ℕ} (a b : Fin n → ℝ) : ℝ := ∑ i, a i * b i

private lemma dot_bound56 {n : ℕ} (a w : Fin n → ℝ) (hw : ∑ i, w i ^ 2 ≤ 1) :
    dot56 a w ^ 2 ≤ ∑ i, a i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a w
  exact h.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hw
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))

private lemma dot_pvec56 {n : ℕ} (v a g : Fin n → ℝ) :
    dot56 a (pvec56 v g) = dot56 (pvec56 v a) g := by
  simp only [dot56, pvec56, mul_sub, sub_mul, Finset.sum_sub_distrib]
  have hL : (∑ x, a x * ((∑ l, v l * g l) * v x)) =
      (∑ l, v l * g l) * ∑ x, a x * v x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hR : (∑ x, (∑ l, v l * a l) * v x * g x) =
      (∑ l, v l * a l) * ∑ x, v x * g x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have h (b : Fin n → ℝ) : (∑ i, b i * v i) = ∑ i, v i * b i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hL, hR, h]
  ring

private lemma linear_second56 {n : ℕ} (a : Fin n → ℝ) :
    (∫ g, dot56 a g ^ 2 ∂stdGauss (Fin n)) = ∑ i, a i ^ 2 := by
  have hm : GaussMoments n (stdGauss (Fin n)) := gaussMoments_std (D := n)
  have he (g : Fin n → ℝ) : dot56 a g ^ 2 =
      ∑ i, ∑ j, (a i * a j) * (g i * g j) := by
    simp only [dot56, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [he]
  rw [integral_finsetSum _ fun i hi => integrable_finsetSum _
    fun j hj => (hm.int2 i j).const_mul _]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ fun j hj => (hm.int2 i j).const_mul _]
  simp only [integral_const_mul, hm.m2]
  simp [pow_two]

private lemma integrable_dot_pvec_sq56 {n : ℕ} (v a : Fin n → ℝ) :
    Integrable (fun g => dot56 a (pvec56 v g) ^ 2) (stdGauss (Fin n)) := by
  convert BstLean.Part48.gauss_poly_integrable ((∑ i,
    MvPolynomial.C (a i) * pvecPoly56 v i) ^ 2) using 1
  funext g
  simp only [map_pow, map_sum, map_mul, MvPolynomial.eval_C, eval_pvecPoly56, dot56]

private lemma integrable_dot_perpDir_sq56 {n : ℕ} (v a : Fin n → ℝ) :
    Integrable (fun g => dot56 a (perpDir v g) ^ 2) (stdGauss (Fin n)) := by
  have hm : Measurable (fun g => dot56 a (perpDir v g)) := by
    unfold dot56
    apply Finset.measurable_sum
    intro i hi
    exact ((measurable_pi_apply i).comp (measurable_perpDir56 v)).const_mul _
  apply Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (∑ i, a i ^ 2)
  filter_upwards [] with g
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact dot_bound56 a _ (perpDir_sq_le_one56 v g)

private lemma bad_radial_bound56 (q N : ℝ) (hN : 0 < N) (hq : q < N / 2) :
    1 ≤ 16 / N ^ 4 * (q - N) ^ 4 := by
  have hs : N / 2 ≤ |q - N| := by rw [abs_of_nonpos (by linarith)]; linarith
  have hp := pow_le_pow_left₀ (show 0 ≤ N / 2 by positivity) hs 4
  rw [pow_abs, div_pow, abs_of_nonneg (show 0 ≤ (q - N) ^ 4 by positivity)] at hp
  norm_num only [show (2 : ℝ) ^ 4 = 16 by norm_num] at hp
  rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hN 4)]
  nlinarith

private lemma dot_perpDir_dom56 {n : ℕ} (v a g : Fin n → ℝ) (N : ℝ) (hN : 0 < N) :
    dot56 a (perpDir v g) ^ 2 ≤ 2 / N * dot56 a (pvec56 v g) ^ 2 +
      ((∑ i, a i ^ 2) * (16 / N ^ 4)) * (qrad56 v g - N) ^ 4 := by
  have hq0 : 0 ≤ qrad56 v g := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have he : dot56 a (perpDir v g) ^ 2 = dot56 a (pvec56 v g) ^ 2 / qrad56 v g := by
    have he' : dot56 a (perpDir v g) = (1 / Real.sqrt (qrad56 v g)) * dot56 a (pvec56 v g) := by
      change (∑ i, a i * ((1 / Real.sqrt (qrad56 v g)) * pvec56 v g i)) = _
      rw [dot56, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [he', mul_pow, div_pow, Real.sq_sqrt hq0, one_pow]
    ring
  by_cases hq : N / 2 ≤ qrad56 v g
  · rw [he]
    have hb : dot56 a (pvec56 v g) ^ 2 / qrad56 v g ≤
        2 / N * dot56 a (pvec56 v g) ^ 2 := by
      rw [div_le_iff₀ (by linarith : 0 < qrad56 v g), div_mul_eq_mul_div,
        div_mul_eq_mul_div, le_div_iff₀ hN]
      nlinarith [mul_le_mul_of_nonneg_right hq (sq_nonneg (dot56 a (pvec56 v g)))]
    exact hb.trans (le_add_of_nonneg_right (by positivity))
  · have hb := mul_le_mul_of_nonneg_left
      (bad_radial_bound56 (qrad56 v g) N hN (lt_of_not_ge hq))
      (Finset.sum_nonneg (s := Finset.univ) (fun i hi => sq_nonneg (a i)))
    have hs := dot_bound56 a _ (perpDir_sq_le_one56 v g)
    simp only [mul_one] at hb
    refine hs.trans (hb.trans ?_)
    calc
      _ = ((∑ i, a i ^ 2) * (16 / N ^ 4)) * (qrad56 v g - N) ^ 4 := by ring
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

theorem perpDir_linear_moment56 : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ a : Fin n → ℝ,
      (∫ g, dot56 a (perpDir v g) ^ 2 ∂stdGauss (Fin n)) ≤
        C / ((n : ℝ) - 1) * ∑ i, a i ^ 2 := by
  obtain ⟨K, hK, hF⟩ := qrad_fourth_exists56
  refine ⟨2 + 64 * K, by positivity, ?_⟩
  intro n hn v hv a
  let N : ℝ := (n : ℝ) - 1
  let R : ℝ := ∑ i, a i ^ 2
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hN1 : 1 ≤ N := by
    dsimp [N]
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hp : (∫ g, dot56 a (pvec56 v g) ^ 2 ∂stdGauss (Fin n)) ≤ R := by
    simp_rw [dot_pvec56]
    rw [linear_second56]
    change (∑ i, (a i - (∑ l, v l * a l) * v i) ^ 2) ≤ R
    rw [perpVec_sq56 v a hv]
    exact sub_le_self _ (sq_nonneg _)
  have hFv := hF n v hv
  change (∫ g, (qrad56 v g - N) ^ 4 ∂stdGauss (Fin n)) ≤ 4 * K * N ^ 2 at hFv
  have hc := integrable_qrad_center_pow56 v 4
  change Integrable (fun g => (qrad56 v g - N) ^ 4) (stdGauss (Fin n)) at hc
  have h := integral_mono (integrable_dot_perpDir_sq56 v a)
    (((integrable_dot_pvec_sq56 v a).const_mul (2 / N)).add (hc.const_mul (R * (16 / N ^ 4))))
    (fun g => dot_perpDir_dom56 v a g N hN)
  simp only [Pi.add_apply] at h
  rw [integral_add (f := fun g => 2 / N * dot56 a (pvec56 v g) ^ 2)
    (g := fun g => (R * (16 / N ^ 4)) * (qrad56 v g - N) ^ 4)
    ((integrable_dot_pvec_sq56 v a).const_mul _) (hc.const_mul _),
    integral_const_mul, integral_const_mul] at h
  have hb : (∫ g, dot56 a (perpDir v g) ^ 2 ∂stdGauss (Fin n)) ≤
      (2 / N + 64 * K / N ^ 2) * R := by
    refine h.trans ?_
    calc
      _ ≤ 2 / N * R + (R * (16 / N ^ 4)) * (4 * K * N ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hp (by positivity))
          (mul_le_mul_of_nonneg_left hFv (by positivity))
      _ = _ := by field_simp; ring
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ hR)
  change 2 / N + 64 * K / N ^ 2 ≤ (2 + 64 * K) / N
  rw [add_div]
  exact add_le_add le_rfl (div_le_div_of_nonneg_left (show 0 ≤ 64 * K by positivity)
    hN (by nlinarith : N ≤ N ^ 2))

theorem perpDir_pair_moment56 : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ v : Fin n → ℝ, UnitV v →
      (∫ g, ∫ g', dot56 (perpDir v g) (perpDir v g') ^ 2
        ∂stdGauss (Fin n) ∂stdGauss (Fin n)) ≤ C / ((n : ℝ) - 1) := by
  obtain ⟨C, hC, hbound⟩ := perpDir_linear_moment56
  refine ⟨C, hC, ?_⟩
  intro n hn v hv
  have hN : 0 < (n : ℝ) - 1 := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  calc
    _ ≤ ∫ _g, C / ((n : ℝ) - 1) ∂stdGauss (Fin n) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => integral_nonneg fun _ => sq_nonneg _)
        (integrable_const _) (Filter.Eventually.of_forall fun g =>
          (hbound n hn v hv _).trans (by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left
              (perpDir_sq_le_one56 v g) (show 0 ≤ C / ((n : ℝ) - 1) by positivity)))
    _ = _ := by simp

end BstLean.Part56
