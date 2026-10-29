import BstLean.Part57Key_Gaussian

/-! Normalized linear second moments from a radial split at half the mean. -/

namespace BstLean.Part57.KeyProof
open MeasureTheory BstLean.Part29 BstLean.Part56
variable {n r : ℕ}

lemma dot_bound (a w : Fin n → ℝ) (hw : ∑ i, w i ^ 2 ≤ 1) :
    dot56 a w ^ 2 ≤ ∑ i, a i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a w
  exact h.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hw
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))

lemma bad_radial (q N : ℝ) (hN : 0 < N) (hq : q < N / 2) :
    1 ≤ 4 / N ^ 2 * (q - N) ^ 2 := by
  have hs : N / 2 ≤ |q - N| := by rw [abs_of_nonpos (by linarith)]; linarith
  have hp := pow_le_pow_left₀ (show 0 ≤ N / 2 by positivity) hs 2
  rw [sq_abs, div_pow] at hp
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hp
  rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hN)]
  nlinarith

lemma dot_dir_dom (V : Fin r → Fin n → ℝ) (a g : Fin n → ℝ) (N : ℝ) (hN : 0 < N) :
    dot56 a (perpDirR V g) ^ 2 ≤ 2 / N * dot56 a (pvec V g) ^ 2 +
      ((∑ i, a i ^ 2) * (4 / N ^ 2)) * (rhoSq V g - N) ^ 2 := by
  have hq0 : 0 ≤ rhoSq V g := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have he : dot56 a (perpDirR V g) ^ 2 = dot56 a (pvec V g) ^ 2 / rhoSq V g := by
    have he' : dot56 a (perpDirR V g) = (1 / Real.sqrt (rhoSq V g)) * dot56 a (pvec V g) := by
      change (∑ i, a i * ((1 / Real.sqrt (rhoSq V g)) * pvec V g i)) = _
      rw [dot56, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [he', mul_pow, div_pow, Real.sq_sqrt hq0, one_pow]
    ring
  by_cases hq : N / 2 ≤ rhoSq V g
  · rw [he]
    have hb : dot56 a (pvec V g) ^ 2 / rhoSq V g ≤ 2 / N * dot56 a (pvec V g) ^ 2 := by
      rw [div_le_iff₀ (by linarith : 0 < rhoSq V g), div_mul_eq_mul_div,
        div_mul_eq_mul_div, le_div_iff₀ hN]
      nlinarith [mul_le_mul_of_nonneg_right hq (sq_nonneg (dot56 a (pvec V g)))]
    exact hb.trans (le_add_of_nonneg_right (by positivity))
  · have hb := mul_le_mul_of_nonneg_left (bad_radial (rhoSq V g) N hN (lt_of_not_ge hq))
      (Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg (a i)))
    have hs := dot_bound a _ (dir_sq V g)
    simp only [mul_one] at hb
    refine hs.trans (hb.trans ?_)
    calc
      _ = ((∑ i, a i ^ 2) * (4 / N ^ 2)) * (rhoSq V g - N) ^ 2 := by ring
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

lemma linear_moment (hr : 1 ≤ r) (hn : 2 * r ≤ n) (V : Fin r → Fin n → ℝ)
    (hV : OrthoF V) (a : Fin n → ℝ) :
    (∫ g, dot56 a (perpDirR V g) ^ 2 ∂stdGauss (Fin n)) ≤
      18 / ((n : ℝ) - r) * ∑ i, a i ^ 2 := by
  let N : ℝ := (n : ℝ) - r
  let R : ℝ := ∑ i, a i ^ 2
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hn' : 2 * (r : ℝ) ≤ n := by exact_mod_cast hn
  have hN : 0 < N := by dsimp [N]; linarith
  have hnN : (n : ℝ) ≤ 2 * N := by dsimp [N]; linarith
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc := int_rad_center V 2
  have hd : Integrable (fun g => dot56 a (perpDirR V g) ^ 2) (stdGauss (Fin n)) :=
    integrable_cont_dir V (fun w => dot56 a w ^ 2) (by unfold dot56; fun_prop)
  have h := integral_mono hd
    (((int_dot_sq V a).const_mul (2 / N)).add (hc.const_mul (R * (4 / N ^ 2))))
    (fun g => dot_dir_dom V a g N hN)
  simp only [Pi.add_apply] at h
  rw [integral_add ((int_dot_sq V a).const_mul _) (hc.const_mul _),
    integral_const_mul, integral_const_mul] at h
  have hb : (∫ g, dot56 a (perpDirR V g) ^ 2 ∂stdGauss (Fin n)) ≤
      (2 / N + 8 * n / N ^ 2) * R := by
    refine h.trans ?_
    calc
      _ ≤ 2 / N * R + (R * (4 / N ^ 2)) * (2 * n) :=
        add_le_add (mul_le_mul_of_nonneg_left (dot_second V hV a) (by positivity))
          (mul_le_mul_of_nonneg_left (rad_variance V hV) (by positivity))
      _ = _ := by ring
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ hR)
  change 2 / N + 8 * n / N ^ 2 ≤ 18 / N
  rw [le_div_iff₀ hN]
  field_simp
  nlinarith

end BstLean.Part57.KeyProof
