import BstLean.Part56Key_Gaussian

namespace BstLean.Part56

open MeasureTheory BstLean.Part29
open scoped ENNReal

private lemma qrad_nonneg56 {n : ℕ} (v g : Fin n → ℝ) : 0 ≤ qrad56 v g :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma bad_radial_bound56 (q N : ℝ) (hN : 0 < N) (hq : q < N / 2) :
    1 ≤ 16 / N ^ 4 * (q - N) ^ 4 := by
  have hs : N / 2 ≤ |q - N| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hp := pow_le_pow_left₀ (show 0 ≤ N / 2 by positivity) hs 4
  rw [pow_abs, div_pow] at hp
  rw [abs_of_nonneg (show 0 ≤ (q - N) ^ 4 by positivity)] at hp
  norm_num only [show (2 : ℝ) ^ 4 = 16 by norm_num] at hp
  have hn : 0 < N ^ 4 := pow_pos hN _
  rw [div_mul_eq_mul_div, le_div_iff₀ hn]
  nlinarith

private lemma perpDir_sq_formula56 {n : ℕ} (v g : Fin n → ℝ) (i : Fin n) :
    perpDir v g i ^ 2 = pvec56 v g i ^ 2 / qrad56 v g := by
  change ((1 / Real.sqrt (qrad56 v g)) * pvec56 v g i) ^ 2 = _
  rw [mul_pow, div_pow, Real.sq_sqrt (qrad_nonneg56 v g), one_pow]
  ring

private lemma perpDir_fourth_formula56 {n : ℕ} (v g : Fin n → ℝ) (i : Fin n) :
    perpDir v g i ^ 4 = pvec56 v g i ^ 4 / qrad56 v g ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, perpDir_sq_formula56, div_pow, ← pow_mul]

private lemma perpDir_sq_dom56 {n : ℕ} (v g : Fin n → ℝ) (i : Fin n) (N : ℝ) (hN : 0 < N) :
    perpDir v g i ^ 2 ≤ 2 / N * pvec56 v g i ^ 2 +
      16 / N ^ 4 * (qrad56 v g - N) ^ 4 := by
  by_cases hq : N / 2 ≤ qrad56 v g
  · have hq0 : 0 < qrad56 v g := by linarith
    have hb : pvec56 v g i ^ 2 / qrad56 v g ≤ 2 / N * pvec56 v g i ^ 2 := by
      rw [div_le_iff₀ hq0]
      have hn := mul_le_mul_of_nonneg_right hq (sq_nonneg (pvec56 v g i))
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hN]
      nlinarith
    rw [perpDir_sq_formula56]
    exact hb.trans (le_add_of_nonneg_right (by positivity))
  · have hb := bad_radial_bound56 (qrad56 v g) N hN (lt_of_not_ge hq)
    have hs : perpDir v g i ^ 2 ≤ 1 := by
      have := perpDir_abs_le_one56 v g i
      nlinarith [sq_abs (perpDir v g i), abs_nonneg (perpDir v g i)]
    exact hs.trans (hb.trans (le_add_of_nonneg_left (by positivity)))

private lemma perpDir_fourth_dom56 {n : ℕ} (v g : Fin n → ℝ) (i : Fin n) (N : ℝ) (hN : 0 < N) :
    perpDir v g i ^ 4 ≤ 4 / N ^ 2 * pvec56 v g i ^ 4 +
      16 / N ^ 4 * (qrad56 v g - N) ^ 4 := by
  by_cases hq : N / 2 ≤ qrad56 v g
  · have hq0 : 0 < qrad56 v g := by linarith
    have hb : pvec56 v g i ^ 4 / qrad56 v g ^ 2 ≤ 4 / N ^ 2 * pvec56 v g i ^ 4 := by
      rw [div_le_iff₀ (sq_pos_of_pos hq0)]
      have hn := pow_le_pow_left₀ (show 0 ≤ N / 2 by positivity) hq 2
      have hp : 0 ≤ pvec56 v g i ^ 4 := by positivity
      have hm := mul_le_mul_of_nonneg_right hn hp
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hN)]
      nlinarith
    rw [perpDir_fourth_formula56]
    exact hb.trans (le_add_of_nonneg_right (by positivity))
  · have hb := bad_radial_bound56 (qrad56 v g) N hN (lt_of_not_ge hq)
    have hs : perpDir v g i ^ 4 ≤ 1 := by
      have := pow_le_pow_left₀ (abs_nonneg (perpDir v g i)) (perpDir_abs_le_one56 v g i) 4
      simpa only [pow_abs, abs_of_nonneg (show 0 ≤ perpDir v g i ^ 4 by positivity), one_pow] using this
    exact hs.trans (hb.trans (le_add_of_nonneg_left (by positivity)))

theorem integrable_perpDir_pow56 {n : ℕ} (v : Fin n → ℝ) (i : Fin n) (k : ℕ) :
    Integrable (fun g => perpDir v g i ^ k) (stdGauss (Fin n)) := by
  apply Integrable.of_bound
    (((measurable_pi_apply i).comp (measurable_perpDir56 v)).pow_const k).aestronglyMeasurable 1
  filter_upwards [] with g
  rw [Real.norm_eq_abs, abs_pow]
  change |perpDir v g i| ^ k ≤ 1
  simpa only [one_pow] using pow_le_pow_left₀
    (abs_nonneg (perpDir v g i)) (perpDir_abs_le_one56 v g i) k

private lemma pvec_mom_bounds56 {n : ℕ} (v : Fin n → ℝ) (hv : UnitV v) (i : Fin n) :
    (∫ g, pvec56 v g i ^ 2 ∂stdGauss (Fin n)) ≤ 1 ∧
    (∫ g, pvec56 v g i ^ 4 ∂stdGauss (Fin n)) ≤ 3 := by
  have hvi : v i ^ 2 ≤ 1 := by
    have := Finset.single_le_sum (fun l hl => sq_nonneg (v l)) (Finset.mem_univ i)
    rwa [hv] at this
  rw [pvec_second56 v hv, pvec_fourth56 v hv]
  constructor <;> nlinarith [sq_nonneg (v i)]

theorem perpDir_coordinate_moments56 : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ i : Fin n,
      (∫ g, perpDir v g i ^ 2 ∂stdGauss (Fin n)) ≤ C / ((n : ℝ) - 1) ∧
      (∫ g, perpDir v g i ^ 4 ∂stdGauss (Fin n)) ≤ C / ((n : ℝ) - 1) ^ 2 := by
  obtain ⟨K, hK, hF⟩ := qrad_fourth_exists56
  refine ⟨12 + 64 * K, by positivity, ?_⟩
  intro n hn v hv i
  let N : ℝ := (n : ℝ) - 1
  have hN1 : 1 ≤ N := by
    dsimp [N]
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hN2 : 0 < N ^ 2 := sq_pos_of_pos hN
  have hN4 : 0 < N ^ 4 := pow_pos hN _
  have hp := pvec_mom_bounds56 v hv i
  have hFv := hF n v hv
  change (∫ g, (qrad56 v g - N) ^ 4 ∂stdGauss (Fin n)) ≤ 4 * K * N ^ 2 at hFv
  have hc := integrable_qrad_center_pow56 v 4
  change Integrable (fun g => (qrad56 v g - N) ^ 4) (stdGauss (Fin n)) at hc
  constructor
  · have h := integral_mono (integrable_perpDir_pow56 v i 2)
      (((integrable_pvec_pow56 v i 2).const_mul (2 / N)).add (hc.const_mul (16 / N ^ 4)))
      (fun g => perpDir_sq_dom56 v g i N hN)
    simp only [Pi.add_apply] at h
    rw [integral_add (f := fun g => 2 / N * pvec56 v g i ^ 2)
      (g := fun g => 16 / N ^ 4 * (qrad56 v g - N) ^ 4)
      ((integrable_pvec_pow56 v i 2).const_mul _) (hc.const_mul _),
      integral_const_mul, integral_const_mul] at h
    have hb : (∫ g, perpDir v g i ^ 2 ∂stdGauss (Fin n)) ≤
        2 / N + 64 * K / N ^ 2 := by
      refine h.trans ?_
      calc
        _ ≤ 2 / N * 1 + 16 / N ^ 4 * (4 * K * N ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hp.1 (by positivity))
            (mul_le_mul_of_nonneg_left hFv (by positivity))
        _ = _ := by field_simp; ring
    have hNN : N ≤ N ^ 2 := by nlinarith
    calc
      _ ≤ 2 / N + 64 * K / N ^ 2 := hb
      _ ≤ 2 / N + 64 * K / N := add_le_add le_rfl
        (div_le_div_of_nonneg_left (show 0 ≤ 64 * K by positivity) hN hNN)
      _ ≤ (12 + 64 * K) / N := by rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hN.le
  · have h := integral_mono (integrable_perpDir_pow56 v i 4)
      (((integrable_pvec_pow56 v i 4).const_mul (4 / N ^ 2)).add (hc.const_mul (16 / N ^ 4)))
      (fun g => perpDir_fourth_dom56 v g i N hN)
    simp only [Pi.add_apply] at h
    rw [integral_add (f := fun g => 4 / N ^ 2 * pvec56 v g i ^ 4)
      (g := fun g => 16 / N ^ 4 * (qrad56 v g - N) ^ 4)
      ((integrable_pvec_pow56 v i 4).const_mul _) (hc.const_mul _),
      integral_const_mul, integral_const_mul] at h
    refine h.trans ?_
    calc
      _ ≤ 4 / N ^ 2 * 3 + 16 / N ^ 4 * (4 * K * N ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hp.2 (by positivity))
          (mul_le_mul_of_nonneg_left hFv (by positivity))
      _ = (12 + 64 * K) / N ^ 2 := by field_simp; ring

end BstLean.Part56
