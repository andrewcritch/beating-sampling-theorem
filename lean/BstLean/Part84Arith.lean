import BstLean.Part84Core

/-!
# Part 84: the arithmetic of the threshold

`thr84 d k K4` is the real threshold expression. For `n ≥ thr84 d k K4` the conditions of the
Gaussian model hold and the failure bound is `≤ 1/100`.
-/

namespace BstLean.Part84

/-- The threshold expression (real). -/
noncomputable def thr84 (d k : ℕ) (K4 : ℝ) : ℝ :=
  80 * (k : ℝ) ^ 2 * (2 * (d : ℝ) + 2) ^ 2 * (4 * (k : ℝ) + 5) ^ 4 +
    143000 * (2 * (d : ℝ) + 2) ^ 4 +
    871000 * ((k : ℝ) + 1) ^ 2 * (2 * (d : ℝ) + 2) ^ 2 +
    3500 * (2 * (k : ℝ) + 1) ^ 2 * K4 + 5000

theorem c1F_le (d : ℕ) (hd : 1 ≤ d) :
    0 ≤ c1F d (101 / 100) ∧ c1F d (101 / 100) ≤ 261 * (2 * (d : ℝ) + 2) ^ 2 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  unfold c1F
  constructor
  · positivity
  · nlinarith

theorem arith84 (n d k : ℕ) (K4 : ℝ) (hK4 : 0 ≤ K4) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (hN : thr84 d k K4 ≤ (n : ℝ)) :
    4 * (4 * (k : ℝ) + 5) ^ 2 * aK n d k ≤ 1 / 2 ∧
    12 * (k : ℝ) * aK n d k + c1F d (101 / 100) / n ≤ 1 / 10 ∧
    K4 * (4 * (101 / 100) + 2 * c1F d (101 / 100) ^ 2 / n) ≤ 5 * K4 ∧
    p0 n k (c1F d (101 / 100)) (5 * K4) (1 / 10) (1 / 2) (3 / 10) + 33 / (n : ℝ) ≤ 1 / 100 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hc0, hc1⟩ := c1F_le d hd
  set kk : ℝ := (k : ℝ) with hkk
  set D : ℝ := 2 * (d : ℝ) + 2 with hD
  set c1 : ℝ := c1F d (101 / 100) with hc1def
  set N : ℝ := (n : ℝ) with hNdef
  have hD4 : 4 ≤ D := by rw [hD]; linarith
  unfold thr84 at hN
  have t1 : 0 ≤ 80 * kk ^ 2 * D ^ 2 * (4 * kk + 5) ^ 4 := by positivity
  have t2 : 0 ≤ 143000 * D ^ 4 := by positivity
  have t3 : 0 ≤ 871000 * (kk + 1) ^ 2 * D ^ 2 := by positivity
  have t4 : 0 ≤ 3500 * (2 * kk + 1) ^ 2 * K4 := by positivity
  have hN5 : (5000 : ℝ) ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  -- (1)
  set X : ℝ := kk ^ 2 * D ^ 2 * (4 * kk + 5) ^ 4 with hX
  have hX0 : 0 ≤ X := by positivity
  have hNX : 80 * X ≤ N := by
    have : 80 * kk ^ 2 * D ^ 2 * (4 * kk + 5) ^ 4 = 80 * X := by rw [hX]; ring
    linarith
  set T : ℝ := 80 / 9 * kk * D * (4 * kk + 5) ^ 2 with hT
  have hT0 : 0 ≤ T := by positivity
  have hT2 : T ^ 2 ≤ N := by
    have : T ^ 2 = 6400 / 81 * X := by rw [hT, hX]; ring
    linarith
  have hTs : T ≤ Real.sqrt N := Real.le_sqrt_of_sq_le hT2
  have haK : aK n d k = 10 / 9 * kk * D / Real.sqrt N := rfl
  have h1 : 4 * (4 * kk + 5) ^ 2 * aK n d k ≤ 1 / 2 := by
    rw [haK]
    have : 4 * (4 * kk + 5) ^ 2 * (10 / 9 * kk * D / Real.sqrt N) = (T / 2) / Real.sqrt N := by
      rw [hT]; field_simp; ring
    rw [this, div_le_iff₀ hsq]
    linarith
  have haK0 : 0 ≤ aK n d k := by rw [haK]; positivity
  -- (2)
  have h56 : 56 * kk ≤ (4 * kk + 5) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ kk) (by linarith : (0 : ℝ) ≤ kk - 1)]
  have h12 : 12 * kk * aK n d k ≤ 3 / 100 := by
    have hA : 4 * (56 * kk) * aK n d k ≤ 1 / 2 :=
      le_trans (mul_le_mul_of_nonneg_right (by linarith) haK0) h1
    have hB : 4 * (56 * kk) * aK n d k = 224 * (kk * aK n d k) := by ring
    have hC : 12 * kk * aK n d k = 12 * (kk * aK n d k) := by ring
    rw [hC]; rw [hB] at hA; linarith
  have hNbig : 143000 * D ^ 4 ≤ N := by linarith
  have hD2 : 16 ≤ D ^ 2 := by nlinarith
  have hD44 : 16 * D ^ 2 ≤ D ^ 4 := by
    have : D ^ 4 = D ^ 2 * D ^ 2 := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hD2 (sq_nonneg D)
  have hD40 : 0 ≤ D ^ 4 := by positivity
  have hc1N : c1 / N ≤ 1 / 100 := by
    rw [div_le_iff₀ hNpos]
    linarith
  -- (3)
  have hc1sq : c1 ^ 2 ≤ 68121 * D ^ 4 := by
    have h := pow_le_pow_left₀ hc0 hc1 2
    have : (261 * D ^ 2) ^ 2 = 68121 * D ^ 4 := by ring
    linarith
  have h3' : 2 * c1 ^ 2 / N ≤ 96 / 100 := by
    rw [div_le_iff₀ hNpos]
    linarith
  refine ⟨h1, by linarith, ?_, ?_⟩
  · have : K4 * (4 * (101 / 100) + 2 * c1 ^ 2 / N) ≤ K4 * 5 :=
      mul_le_mul_of_nonneg_left (by linarith) hK4
    linarith
  · unfold p0
    have e1 : 5 / 2 * (kk + 1) ^ 2 * c1 / (N * ((1 / 2 : ℝ) ^ 2 * (3 / 10))) =
        100 / 3 * ((kk + 1) ^ 2 * c1) / N := by
      field_simp; ring
    have e2 : 5 / 2 * (2 * kk + 1) ^ 2 * (5 * K4) / (N * (1 - 1 / 10 - 3 / 10 : ℝ) ^ 2) =
        625 / 18 * ((2 * kk + 1) ^ 2 * K4) / N := by
      field_simp; ring
    rw [e1, e2, ← add_div, ← add_div, div_le_iff₀ hNpos]
    set U : ℝ := (kk + 1) ^ 2 * D ^ 2 with hU
    set V : ℝ := (2 * kk + 1) ^ 2 * K4 with hV
    have hV0 : 0 ≤ V := by positivity
    have hA : (kk + 1) ^ 2 * c1 ≤ 261 * U := by
      have := mul_le_mul_of_nonneg_left hc1 (by positivity : (0 : ℝ) ≤ (kk + 1) ^ 2)
      have e : (kk + 1) ^ 2 * (261 * D ^ 2) = 261 * U := by rw [hU]; ring
      linarith
    have hN' : 871000 * U + 3500 * V + 5000 ≤ N := by
      have e3 : 871000 * (kk + 1) ^ 2 * D ^ 2 = 871000 * U := by rw [hU]; ring
      have e4 : 3500 * (2 * kk + 1) ^ 2 * K4 = 3500 * V := by rw [hV]; ring
      linarith
    linarith

end BstLean.Part84
