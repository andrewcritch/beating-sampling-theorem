import BstLean.Part81Defs2

/-!
# Part 81 (UM), part C: the sequence `muS n j`, sums uniform in the upper limit
-/

namespace BstLean.Part81.UM

open BstLean.Part81

lemma muS_pos' (n : ℕ) (hn : 1 ≤ n) (j : ℕ) : 0 < muS n j := by
  have hn0 : (0 : ℝ) < n := by positivity
  induction j with
  | zero => simpa [muS] using hn0
  | succ j ih => rw [muS]; positivity

lemma muS_succ_le (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    muS n (j + 1) ≤ muS n j * (2 * (j : ℝ) + 1) / n := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hp := muS_pos' n hn j
  rw [muS]
  apply div_le_div_of_nonneg_left (by positivity) hn0
  have : (0 : ℝ) ≤ 2 * (j : ℝ) := by positivity
  linarith

lemma muS_one (n : ℕ) (hn : 1 ≤ n) : muS n 1 = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp [muS, hn0]

lemma muS_two (n : ℕ) (hn : 1 ≤ n) : muS n 2 = 3 / ((n : ℝ) + 2) := by
  have h := muS_one n hn
  rw [muS, h]; norm_num

lemma muS_two_le (n : ℕ) (hn : 1 ≤ n) : muS n 2 ≤ 3 / (n : ℝ) := by
  have h := muS_succ_le n hn 1
  rw [muS_one n hn] at h
  norm_num at h ⊢; linarith

lemma muS_three_le (n : ℕ) (hn : 1 ≤ n) : muS n 3 ≤ 15 / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by positivity
  have h := muS_succ_le n hn 2
  have h2 := muS_two_le n hn
  have : muS n 2 * (2 * ((2 : ℕ) : ℝ) + 1) / n ≤ 3 / (n : ℝ) * (2 * ((2 : ℕ) : ℝ) + 1) / n := by
    gcongr
  have e : 3 / (n : ℝ) * (2 * ((2 : ℕ) : ℝ) + 1) / n = 15 / (n : ℝ) ^ 2 := by
    field_simp; norm_num
  linarith

lemma muS_four_le (n : ℕ) (hn : 1 ≤ n) : muS n 4 ≤ 105 / (n : ℝ) ^ 3 := by
  have hn0 : (0 : ℝ) < n := by positivity
  have h := muS_succ_le n hn 3
  have h2 := muS_three_le n hn
  have : muS n 3 * (2 * ((3 : ℕ) : ℝ) + 1) / n ≤ 15 / (n : ℝ) ^ 2 * (2 * ((3 : ℕ) : ℝ) + 1) / n := by
    gcongr
  have e : 15 / (n : ℝ) ^ 2 * (2 * ((3 : ℕ) : ℝ) + 1) / n = 105 / (n : ℝ) ^ 3 := by
    field_simp; norm_num
  linarith

lemma muS_five_le (n : ℕ) (hn : 1 ≤ n) : muS n 5 ≤ 945 / (n : ℝ) ^ 4 := by
  have hn0 : (0 : ℝ) < n := by positivity
  have h := muS_succ_le n hn 4
  have h2 := muS_four_le n hn
  have : muS n 4 * (2 * ((4 : ℕ) : ℝ) + 1) / n ≤ 105 / (n : ℝ) ^ 3 * (2 * ((4 : ℕ) : ℝ) + 1) / n := by
    gcongr
  have e : 105 / (n : ℝ) ^ 3 * (2 * ((4 : ℕ) : ℝ) + 1) / n = 945 / (n : ℝ) ^ 4 := by
    field_simp; norm_num
  linarith

lemma muS_six_le (n : ℕ) (hn : 1 ≤ n) : muS n 6 ≤ 10395 / (n : ℝ) ^ 5 := by
  have hn0 : (0 : ℝ) < n := by positivity
  have h := muS_succ_le n hn 5
  have h2 := muS_five_le n hn
  have : muS n 5 * (2 * ((5 : ℕ) : ℝ) + 1) / n ≤ 945 / (n : ℝ) ^ 4 * (2 * ((5 : ℕ) : ℝ) + 1) / n := by
    gcongr
  have e : 945 / (n : ℝ) ^ 4 * (2 * ((5 : ℕ) : ℝ) + 1) / n = 10395 / (n : ℝ) ^ 5 := by
    field_simp; norm_num
  linarith

/-- Polynomial decay: `muS n j · j⁵` is nonincreasing from `j = 6`. -/
lemma muS_tail (n : ℕ) (hn : 1000 ≤ n) (k : ℕ) :
    muS n (k + 6) * ((k : ℝ) + 6) ^ 5 ≤ muS n 6 * 6 ^ 5 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  induction k with
  | zero => simp
  | succ k ih =>
    refine le_trans ?_ ih
    have hp := muS_pos' n hn1 (k + 6)
    have hk : (0 : ℝ) ≤ k := by positivity
    set j : ℝ := (k : ℝ) + 6 with hj
    have hj6 : (6 : ℝ) ≤ j := by linarith
    have hd : (0 : ℝ) < (n : ℝ) + 2 * j := by linarith
    have e : muS n (k + 1 + 6) = muS n (k + 6) * (2 * j + 1) / ((n : ℝ) + 2 * j) := by
      show muS n (k + 6 + 1) = _
      rw [muS]; push_cast; rw [hj]
    rw [e]
    push_cast
    have e2 : (k : ℝ) + 1 + 6 = j + 1 := by rw [hj]; ring
    rw [e2]
    have key : (2 * j + 1) * (j + 1) ^ 5 ≤ j ^ 5 * ((n : ℝ) + 2 * j) := by
      have a1 : (2 * j + 1) * (j + 1) ≤ (j - 4) * ((n : ℝ) + 2 * j) := by nlinarith
      have a2 : (j - 4) * (j + 1) ^ 4 ≤ j ^ 5 := by
        have : j ^ 5 - (j - 4) * (j + 1) ^ 4 = 10 * j ^ 3 + 20 * j ^ 2 + 15 * j + 4 := by ring
        have : (0 : ℝ) ≤ 10 * j ^ 3 + 20 * j ^ 2 + 15 * j + 4 := by positivity
        linarith
      have p4 : (0 : ℝ) ≤ (j + 1) ^ 4 := by positivity
      calc (2 * j + 1) * (j + 1) ^ 5 = ((2 * j + 1) * (j + 1)) * (j + 1) ^ 4 := by ring
        _ ≤ ((j - 4) * ((n : ℝ) + 2 * j)) * (j + 1) ^ 4 := by gcongr
        _ = ((j - 4) * (j + 1) ^ 4) * ((n : ℝ) + 2 * j) := by ring
        _ ≤ j ^ 5 * ((n : ℝ) + 2 * j) := by gcongr
    have : muS n (k + 6) * (2 * j + 1) / ((n : ℝ) + 2 * j) * (j + 1) ^ 5
        = muS n (k + 6) * ((2 * j + 1) * (j + 1) ^ 5) / ((n : ℝ) + 2 * j) := by ring
    rw [this, div_le_iff₀ hd]
    calc muS n (k + 6) * ((2 * j + 1) * (j + 1) ^ 5)
        ≤ muS n (k + 6) * (j ^ 5 * ((n : ℝ) + 2 * j)) := by gcongr
      _ = muS n (k + 6) * j ^ 5 * ((n : ℝ) + 2 * j) := by ring

lemma tele (b : ℝ) (hb : 0 < b) :
    1 / (b + 1) ^ 3 ≤ 1 / (2 * b ^ 2) - 1 / (2 * (b + 1) ^ 2) := by
  have e : 1 / (2 * b ^ 2) - 1 / (2 * (b + 1) ^ 2) - 1 / (b + 1) ^ 3
      = (3 * b + 1) / (2 * b ^ 2 * (b + 1) ^ 3) := by
    field_simp; ring
  have : 0 ≤ (3 * b + 1) / (2 * b ^ 2 * (b + 1) ^ 3) := by positivity
  linarith

/-- Tail from `j = 6` with weights of at most quadratic growth. -/
lemma tail_sum (n : ℕ) (hn : 1000 ≤ n) (u : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ k, 0 ≤ u k ∧ u k ≤ K * ((k : ℝ) + 6) ^ 2) (M : ℕ) :
    ∑ k ∈ Finset.range M, u k * muS n (k + 6)
      ≤ K * (muS n 6 * 6 ^ 5) * (1 / 50 - 1 / (2 * ((M : ℝ) + 5) ^ 2)) := by
  have hn1 : 1 ≤ n := by omega
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hp := muS_pos' n hn1 (M + 6)
    have ht := muS_tail n hn M
    obtain ⟨hu0, hu1⟩ := hu M
    have hb : (0 : ℝ) < (M : ℝ) + 5 := by positivity
    have hC : 0 ≤ K * (muS n 6 * 6 ^ 5) := by
      have := muS_pos' n hn1 6; positivity
    have hterm : u M * muS n (M + 6) ≤ K * (muS n 6 * 6 ^ 5) * (1 / ((M : ℝ) + 5 + 1) ^ 3) := by
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      have e6 : (M : ℝ) + 5 + 1 = (M : ℝ) + 6 := by ring
      rw [e6]
      calc u M * muS n (M + 6) * ((M : ℝ) + 6) ^ 3
          ≤ (K * ((M : ℝ) + 6) ^ 2) * muS n (M + 6) * ((M : ℝ) + 6) ^ 3 := by gcongr
        _ = K * (muS n (M + 6) * ((M : ℝ) + 6) ^ 5) := by ring
        _ ≤ K * (muS n 6 * 6 ^ 5) := by gcongr
    have htele := tele ((M : ℝ) + 5) hb
    have h2 : K * (muS n 6 * 6 ^ 5) * (1 / ((M : ℝ) + 5 + 1) ^ 3)
        ≤ K * (muS n 6 * 6 ^ 5) *
          (1 / (2 * ((M : ℝ) + 5) ^ 2) - 1 / (2 * ((M : ℝ) + 5 + 1) ^ 2)) := by gcongr
    have e : ((M + 1 : ℕ) : ℝ) + 5 = (M : ℝ) + 5 + 1 := by push_cast; ring
    rw [e]
    nlinarith [ih, hterm, h2]

lemma sum_split3 (g : ℕ → ℝ) (M : ℕ) :
    ∑ k ∈ Finset.range (M + 3), g k = g 0 + g 1 + g 2 + ∑ k ∈ Finset.range M, g (k + 3) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
  ring

/-- Master bound: sums from `j = 3` with weights `v k` (at index `j = k + 3`). -/
lemma master (n : ℕ) (hn : 1000 ≤ n) (v : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hv : ∀ k, 0 ≤ v k ∧ v k ≤ K * ((k : ℝ) + 3) ^ 2) (M : ℕ) :
    ∑ k ∈ Finset.range M, v k * muS n (k + 3)
      ≤ v 0 * (15 / (n : ℝ) ^ 2) + v 1 * (105 / (n : ℝ) ^ 3) + v 2 * (945 / (n : ℝ) ^ 4)
        + K * (1616631 / (n : ℝ) ^ 5) := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by positivity
  have hnn : ∀ k, 0 ≤ v k * muS n (k + 3) := fun k =>
    mul_nonneg (hv k).1 (muS_pos' n hn1 _).le
  have h1 : ∑ k ∈ Finset.range M, v k * muS n (k + 3)
      ≤ ∑ k ∈ Finset.range (M + 3), v k * muS n (k + 3) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) (fun k _ _ => hnn k)
  rw [sum_split3] at h1
  have ht := tail_sum n hn (fun k => v (k + 3)) K hK (fun k => by
    refine ⟨(hv _).1, ?_⟩
    have := (hv (k + 3)).2
    push_cast at this
    have e : (k : ℝ) + 3 + 3 = (k : ℝ) + 6 := by ring
    rw [e] at this; exact this) M
  have ht' : ∑ k ∈ Finset.range M, v (k + 3) * muS n (k + 3 + 3)
      ≤ K * (muS n 6 * 6 ^ 5) * (1 / 50) := by
    refine le_trans ht ?_
    have hC : 0 ≤ K * (muS n 6 * 6 ^ 5) := by
      have := muS_pos' n hn1 6; positivity
    have : (0 : ℝ) ≤ 1 / (2 * ((M : ℝ) + 5) ^ 2) := by positivity
    nlinarith
  have h6 : K * (muS n 6 * 6 ^ 5) * (1 / 50) ≤ K * (1616631 / (n : ℝ) ^ 5) := by
    have := muS_six_le n hn1
    have e : K * (muS n 6 * 6 ^ 5) * (1 / 50) = K * (muS n 6 * (7776 / 50)) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hK
    calc muS n 6 * (7776 / 50) ≤ 10395 / (n : ℝ) ^ 5 * (7776 / 50) := by gcongr
      _ ≤ 1616631 / (n : ℝ) ^ 5 := by
        rw [div_mul_eq_mul_div]; gcongr; norm_num
  have a0 : v 0 * muS n (0 + 3) ≤ v 0 * (15 / (n : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left (muS_three_le n hn1) (hv 0).1
  have a1 : v 1 * muS n (1 + 3) ≤ v 1 * (105 / (n : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left (muS_four_le n hn1) (hv 1).1
  have a2 : v 2 * muS n (2 + 3) ≤ v 2 * (945 / (n : ℝ) ^ 4) :=
    mul_le_mul_of_nonneg_left (muS_five_le n hn1) (hv 2).1
  linarith

/-- Powers of `1/n` for `n ≥ 1000`. -/
lemma inv_pows (n : ℕ) (hn : 1000 ≤ n) :
    1 / (n : ℝ) ^ 3 ≤ (1 / 1000) * (1 / (n : ℝ) ^ 2) ∧
    1 / (n : ℝ) ^ 4 ≤ (1 / 1000000) * (1 / (n : ℝ) ^ 2) ∧
    1 / (n : ℝ) ^ 5 ≤ (1 / 1000000000) * (1 / (n : ℝ) ^ 2) ∧
    1 / (n : ℝ) ^ 4 ≤ (1 / 1000) * (1 / (n : ℝ) ^ 3) ∧
    1 / (n : ℝ) ^ 5 ≤ (1 / 1000000) * (1 / (n : ℝ) ^ 3) := by
  have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ht : 1 / (n : ℝ) ≤ 1 / 1000 := by
    apply one_div_le_one_div_of_le (by norm_num) hnR
  have ht0 : 0 < 1 / (n : ℝ) := by positivity
  set t : ℝ := 1 / (n : ℝ) with htdef
  have e : ∀ k : ℕ, 1 / (n : ℝ) ^ k = t ^ k := fun k => by rw [htdef, one_div_pow]
  simp only [e]
  have t2 : 0 ≤ t ^ 2 := by positivity
  have t3 : 0 ≤ t ^ 3 := by positivity
  have b1 : t ^ 3 ≤ (1 / 1000) * t ^ 2 := by nlinarith
  have b4 : t ^ 4 ≤ (1 / 1000) * t ^ 3 := by nlinarith
  have b5 : t ^ 5 ≤ (1 / 1000) * t ^ 4 := by
    have t4 : 0 ≤ t ^ 4 := by positivity
    nlinarith
  refine ⟨b1, ?_, ?_, b4, ?_⟩ <;> linarith

lemma sum1_range (n : ℕ) (hn : 1000 ≤ n) (M : ℕ) :
    ∑ k ∈ Finset.range M, muS n (k + 3) ≤ 16 / (n : ℝ) ^ 2 := by
  have h := master n hn (fun _ => 1) 1 (by norm_num) (fun k => by
    have : (0 : ℝ) ≤ k := by positivity
    constructor
    · norm_num
    · nlinarith) M
  simp only [one_mul] at h
  obtain ⟨p1, p2, p3, p4, p5⟩ := inv_pows n hn
  have e : ∀ (c : ℝ) (k : ℕ), c / (n : ℝ) ^ k = c * (1 / (n : ℝ) ^ k) := fun c k => by ring
  rw [e] at h ⊢
  rw [e 105, e 945, e 1616631] at h
  have q2 : (0 : ℝ) ≤ ((n : ℝ) ^ 2)⁻¹ := by positivity
  have q3 : (0 : ℝ) ≤ ((n : ℝ) ^ 3)⁻¹ := by positivity
  simp only [one_div] at p1 p2 p3 p4 p5 h ⊢
  linarith

lemma sum2_range (n : ℕ) (hn : 1000 ≤ n) (M : ℕ) :
    ∑ k ∈ Finset.range M, ((k : ℝ) + 1) * muS n (k + 3) ≤ 16 / (n : ℝ) ^ 2 := by
  have h := master n hn (fun k => (k : ℝ) + 1) 1 (by norm_num) (fun k => by
    have : (0 : ℝ) ≤ k := by positivity
    constructor
    · positivity
    · nlinarith) M
  obtain ⟨p1, p2, p3, p4, p5⟩ := inv_pows n hn
  have e : ∀ (c : ℝ) (k : ℕ), c / (n : ℝ) ^ k = c * (1 / (n : ℝ) ^ k) := fun c k => by ring
  rw [e] at h ⊢
  rw [e 105, e 945, e 1616631] at h
  have q2 : (0 : ℝ) ≤ ((n : ℝ) ^ 2)⁻¹ := by positivity
  have q3 : (0 : ℝ) ≤ ((n : ℝ) ^ 3)⁻¹ := by positivity
  norm_num at h
  simp only [one_div] at p1 p2 p3 p4 p5 h ⊢
  linarith

lemma sum3_range (n : ℕ) (hn : 1000 ≤ n) (M : ℕ) :
    ∑ k ∈ Finset.range M, (((k : ℝ) + 1) * ((k : ℝ) + 2) / 2) * muS n (k + 4)
      ≤ 110 / (n : ℝ) ^ 3 := by
  have h := master n hn (fun k => (k : ℝ) * ((k : ℝ) + 1) / 2) (1 / 2) (by norm_num) (fun k => by
    have : (0 : ℝ) ≤ k := by positivity
    constructor
    · positivity
    · nlinarith) (M + 1)
  rw [Finset.sum_range_succ'] at h
  have e0 : ∑ k ∈ Finset.range M, (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) / 2) * muS n (k + 1 + 3)
      = ∑ k ∈ Finset.range M, (((k : ℝ) + 1) * ((k : ℝ) + 2) / 2) * muS n (k + 4) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring
  rw [e0] at h
  obtain ⟨p1, p2, p3, p4, p5⟩ := inv_pows n hn
  have e : ∀ (c : ℝ) (k : ℕ), c / (n : ℝ) ^ k = c * (1 / (n : ℝ) ^ k) := fun c k => by ring
  rw [e] at h ⊢
  rw [e 105, e 945, e 1616631] at h
  have q2 : (0 : ℝ) ≤ ((n : ℝ) ^ 2)⁻¹ := by positivity
  have q3 : (0 : ℝ) ≤ ((n : ℝ) ^ 3)⁻¹ := by positivity
  norm_num at h
  simp only [one_div] at p1 p2 p3 p4 p5 h ⊢
  linarith

end BstLean.Part81.UM

namespace BstLean.Part81

open BstLean.Part81.UM

theorem muS_sum1 (n : ℕ) (hn : 1000 ≤ n) (J : ℕ) :
    ∑ j ∈ Finset.Icc 3 J, muS n j ≤ 16 / (n : ℝ) ^ 2 := by
  have h := sum1_range n hn (J + 1 - 3)
  rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simpa [add_comm] using h

theorem muS_sum2 (n : ℕ) (hn : 1000 ≤ n) (J : ℕ) :
    ∑ j ∈ Finset.Icc 3 J, ((j : ℝ) - 2) * muS n j ≤ 16 / (n : ℝ) ^ 2 := by
  have h := sum2_range n hn (J + 1 - 3)
  rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun k _ => ?_) h
  rw [add_comm 3 k]; push_cast; ring

theorem muS_sum3 (n : ℕ) (hn : 1000 ≤ n) (J : ℕ) :
    ∑ j ∈ Finset.Icc 4 J, (((j : ℝ) - 2) * ((j : ℝ) - 3) / 2) * muS n j ≤ 110 / (n : ℝ) ^ 3 := by
  have h := sum3_range n hn (J + 1 - 4)
  rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun k _ => ?_) h
  rw [add_comm 4 k]; push_cast; ring

end BstLean.Part81
