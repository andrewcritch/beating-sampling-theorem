import BstLean.Part108Core

/-!
# Part 108: the numeric bounds for every `n ≥ 4 096`

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part108

open BstLean.Part105
open BstLean.Part107 (vbar Ea2 delN Sof)

theorem vbar_le (n dA : ℕ) (hn : 4096 ≤ n) (hdA : dA = 3 ∨ dA = 4) :
    BstLean.Part107.vbar dA n ≤ (dA : ℝ) - 1 := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  rcases hdA with rfl | rfl
  · have hdel : delN 3 (2 * n) =
        (3 / (2 * (n : ℝ)) + 3 * 21 / ((2 * (n : ℝ)) * (2 * (n : ℝ) + 2))) / 49 := by
      simp only [delN, Sof, if_true]; push_cast; norm_num
    have hd0 : 0 ≤ delN 3 (2 * n) := by rw [hdel]; positivity
    have hE0 : 0 ≤ Ea2 3 n := by unfold Ea2; positivity
    have hE : Ea2 3 n ≤ 1 / 25 := by
      unfold Ea2; rw [hdel]; push_cast
      calc _ ≤ (1 : ℝ) / (2 * 3 + 1) ^ 2 +
            (3 / (2 * 4096) + 3 * 21 / ((2 * 4096) * (2 * 4096 + 2))) / 49
            + 3 / 4096 := by gcongr
        _ ≤ 1 / 25 := by norm_num
    have hs : Real.sqrt (Ea2 3 n) ≤ 1 / 5 := by
      rw [Real.sqrt_le_iff]; exact ⟨by norm_num, hE.trans (by norm_num)⟩
    unfold vbar; push_cast; linarith
  · have hdel : delN 4 (2 * n) =
        (3 / (2 * (n : ℝ)) + 3 * 37 / ((2 * (n : ℝ)) * (2 * (n : ℝ) + 2))) / 81 := by
      simp only [delN, Sof]; push_cast; norm_num
    have hd0 : 0 ≤ delN 4 (2 * n) := by rw [hdel]; positivity
    have hE0 : 0 ≤ Ea2 4 n := by unfold Ea2; positivity
    have hE : Ea2 4 n ≤ 1 / 25 := by
      unfold Ea2; rw [hdel]; push_cast
      calc _ ≤ (1 : ℝ) / (2 * 4 + 1) ^ 2 +
            (3 / (2 * 4096) + 3 * 37 / ((2 * 4096) * (2 * 4096 + 2))) / 81
            + 3 / 4096 := by gcongr
        _ ≤ 1 / 25 := by norm_num
    have hs : Real.sqrt (Ea2 4 n) ≤ 1 / 5 := by
      rw [Real.sqrt_le_iff]; exact ⟨by norm_num, hE.trans (by norm_num)⟩
    unfold vbar; push_cast; linarith

theorem cardA_ge (n dA : ℕ) (hn : 4096 ≤ n) (hdA : dA = 3 ∨ dA = 4) :
    (n : ℝ) ^ 4 / 6 ≤ (Fintype.card (CoefIdx n n dA) : ℝ) := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  rw [BstLean.Part106.card_coefIdx]
  push_cast
  rcases hdA with rfl | rfl
  · have h := Nat.pow_le_choose (α := ℝ) 3 (n + 3)
    have e : ((n + 3 + 1 - 3 : ℕ) : ℝ) = (n : ℝ) + 1 := by
      have : n + 3 + 1 - 3 = n + 1 := by omega
      rw [this]; push_cast; ring
    rw [e] at h
    have hf : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [hf] at h
    have h3 : (n : ℝ) ^ 3 ≤ ((n : ℝ) + 1) ^ 3 := by gcongr; linarith
    calc (n : ℝ) ^ 4 / 6 = n * ((n : ℝ) ^ 3 / 6) := by ring
      _ ≤ n * (((n : ℝ) + 1) ^ 3 / 6) := by gcongr
      _ ≤ _ := by gcongr
  · have h := Nat.pow_le_choose (α := ℝ) 4 (n + 4)
    have e : ((n + 4 + 1 - 4 : ℕ) : ℝ) = (n : ℝ) + 1 := by
      have : n + 4 + 1 - 4 = n + 1 := by omega
      rw [this]; push_cast; ring
    rw [e] at h
    have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hf] at h
    have h3 : (n : ℝ) ^ 3 ≤ ((n : ℝ) + 1) ^ 3 := by gcongr; linarith
    have h4 : (n : ℝ) ^ 3 / 6 ≤ ((n : ℝ) + 1) ^ 4 / 24 := by
      have : (n : ℝ) ^ 3 * 4 ≤ ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 1) :=
        mul_le_mul h3 (by linarith) (by norm_num) (by positivity)
      have e4 : ((n : ℝ) + 1) ^ 4 = ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 1) := by ring
      rw [e4]; linarith
    calc (n : ℝ) ^ 4 / 6 = n * ((n : ℝ) ^ 3 / 6) := by ring
      _ ≤ n * (((n : ℝ) + 1) ^ 4 / 24) := by gcongr
      _ ≤ _ := by gcongr

private lemma ssum_arith {x : ℝ} (hx : 4096 ≤ x) :
    24 / x ^ 4 * 25 * (x * (x + 2)) + (24 / x ^ 4) ^ 2 * 125 * (15 * x ^ 3) +
      (24 / x ^ 4) ^ 3 * 625 * (105 * x ^ 4) ≤ 601 / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have h3 : (4096 : ℝ) ^ 3 ≤ x ^ 3 := by gcongr
  have h5 : (4096 : ℝ) ^ 2 * x ^ 3 ≤ x ^ 5 := by
    have : (4096 : ℝ) ^ 2 ≤ x ^ 2 := by gcongr
    calc (4096 : ℝ) ^ 2 * x ^ 3 ≤ x ^ 2 * x ^ 3 := by gcongr
      _ = x ^ 5 := by ring
  have h6 : 4096 * x ^ 5 ≤ x ^ 6 := by
    calc 4096 * x ^ 5 ≤ x * x ^ 5 := by gcongr
      _ = x ^ 6 := by ring
  have key : 1200 * x ^ 5 + 1080000 * x ^ 3 + 907200000 ≤ x ^ 6 := by
    have : (0 : ℝ) ≤ x ^ 5 := by positivity
    nlinarith
  have e : 24 / x ^ 4 * 25 * (x * (x + 2)) + (24 / x ^ 4) ^ 2 * 125 * (15 * x ^ 3) +
      (24 / x ^ 4) ^ 3 * 625 * (105 * x ^ 4) =
      (600 * x ^ 6 + 1200 * x ^ 5 + 1080000 * x ^ 3 + 907200000) / x ^ 8 := by
    field_simp
    ring
  have e2 : 601 / x ^ 2 = 601 * x ^ 6 / x ^ 8 := by
    field_simp
  rw [e, e2]
  gcongr
  linarith

theorem ssum_le (hG : GMom108) (n dA dF : ℕ) (hn : 4096 ≤ n) (hdA : dA = 3 ∨ dA = 4)
    (hdF : dF = 3 ∨ dF = 4) :
    Ssum n dA dF (4 / (Fintype.card (CoefIdx n n dA) : ℝ)) ≤ 601 / (n : ℝ) ^ 2 := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  obtain ⟨hg0, hg2, hg3, hg4⟩ := hG n (by omega)
  have hD := cardA_ge n dA hn hdA
  set D : ℝ := (Fintype.card (CoefIdx n n dA) : ℝ) with hDdef
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hc0 : 0 ≤ 4 / D := by positivity
  have hc : 4 / D ≤ 24 / (n : ℝ) ^ 4 := by
    rw [div_le_div_iff₀ hDpos (by positivity)]
    linarith
  have hK0 : (0 : ℝ) ≤ (dA : ℝ) + 1 := by positivity
  have hK : (dA : ℝ) + 1 ≤ 5 := by
    rcases hdA with rfl | rfl <;> norm_num
  have t2 : (4 / D) ^ (2 - 1) * ((dA : ℝ) + 1) ^ 2 * gmom n 2 ≤
      24 / (n : ℝ) ^ 4 * 25 * ((n : ℝ) * ((n : ℝ) + 2)) := by
    rw [hg2]
    have : ((dA : ℝ) + 1) ^ 2 ≤ 25 := by nlinarith
    simp only [Nat.add_one_sub_one, pow_one]
    gcongr
  have t3 : (4 / D) ^ (3 - 1) * ((dA : ℝ) + 1) ^ 3 * gmom n 3 ≤
      (24 / (n : ℝ) ^ 4) ^ 2 * 125 * (15 * (n : ℝ) ^ 3) := by
    have : ((dA : ℝ) + 1) ^ 3 ≤ 5 ^ 3 := by gcongr
    have h125 : ((dA : ℝ) + 1) ^ 3 ≤ 125 := by linarith
    have hp : (4 / D) ^ (3 - 1) ≤ (24 / (n : ℝ) ^ 4) ^ 2 := by
      show (4 / D) ^ 2 ≤ _
      gcongr
    exact mul_le_mul (mul_le_mul hp h125 (by positivity) (by positivity)) hg3 (hg0 3)
      (by positivity)
  have t4 : (4 / D) ^ (4 - 1) * ((dA : ℝ) + 1) ^ 4 * gmom n 4 ≤
      (24 / (n : ℝ) ^ 4) ^ 3 * 625 * (105 * (n : ℝ) ^ 4) := by
    have : ((dA : ℝ) + 1) ^ 4 ≤ 5 ^ 4 := by gcongr
    have h625 : ((dA : ℝ) + 1) ^ 4 ≤ 625 := by linarith
    have hp : (4 / D) ^ (4 - 1) ≤ (24 / (n : ℝ) ^ 4) ^ 3 := by
      show (4 / D) ^ 3 ≤ _
      gcongr
    exact mul_le_mul (mul_le_mul hp h625 (by positivity) (by positivity)) hg4 (hg0 4)
      (by positivity)
  have hA := ssum_arith hx
  have hlast : (0 : ℝ) ≤ (24 / (n : ℝ) ^ 4) ^ 3 * 625 * (105 * (n : ℝ) ^ 4) := by positivity
  unfold Ssum
  rcases hdF with rfl | rfl
  · have e : Finset.Icc 2 3 = {2, 3} := by decide
    rw [e, Finset.sum_pair (by norm_num)]
    linarith
  · have e : Finset.Icc 2 4 = {2, 3, 4} := by decide
    rw [e, Finset.sum_insert (by decide), Finset.sum_pair (by norm_num)]
    linarith

lemma eps2_pos (n : ℕ) (hn : 4096 ≤ n) : 0 < eps2 n := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  unfold eps2; positivity

lemma eps2_mul (n : ℕ) (hn : 4096 ≤ n) : (n : ℝ) ^ 3 * eps2 n = 4 / 10 ^ 9 := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  unfold eps2; field_simp

lemma eps2_le (n : ℕ) (hn : 4096 ≤ n) : eps2 n ≤ 1 / 10 ^ 9 := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h3 : (4096 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := by gcongr
  unfold eps2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem eta_num (n k : ℕ) (hn : 4096 ≤ n) (hk2 : k < n ^ 2) (s : ℝ) (hs : 0 < s)
    (h : (s ^ 2 - 1) ^ 2 < eps2 n) :
    s ^ 2 < 2 ∧ Real.sqrt ((Real.sqrt (s ^ 2 * (2 - s ^ 2)))⁻¹ ^ (k * n) - 1) ≤ 64 / 10 ^ 6 := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have he0 := eps2_pos n hn
  have he1 := eps2_le n hn
  set e := eps2 n with hedef
  have hs2 : s ^ 2 < 2 := by
    by_contra hc
    push Not at hc
    nlinarith
  refine ⟨hs2, ?_⟩
  set q : ℝ := 1 - e with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  have hq1 : q ≤ 1 := by rw [hq]; linarith
  have hP : q ≤ s ^ 2 * (2 - s ^ 2) := by
    have : s ^ 2 * (2 - s ^ 2) = 1 - (s ^ 2 - 1) ^ 2 := by ring
    rw [this, hq]; linarith
  have hsq : q ≤ Real.sqrt (s ^ 2 * (2 - s ^ 2)) := by
    refine Real.le_sqrt_of_sq_le ?_
    refine le_trans ?_ hP
    nlinarith
  have hinv : (Real.sqrt (s ^ 2 * (2 - s ^ 2)))⁻¹ ≤ 1 + e / q := by
    have h1 : (Real.sqrt (s ^ 2 * (2 - s ^ 2)))⁻¹ ≤ q⁻¹ := inv_anti₀ hq0 hsq
    refine h1.trans (le_of_eq ?_)
    have hq' : q ≠ 0 := hq0.ne'
    field_simp
    rw [hq]; ring
  have hy0 : 0 ≤ e / q := by positivity
  have hm : ((k * n : ℕ) : ℝ) ≤ (n : ℝ) ^ 3 := by
    have : k * n ≤ n ^ 3 := by
      calc k * n ≤ n ^ 2 * n := Nat.mul_le_mul_right _ hk2.le
        _ = n ^ 3 := by ring
    exact_mod_cast this
  have hmy : ((k * n : ℕ) : ℝ) * (e / q) ≤ 40001 / 10 ^ 13 := by
    have h1 : ((k * n : ℕ) : ℝ) * (e / q) ≤ (n : ℝ) ^ 3 * (e / q) := by gcongr
    have h2 : (n : ℝ) ^ 3 * (e / q) = 4 / 10 ^ 9 / q := by
      rw [← mul_div_assoc, eps2_mul n hn]
    rw [h2] at h1
    refine h1.trans ?_
    rw [div_le_iff₀ hq0]
    rw [hq]; nlinarith
  have hpow : (Real.sqrt (s ^ 2 * (2 - s ^ 2)))⁻¹ ^ (k * n) ≤
      1 / (1 - ((k * n : ℕ) : ℝ) * (e / q)) :=
    (pow_le_pow_left₀ (by positivity) hinv _).trans
      (BstLean.Part106.one_add_pow_le hy0 (k * n) (by linarith))
  rw [Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  have hden : 0 < 1 - ((k * n : ℕ) : ℝ) * (e / q) := by linarith
  have : 1 / (1 - ((k * n : ℕ) : ℝ) * (e / q)) ≤ 1 + (64 / 10 ^ 6) ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith
  linarith

theorem chiW_num (n dA : ℕ) (hn : 4096 ≤ n) (hdA : dA = 3 ∨ dA = 4) :
    2 / (eps2 n * (Fintype.card (CoefIdx (2 * n) n (2 * dA)) : ℝ)) ≤ 1 / (10 * (n : ℝ)) := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hD : 5242880000 * (n : ℝ) ^ 4 ≤ (Fintype.card (CoefIdx (2 * n) n (2 * dA)) : ℝ) := by
    rcases hdA with rfl | rfl
    · exact BstLean.Part106.card_six_ge hn
    · exact BstLean.Part106.card_eight_ge hn
  have he0 := eps2_pos n hn
  have hprod : 20 * (n : ℝ) ≤ eps2 n * (Fintype.card (CoefIdx (2 * n) n (2 * dA)) : ℝ) := by
    calc 20 * (n : ℝ) ≤ eps2 n * (5242880000 * (n : ℝ) ^ 4) := by
          have : eps2 n * (5242880000 * (n : ℝ) ^ 4) =
              5242880000 * n * ((n : ℝ) ^ 3 * eps2 n) := by ring
          rw [this, eps2_mul n hn]
          nlinarith
      _ ≤ _ := by gcongr
  rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hprod) (by positivity)]
  linarith

theorem total_le (hG : GMom108) (n dA dF k : ℕ) (hn : 4096 ≤ n) (hdA : dA = 3 ∨ dA = 4)
    (hdF : dF = 3 ∨ dF = 4) (hk : 1 ≤ k) {θ ι : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hι : 0 < ι)
    (hι1 : ι < 1) :
    coreBound n dA dF k θ ι +
        2 / (eps2 n * (Fintype.card (CoefIdx (2 * n) n (2 * dA)) : ℝ)) + 64 / 10 ^ 6 ≤
      delta108 n dA k θ ι := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hS := ssum_le hG n dA dF hn hdA hdF
  have hD := cardA_ge n dA hn hdA
  have hv := vbar_le n dA hn hdA
  have hchi := chiW_num n dA hn hdA
  set D : ℝ := (Fintype.card (CoefIdx n n dA) : ℝ) with hDdef
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hS0 : 0 ≤ Ssum n dA dF (4 / D) := Ssum_nonneg n dA dF (by positivity)
  have hc : 0 < ι ^ 2 * (1 - θ) := mul_pos (by positivity) (by linarith)
  have hlow : 2 * (n : ℝ) ≤ (n : ℝ) * ((dA : ℝ) + 1 - vbar dA n) := by nlinarith
  have t3 : 34 * Ssum n dA dF (4 / D) / (ι ^ 2 * (1 - θ) * ((n : ℝ) * ((dA : ℝ) + 1 - vbar dA n))) ≤
      10217 / (ι ^ 2 * (1 - θ) * (n : ℝ) ^ 3) := by
    calc _ ≤ 34 * (601 / (n : ℝ) ^ 2) / (ι ^ 2 * (1 - θ) * (2 * (n : ℝ))) := by
          gcongr
      _ = _ := by field_simp; ring
  have t4 : 32 / (9 * D) ≤ 1 / (90 * (n : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : (4096 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := by gcongr
    have : (n : ℝ) ^ 4 = n * (n : ℝ) ^ 3 := by ring
    nlinarith
  have e9 : 1 / (90 * (n : ℝ)) + 1 / (10 * (n : ℝ)) = 1 / (9 * (n : ℝ)) := by
    field_simp; norm_num
  unfold coreBound delta108
  rw [← hDdef]
  linarith

private lemma lam_le (n dA : ℕ) (hn : 4096 ≤ n) (hdA : dA = 3 ∨ dA = 4) :
    0 ≤ lam0 (2 * n) (2 * dA) ∧ lam0 (2 * n) (2 * dA) ≤ 25 / 10 ^ 6 := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  refine ⟨lam0_nonneg (N := 2 * n) (d := 2 * dA) (by omega) (by rcases hdA with h | h <;> omega), ?_⟩
  have h2 : 2 / (n : ℝ) ≤ 2 / 4096 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have h3 : 3 / (n : ℝ) ≤ 3 / 4096 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  rcases hdA with rfl | rfl
  · refine (lam0_bound n (by omega)).trans ?_
    have h1 : 1 / (10 * (n : ℝ)) ≤ 1 / (10 * 4096) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    calc 1 / (10 * (n : ℝ)) * (1 + 2 / (n : ℝ)) ≤ 1 / (10 * 4096) * (1 + 2 / 4096) := by gcongr
      _ ≤ _ := by norm_num
  · refine (BstLean.Part106.lam0_bound8 n (by omega)).trans ?_
    have h1 : 1 / (14 * (n : ℝ)) ≤ 1 / (14 * 4096) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    calc 1 / (14 * (n : ℝ)) * (1 + 3 / (n : ℝ)) ≤ 1 / (14 * 4096) * (1 + 3 / 4096) := by gcongr
      _ ≤ _ := by norm_num

/-- The four terms of `delta108`, each bounded by its value at `n = 4096`. -/
private lemma delta_core (n dA k : ℕ) (hn : 4096 ≤ n) (hdA : dA = 3 ∨ dA = 4) {θ ι K : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hι : 0 < ι) (hι1 : ι < 1) (hK : 0 < K) (hk : K ≤ k) :
    delta108 n dA k θ ι ≤
      (107 / 10) / (107 / 10 + 4096 * θ ^ 2) +
        4 * (25 / 10 ^ 6 + 1 / K) / ((1 - 25 / 10 ^ 6) * ((1 - ι) ^ 2 * (1 - θ))) +
        10217 / (ι ^ 2 * (1 - θ) * 4096 ^ 3) + (64 / 10 ^ 6 + 1 / (9 * 4096)) := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  obtain ⟨hl0, hl1⟩ := lam_le n dA hn hdA
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le hK hk
  have h1θ : 0 < 1 - θ := by linarith
  have h1ι : 0 < 1 - ι := by linarith
  have hk' : 1 / (k : ℝ) ≤ 1 / K := div_le_div_of_nonneg_left (by norm_num) hK hk
  have h3 : (4096 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := by gcongr
  unfold delta108
  have a1 : (107 / 10) / (107 / 10 + (n : ℝ) * θ ^ 2) ≤ (107 / 10) / (107 / 10 + 4096 * θ ^ 2) := by
    gcongr
  have a2 : 4 * (lam0 (2 * n) (2 * dA) + 1 / (k : ℝ)) /
      ((1 - lam0 (2 * n) (2 * dA)) * ((1 - ι) ^ 2 * (1 - θ))) ≤
      4 * (25 / 10 ^ 6 + 1 / K) / ((1 - 25 / 10 ^ 6) * ((1 - ι) ^ 2 * (1 - θ))) := by
    have hc : 0 < (1 - ι) ^ 2 * (1 - θ) := by positivity
    have hd1 : (0 : ℝ) < 1 - 25 / 10 ^ 6 := by norm_num
    have hd2 : (1 : ℝ) - 25 / 10 ^ 6 ≤ 1 - lam0 (2 * n) (2 * dA) := by linarith
    have hkk : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
    apply div_le_div₀ (by positivity) (by linarith) (by positivity)
    exact mul_le_mul_of_nonneg_right hd2 hc.le
  have a3 : 10217 / (ι ^ 2 * (1 - θ) * (n : ℝ) ^ 3) ≤ 10217 / (ι ^ 2 * (1 - θ) * 4096 ^ 3) := by
    gcongr
  have a4 : 1 / (9 * (n : ℝ)) ≤ 1 / (9 * 4096) := by gcongr
  linarith

theorem delta_k5000 (n dA k : ℕ) (hn : 4096 ≤ n) (hdA : dA = 3 ∨ dA = 4) (hk : 5000 ≤ k) :
    delta108 n dA k (7 / 10) (1 / 10) ≤ 1 / 100 := by
  have hk' : (5000 : ℝ) ≤ k := by exact_mod_cast hk
  refine (delta_core n dA k hn hdA (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hk').trans ?_
  norm_num

theorem delta_k1e6 (n dA k : ℕ) (hn : 4096 ≤ n) (hdA : dA = 3 ∨ dA = 4) (hk : 10 ^ 6 ≤ k) :
    delta108 n dA k (17 / 20) (1 / 10) ≤ 1 / 200 := by
  have hk' : ((10 : ℝ) ^ 6) ≤ k := by exact_mod_cast hk
  refine (delta_core n dA k hn hdA (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hk').trans ?_
  norm_num

end BstLean.Part108

#print axioms BstLean.Part108.vbar_le
#print axioms BstLean.Part108.cardA_ge
#print axioms BstLean.Part108.ssum_le
#print axioms BstLean.Part108.eta_num
#print axioms BstLean.Part108.chiW_num
#print axioms BstLean.Part108.total_le
#print axioms BstLean.Part108.delta_k5000
#print axioms BstLean.Part108.delta_k1e6
