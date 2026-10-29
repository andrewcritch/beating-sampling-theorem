import BstLean.Part90Main
import BstLean.Part90Osc

/-!
# Part 90: the arithmetic of the assembly at `(3, 3)`

Generic numeric lemmas: the size of `D_W` at `d = 3`, the scale ratio, the window constant
`cVW 3`, the Christoffel constant `SE 6`, and the variance term of the sphere step.

No `sorry`, no `native_decide`, no `axiom`.
-/

namespace BstLean.Part90

open BstLean.Part86 BstLean.Part89 BstLean.Part88

lemma choose3 (n : ℕ) : 6 * (n + 3).choose 3 = (n + 3) * (n + 2) * (n + 1) := by
  induction n with
  | zero => norm_num [Nat.choose]
  | succ k ih =>
    have h2 := choose2_86 (k + 1)
    have e : (k + 1 + 3).choose 3 = (k + 3).choose 2 + (k + 3).choose 3 := by
      rw [show k + 1 + 3 = (k + 3) + 1 from rfl, Nat.choose_succ_succ]
    have e2 : k + 1 + 2 = k + 3 := rfl
    rw [e2] at h2
    rw [e]
    nlinarith

/-- `D_W ≥ n⁴/6` at `d = 3`. -/
lemma DWr3_ge (n : ℕ) (hn : 100 ≤ n) : (n : ℝ) ^ 4 / 6 ≤ DWr n (JR n 3) := by
  rw [DWr_eq n 3 (by omega), BstLean.Part36.DD_eq]
  have h := choose3 n
  have h' : 6 * (((n + 3).choose 3 : ℕ) : ℝ) = ((n : ℝ) + 3) * ((n : ℝ) + 2) * ((n : ℝ) + 1) := by
    exact_mod_cast h
  have hn' : (100 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  nlinarith [pow_pos (by linarith : (0 : ℝ) < n) 2, pow_pos (by linarith : (0 : ℝ) < n) 3]

/-- The scale ratio at `β = 1/(600 n)`. -/
lemma tS3 (n : ℕ) (hn : 100000000 ≤ n) :
    0 ≤ tS n (1 / (600 * (n : ℝ))) ∧ tS n (1 / (600 * (n : ℝ))) ≤ 2 / 10000000 ∧
      tS n (1 / (600 * (n : ℝ))) ^ 2 * n ≤ 1 / 359000 := by
  have hN : (100000000 : ℝ) ≤ n := by exact_mod_cast hn
  set N : ℝ := (n : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  set s : ℝ := Real.sqrt N with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = N := Real.sq_sqrt hN0.le
  have h4 : (0 : ℝ) < 600 * N - 1 := by linarith
  have e : tS n (1 / (600 * N)) = s / (600 * N - 1) := by
    unfold tS
    have hb : 1 - 1 / (600 * N) = (600 * N - 1) / (600 * N) := by field_simp
    rw [← hNdef, ← hs, hb]
    field_simp
  rw [e]
  set T : ℝ := s / (600 * N - 1) with hT
  have hT0 : 0 ≤ T := div_nonneg hs0 h4.le
  have hTm : T * (600 * N - 1) = s := by rw [hT]; field_simp
  have hT2 : T ^ 2 * (600 * N - 1) ^ 2 = N := by rw [← mul_pow, hTm, hs2]
  have hq : N ^ 2 * 359000 ≤ (600 * N - 1) ^ 2 := by nlinarith
  have hTN : T ^ 2 * N ≤ 1 / 359000 := by
    have h1 : T ^ 2 * (N ^ 2 * 359000) ≤ N :=
      (mul_le_mul_of_nonneg_left hq (sq_nonneg T)).trans hT2.le
    have h2 : T ^ 2 * N * N ≤ 1 / 359000 * N := by nlinarith
    exact le_of_mul_le_mul_right h2 hN0
  refine ⟨hT0, ?_, hTN⟩
  by_contra hcon
  rw [not_le] at hcon
  have h1 : (2 / 10000000 : ℝ) ^ 2 < T ^ 2 := by nlinarith
  have h2 : T ^ 2 * 100000000 ≤ T ^ 2 * N := mul_le_mul_of_nonneg_left hN (sq_nonneg T)
  nlinarith

private lemma coreC (t L c a τ : ℝ) (ha : a = (1 + 3 * t) ^ (2 * 3) - 1)
    (hτ : τ = t * (1 + 3 * t) ^ 3)
    (ht0 : 0 ≤ t) (ht : t ≤ 2 / 10000000) (hL0 : 0 ≤ L) (hL : L ≤ 1 / 1000000) (hc : 0 ≤ c) :
    (1 + 1 / 20000) * c * (1 + (a + τ + τ ^ 2)) ^ 2 +
        (1 + 1 / (1 / 20000)) * (a + τ * (1 + τ) + L * (2 + (a + τ + τ ^ 2))) ^ 2 ≤
      100007 / 100000 * c + 14442800 * t ^ 2 + 160300 * L ^ 2 := by
  set u : ℝ := 1 + 3 * t with hu
  have hu1 : 1 ≤ u := by linarith
  have hu2 : u ≤ 1000001 / 1000000 := by linarith
  have hq2 : u ^ 2 ≤ 1000003 / 1000000 := by nlinarith
  have hq2' : 1 ≤ u ^ 2 := by nlinarith
  have hq3 : u ^ 3 ≤ 1000005 / 1000000 := by
    have := mul_le_mul hq2 hu2 (by linarith) (by norm_num)
    have e : u ^ 3 = u ^ 2 * u := by ring
    rw [e]; linarith
  have hq3' : 0 ≤ u ^ 3 := by positivity
  have hq4 : u ^ 4 ≤ 1000007 / 1000000 := by
    have := mul_le_mul hq3 hu2 (by linarith) (by norm_num)
    have e : u ^ 4 = u ^ 3 * u := by ring
    rw [e]; linarith
  have hq5 : u ^ 5 ≤ 1000009 / 1000000 := by
    have := mul_le_mul hq4 hu2 (by linarith) (by norm_num)
    have e : u ^ 5 = u ^ 4 * u := by ring
    rw [e]; linarith
  have haeq : a = 3 * t * (u ^ 5 + u ^ 4 + u ^ 3 + u ^ 2 + u + 1) := by rw [ha, hu]; ring
  have hprod0 : 0 ≤ u ^ 5 + u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := by positivity
  have ha0 : 0 ≤ a := by rw [haeq]; positivity
  have hale : a ≤ 180001 / 10000 * t := by
    rw [haeq]
    have := mul_le_mul_of_nonneg_left
      (by linarith : u ^ 5 + u ^ 4 + u ^ 3 + u ^ 2 + u + 1 ≤ 6000025 / 1000000)
      (by linarith : 0 ≤ 3 * t)
    linarith
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have hτle : τ ≤ 1000005 / 1000000 * t := by
    rw [hτ]
    have := mul_le_mul_of_nonneg_left hq3 ht0
    linarith
  have hτs : τ ≤ 3 / 10000000 := by linarith
  have hτ2 : τ ^ 2 ≤ 3 / 10000000 * τ := by nlinarith
  have hτ20 : 0 ≤ τ ^ 2 := sq_nonneg _
  set e1 : ℝ := a + τ + τ ^ 2 with he1
  have he10 : 0 ≤ e1 := by linarith
  have he1le : e1 ≤ 19001 / 1000 * t := by linarith
  have he1s : e1 ≤ 4 / 1000000 := by linarith
  set e2 : ℝ := a + τ * (1 + τ) + L * (2 + e1) with he2
  have he20 : 0 ≤ e2 := by
    have : 0 ≤ L * (2 + e1) := mul_nonneg hL0 (by linarith)
    have : τ * (1 + τ) = τ + τ ^ 2 := by ring
    linarith
  have he2le : e2 ≤ 19001 / 1000 * t + 2001 / 1000 * L := by
    have h1 : L * (2 + e1) ≤ L * (2001 / 1000) := mul_le_mul_of_nonneg_left (by linarith) hL0
    have : τ * (1 + τ) = τ + τ ^ 2 := by ring
    linarith
  have he2sq : e2 ^ 2 ≤ 7221 / 10 * t ^ 2 + 801 / 100 * L ^ 2 := by
    have h1 : e2 ^ 2 ≤ (19001 / 1000 * t + 2001 / 1000 * L) ^ 2 :=
      pow_le_pow_left₀ he20 he2le 2
    have h2 : (19001 / 1000 * t + 2001 / 1000 * L) ^ 2 =
        2 * (19001 / 1000) ^ 2 * t ^ 2 + 2 * (2001 / 1000) ^ 2 * L ^ 2 -
          (19001 / 1000 * t - 2001 / 1000 * L) ^ 2 := by ring
    have h3 := sq_nonneg (19001 / 1000 * t - 2001 / 1000 * L)
    have h4 := sq_nonneg t
    have h5 := sq_nonneg L
    rw [h2] at h1
    generalize (19001 / 1000 * t - 2001 / 1000 * L) ^ 2 = Z at h1 h3
    linarith
  have hsq1 : (1 + e1) ^ 2 ≤ 100001 / 100000 := by
    have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + e1)
      (by linarith : 1 + e1 ≤ 1000004 / 1000000) 2
    norm_num at this ⊢; linarith
  have hsq0 : 0 ≤ (1 + e1) ^ 2 := sq_nonneg _
  have hc1 : c * (1 + e1) ^ 2 ≤ c * (100001 / 100000) := mul_le_mul_of_nonneg_left hsq1 hc
  have hc0 : 0 ≤ c * (1 + e1) ^ 2 := mul_nonneg hc hsq0
  have he2sq0 : 0 ≤ e2 ^ 2 := sq_nonneg _
  have e51 : (1 + 1 / (1 / 20000) : ℝ) = 20001 := by norm_num
  rw [e51]
  have e3 : (1 + 1 / 20000 : ℝ) * c * (1 + e1) ^ 2 = 20001 / 20000 * (c * (1 + e1) ^ 2) := by ring
  rw [e3]
  generalize c * (1 + e1) ^ 2 = P at hc1 hc0
  generalize e2 ^ 2 = R at he2sq he2sq0
  have ht2n := sq_nonneg t
  have hL2n := sq_nonneg L
  linarith

/-- The window constant at `k = 3`, `ϑ = 1/20000`. -/
lemma cVW_le3 (t L c : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 2 / 10000000) (hL0 : 0 ≤ L)
    (hL : L ≤ 1 / 1000000) (hc : 0 ≤ c) :
    cVW 3 t L c (1 / 20000) ≤ 100007 / 100000 * c + 14442800 * t ^ 2 + 160300 * L ^ 2 := by
  unfold cVW e2S e1S a1S tauS
  simp only [Nat.cast_ofNat]
  exact coreC t L c _ _ rfl rfl ht0 ht hL0 hL hc

/-- The Christoffel constant at degree `6`, `ξ = 1/500`. -/
lemma SE6_le (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 1000000) :
    SE (2 * 3) β (1 / 500) ≤ 20001 / 10000 := by
  have s3 : Sodd 3 = 20 := by
    unfold Sodd; norm_num [Finset.sum_range_succ]
  have s2 : Sodd 2 = 4 := by
    unfold Sodd; norm_num [Finset.sum_range_succ]
  unfold SE
  have e1 : 2 * 3 / 2 = 3 := by norm_num
  have e2 : (2 * 3 - 1) / 2 = 2 := by norm_num
  rw [e1, e2]
  unfold SS
  rw [s3, s2]
  apply max_le
  · norm_num
  · have h1 : ((((2 / 2 : ℕ) : ℕ) : ℝ)) + 1 + 5 / 4 * (1 / 500 : ℝ) ^ 2 * 4 = 200002 / 100000 := by
      norm_num
    rw [h1]
    nlinarith

/-- The variance term of the sphere step, `b = 7/125`, `ξ = 1/500`. -/
lemma var3 (S W N L ν : ℝ) (hS : S ≤ 20001 / 10000) (hW : 0 ≤ W) (hN : 0 < N)
    (hL0 : 0 ≤ L) (hL : L ≤ 1 / 1000000) (hν : ν ≤ 1 / 10000) :
    S * (N * W) / ((1 - 7 / 125) ^ 2 * (1 - L) ^ 2 * N) / ((1 - (1 / 500) ^ 2) * (1 - ν)) ≤
      2245 / 1000 * W := by
  have h1 : (0 : ℝ) < 1 - L := by linarith
  have h2 : (0 : ℝ) < 1 - ν := by linarith
  have hp : (999998 : ℝ) / 1000000 ≤ (1 - L) ^ 2 := by nlinarith [sq_nonneg L]
  have hpq : (999998 : ℝ) / 1000000 * (9999 / 10000) ≤ (1 - L) ^ 2 * (1 - ν) :=
    mul_le_mul hp (by linarith) (by norm_num) (sq_nonneg _)
  have hden : (0 : ℝ) < (1 - 7 / 125) ^ 2 * (1 - L) ^ 2 * ((1 - (1 / 500) ^ 2) * (1 - ν)) := by
    positivity
  have e : S * (N * W) / ((1 - 7 / 125) ^ 2 * (1 - L) ^ 2 * N) / ((1 - (1 / 500) ^ 2) * (1 - ν)) =
      S * W / ((1 - 7 / 125) ^ 2 * (1 - L) ^ 2 * ((1 - (1 / 500) ^ 2) * (1 - ν))) := by
    field_simp
  rw [e, div_le_iff₀ hden]
  have hSW : S * W ≤ 20001 / 10000 * W := mul_le_mul_of_nonneg_right hS hW
  have hk : (20001 : ℝ) / 10000 ≤
      2245 / 1000 * ((1 - 7 / 125) ^ 2 * (1 - L) ^ 2 * ((1 - (1 / 500) ^ 2) * (1 - ν))) := by
    have : (1 - 7 / 125 : ℝ) ^ 2 * (1 - L) ^ 2 * ((1 - (1 / 500) ^ 2) * (1 - ν)) =
        ((118 / 125) ^ 2 * (249999 / 250000)) * ((1 - L) ^ 2 * (1 - ν)) := by ring
    rw [this]; linarith
  have := mul_le_mul_of_nonneg_right hk hW
  linarith

/-- The bound of `X = Xc …` in the generic form. -/
lemma X_gen (L ζ c1 c2 c3 c4 F q lam Z0 u u0 : ℝ) (hu : 0 < u) (hu0 : u ≤ u0)
    (hL : L = lam * u ^ 2) (hζ : ζ = Z0 * u) (hZ0 : 0 < Z0) (hlam : 0 ≤ lam)
    (hL1 : L < 1) (hq : 1 / (1 - L) ≤ q)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3) (hc4 : 0 ≤ c4) (hF : 0 ≤ F) :
    L * c3 / (1 - L) + ζ / 2 + L * (c1 + c3) / ((1 - L) * (2 * ζ)) +
        L * (c4 + (c2 + c4) / (2 * ζ)) * (F / (1 - L)) ≤
      (q * c3 * lam * u0 + Z0 / 2 + q * (c1 + c3) * lam / (2 * Z0) + q * F * c4 * lam * u0 +
        q * F * (c2 + c4) * lam / (2 * Z0)) * u := by
  have h1L : 0 < 1 - L := by linarith
  have hq0 : 0 ≤ 1 / (1 - L) := by positivity
  have hLz : L / ζ = lam / Z0 * u := by rw [hL, hζ]; field_simp
  have hLu : L ≤ lam * u0 * u := by
    rw [hL]
    have := mul_le_mul_of_nonneg_left hu0 (mul_nonneg hlam hu.le)
    nlinarith
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hζ0 : 0 < ζ := by rw [hζ]; positivity
  have e : L * c3 / (1 - L) + ζ / 2 + L * (c1 + c3) / ((1 - L) * (2 * ζ)) +
        L * (c4 + (c2 + c4) / (2 * ζ)) * (F / (1 - L)) =
      (1 / (1 - L)) * (c3 * L) + ζ / 2 + (1 / (1 - L)) * ((c1 + c3) * (L / ζ) / 2) +
        (1 / (1 - L)) * (F * c4 * L) + (1 / (1 - L)) * (F * (c2 + c4) * (L / ζ) / 2) := by
    field_simp
    ring
  rw [e, hLz]
  have t1 : (1 / (1 - L)) * (c3 * L) ≤ q * (c3 * (lam * u0 * u)) :=
    mul_le_mul hq (mul_le_mul_of_nonneg_left hLu hc3) (mul_nonneg hc3 hL0)
      (hq0.trans hq)
  have t3 : (1 / (1 - L)) * ((c1 + c3) * (lam / Z0 * u) / 2) ≤
      q * ((c1 + c3) * (lam / Z0 * u) / 2) :=
    mul_le_mul_of_nonneg_right hq (by positivity)
  have t4 : (1 / (1 - L)) * (F * c4 * L) ≤ q * (F * c4 * (lam * u0 * u)) :=
    mul_le_mul hq (mul_le_mul_of_nonneg_left hLu (mul_nonneg hF hc4))
      (mul_nonneg (mul_nonneg hF hc4) hL0) (hq0.trans hq)
  have t5 : (1 / (1 - L)) * (F * (c2 + c4) * (lam / Z0 * u) / 2) ≤
      q * (F * (c2 + c4) * (lam / Z0 * u) / 2) :=
    mul_le_mul_of_nonneg_right hq (by positivity)
  have e2 : (q * c3 * lam * u0 + Z0 / 2 + q * (c1 + c3) * lam / (2 * Z0) + q * F * c4 * lam * u0 +
        q * F * (c2 + c4) * lam / (2 * Z0)) * u =
      q * (c3 * (lam * u0 * u)) + Z0 * u / 2 + q * ((c1 + c3) * (lam / Z0 * u) / 2) +
        q * (F * c4 * (lam * u0 * u)) + q * (F * (c2 + c4) * (lam / Z0 * u) / 2) := by
    field_simp
  rw [e2, hζ]
  linarith

end BstLean.Part90
