import BstLean.Part189Defs
import BstLean.Part189Widths

namespace BstLean.Part189
open BstLean.Part130
noncomputable section

def countEnvelope (x w f j : ℝ) : ℝ :=
  2 * w ^ 2 + w * (6 * x + 4 * j + 6) + 6 * j + 20 +
  (2 * x ^ 4 + 16 * x ^ 3 + 15 * x ^ 2 + 6 * x + 21) +
  512 * x * (2 * x ^ 4 + 7 * x ^ 2 * f + 30 * x ^ 3 + 100 * x ^ 2) +
  (100 * x ^ 3 + 100 * f + 51200 * x + 100) +
  10 ^ 12 * (2 * x * f + 2 * f ^ 2 + 2 * f + 1 + 10 * x + 100) + 10 ^ 12 + 10

lemma paperCount_le_countEnvelope {n : ℕ} (hn : 1 ≤ n) :
    (paperCount n : ℝ) ≤ countEnvelope n (mW n) (mF n) (worldSigns n) := by
  rw [paperCount_eq hn]
  unfold countEnvelope
  push_cast
  have h : ((mF n - 1 : ℕ) : ℝ) ≤ (mF n : ℝ) := by exact_mod_cast Nat.sub_le (mF n) 1
  linarith

/-- This polynomial bounds the lower-order terms after the square-root bounds. -/
def overhead (d q x : ℝ) : ℝ :=
  4 / (q * d) * x ^ 6 + (1024 + 3590 / d) * x ^ 5 + (15362 + 18 / d) * x ^ 4 +
  (54900 + 10 ^ 12 * (2 + 2 / d)) * x ^ 3 +
  (15 + 10 / q + 100 / d + 10 ^ 12 * 6 / d) * x ^ 2 +
  (51212 + 12 * 10 ^ 12) * x + 279 + 106 * 10 ^ 12

lemma sqrt_upper {x d : ℝ} (hd : 0 < d) (hx : d ^ 2 ≤ x) : Real.sqrt x ≤ x / d := by
  have hx0 : 0 ≤ x := le_trans (sq_nonneg d) hx
  have hs := Real.sqrt_nonneg x
  have he := Real.sq_sqrt hx0
  have hds : d ≤ Real.sqrt x := (Real.le_sqrt hd.le hx0).mpr hx
  apply (le_div_iff₀ hd).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hds) hs]

lemma worldSigns_le {n : ℕ} {d q : ℝ} (hd : 0 < d) (hq : 0 < q)
    (hq2 : q ^ 2 ≤ d) (hn : d ^ 2 ≤ (n : ℝ)) :
    (worldSigns n : ℝ) ≤ (n : ℝ) ^ 2 / q + 2 := by
  have hx : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs : Real.sqrt n ≤ (n : ℝ) / q ^ 2 := by
    calc Real.sqrt n ≤ (n : ℝ) / d := sqrt_upper hd hn
      _ ≤ (n : ℝ) / q ^ 2 := div_le_div_of_nonneg_left hx (sq_pos_of_pos hq) hq2
  have hw : (mW n : ℝ) ≤ ((n : ℝ) ^ 2 / q + 1) ^ 2 := by
    calc (mW n : ℝ) ≤ (n : ℝ) ^ 3 * Real.sqrt n + 1 := widthW_le n
      _ ≤ (n : ℝ) ^ 3 * ((n : ℝ) / q ^ 2) + 1 := by gcongr
      _ ≤ ((n : ℝ) ^ 2 / q + 1) ^ 2 := by
        have he : (n : ℝ) ^ 3 * ((n : ℝ) / q ^ 2) = ((n : ℝ) ^ 2 / q) ^ 2 := by ring
        rw [he]
        have hp : 0 ≤ (n : ℝ) ^ 2 / q := by positivity
        nlinarith
  have ht : 0 ≤ (n : ℝ) ^ 2 / q + 1 := by positivity
  have hroot : Real.sqrt (mW n : ℝ) ≤ (n : ℝ) ^ 2 / q + 1 :=
    (Real.sqrt_le_iff).mpr ⟨ht, hw⟩
  have hceil := (Nat.ceil_lt_add_one (Real.sqrt_nonneg (mW n : ℝ))).le
  unfold worldSigns
  linarith

lemma envelope_expand {x d q : ℝ} (hx : 0 ≤ x) (hd : 0 < d) (hq : 0 < q) :
    countEnvelope x (x ^ 3 * Real.sqrt x + 1) (x * Real.sqrt x + 1) (x ^ 2 / q + 2) =
    2 * x ^ 7 +
    (4 / q * x ^ 5 + 3590 * x ^ 4 + 18 * x ^ 3 + 100 * x +
      10 ^ 12 * (2 * x ^ 2 + 6 * x)) * Real.sqrt x +
    1024 * x ^ 5 + 15362 * x ^ 4 + (54900 + 2 * 10 ^ 12) * x ^ 3 +
    (15 + 10 / q) * x ^ 2 + (51212 + 12 * 10 ^ 12) * x + 279 + 106 * 10 ^ 12 := by
  unfold countEnvelope
  ring_nf
  simp only [Real.sq_sqrt hx]
  ring

lemma countEnvelope_le_overhead {x d q : ℝ} (hd : 0 < d) (hq : 0 < q)
    (hx : d ^ 2 ≤ x) :
    countEnvelope x (x ^ 3 * Real.sqrt x + 1) (x * Real.sqrt x + 1) (x ^ 2 / q + 2) ≤
      2 * x ^ 7 + overhead d q x := by
  have hx0 : 0 ≤ x := le_trans (sq_nonneg d) hx
  have hc : 0 ≤ 4 / q * x ^ 5 + 3590 * x ^ 4 + 18 * x ^ 3 + 100 * x +
      10 ^ 12 * (2 * x ^ 2 + 6 * x) := by positivity
  have h := mul_le_mul_of_nonneg_left (sqrt_upper hd hx) hc
  rw [envelope_expand hx0 hd hq]
  have he : overhead d q x =
    (4 / q * x ^ 5 + 3590 * x ^ 4 + 18 * x ^ 3 + 100 * x +
      10 ^ 12 * (2 * x ^ 2 + 6 * x)) * (x / d) +
    1024 * x ^ 5 + 15362 * x ^ 4 + (54900 + 2 * 10 ^ 12) * x ^ 3 +
    (15 + 10 / q) * x ^ 2 + (51212 + 12 * 10 ^ 12) * x + 279 + 106 * 10 ^ 12 := by
      unfold overhead
      ring
  rw [he]
  linarith

theorem paperCount_le_polynomial {n : ℕ} {d q : ℝ} (hn : 1 ≤ n)
    (hd : 0 < d) (hq : 0 < q) (hq2 : q ^ 2 ≤ d) (hx : d ^ 2 ≤ (n : ℝ)) :
    (paperCount n : ℝ) ≤ 2 * (n : ℝ) ^ 7 + overhead d q n := by
  calc (paperCount n : ℝ) ≤ countEnvelope n (mW n) (mF n) (worldSigns n) :=
      paperCount_le_countEnvelope hn
    _ ≤ countEnvelope n ((n : ℝ) ^ 3 * Real.sqrt n + 1)
        ((n : ℝ) * Real.sqrt n + 1) ((n : ℝ) ^ 2 / q + 2) := by
      unfold countEnvelope
      gcongr
      all_goals first | exact widthW_le n | exact widthF_le n | exact worldSigns_le hd hq hq2 hx
    _ ≤ 2 * (n : ℝ) ^ 7 + overhead d q n := countEnvelope_le_overhead hd hq hx

lemma monomial_transfer {a x : ℝ} (ha : 0 < a) (hx : a ≤ x) {k : ℕ} (hk : k ≤ 7) :
    x ^ k ≤ (a ^ k / a ^ 7) * x ^ 7 := by
  have hr : 1 ≤ x / a := (le_div_iff₀ ha).mpr (by simpa using hx)
  have h := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr hk) (pow_nonneg ha.le k)
  have hleft : a ^ k * (x / a) ^ k = x ^ k := by
    rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ ha.ne')]
  have hright : a ^ k * (x / a) ^ 7 = (a ^ k / a ^ 7) * x ^ 7 := by ring
  rwa [hleft, hright] at h

lemma overhead_transfer {a x d q : ℝ} (ha : 0 < a) (hx : a ≤ x)
    (hd : 0 < d) (hq : 0 < q) :
    overhead d q x ≤ (overhead d q a / a ^ 7) * x ^ 7 := by
  have h0 := monomial_transfer ha hx (k := 0) (by omega)
  have h1 := monomial_transfer ha hx (k := 1) (by omega)
  have h2 := monomial_transfer ha hx (k := 2) (by omega)
  have h3 := monomial_transfer ha hx (k := 3) (by omega)
  have h4 := monomial_transfer ha hx (k := 4) (by omega)
  have h5 := monomial_transfer ha hx (k := 5) (by omega)
  have h6 := monomial_transfer ha hx (k := 6) (by omega)
  have H0 := mul_le_mul_of_nonneg_left h0
    (by norm_num : (0 : ℝ) ≤ 279 + 106 * 10 ^ 12)
  have H1 := mul_le_mul_of_nonneg_left h1
    (by norm_num : (0 : ℝ) ≤ 51212 + 12 * 10 ^ 12)
  have H2 := mul_le_mul_of_nonneg_left h2
    (by positivity : (0 : ℝ) ≤ 15 + 10 / q + 100 / d + 10 ^ 12 * 6 / d)
  have H3 := mul_le_mul_of_nonneg_left h3
    (by positivity : (0 : ℝ) ≤ 54900 + 10 ^ 12 * (2 + 2 / d))
  have H4 := mul_le_mul_of_nonneg_left h4
    (by positivity : (0 : ℝ) ≤ 15362 + 18 / d)
  have H5 := mul_le_mul_of_nonneg_left h5
    (by positivity : (0 : ℝ) ≤ 1024 + 3590 / d)
  have H6 := mul_le_mul_of_nonneg_left h6
    (by positivity : (0 : ℝ) ≤ 4 / (q * d))
  have H := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add H6 H5) H4) H3) H2) H1) H0
  unfold overhead
  convert H using 1 <;> ring

/-- One exact rational check at `a` gives an unbounded dimension theorem. -/
theorem paperCount_lt_of_certificate {a : ℕ} {d q c : ℝ}
    (ha : 1 ≤ a) (hd : 0 < d) (hq : 0 < q) (hq2 : q ^ 2 ≤ d)
    (ha2 : d ^ 2 ≤ (a : ℝ)) (hc : overhead d q a < (2 * c - 2) * (a : ℝ) ^ 7)
    {n : ℕ} (hn : a ≤ n) : (paperCount n : ℝ) < c * (2 * (n : ℝ) ^ 7) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ha)
  have hnx : (a : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le ha0 hnx
  have hratio : overhead d q a / (a : ℝ) ^ 7 < 2 * c - 2 :=
    (div_lt_iff₀ (pow_pos ha0 7)).mpr hc
  have hstrict := mul_lt_mul_of_pos_right hratio (pow_pos hn0 7)
  have hbound := paperCount_le_polynomial (le_trans ha hn) hd hq hq2 (le_trans ha2 hnx)
  have htrans := overhead_transfer ha0 hnx hd hq
  nlinarith

end
end BstLean.Part189
