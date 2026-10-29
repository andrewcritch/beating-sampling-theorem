import BstLean.Part247ERadius

/-! Part 247: a rational sufficient condition for the uniform sharp E bound. -/
namespace BstLean.Part247
open Real BstLean.Part130 BstLean.Part182 BstLean.Part244

theorem e_bound {n : ℕ} (hn : 11883 ≤ n) {c cp d0 d1 a ak R m kE : ℝ}
    (h0 : kdot cp ≤ d0) (h1 : kdot (s3c1 n 46 c) ≤ d1)
    (ha : 0 ≤ a) (ha2 : d0 + 2 * eta ≤ a^2)
    (hak : 0 ≤ ak) (hak2 : d1 / 2 + eta ≤ ak^2)
    (hm : a + 141422 / 100000 / 109 + 135647 / 10000 / 109^2 ≤ m)
    (hR : 4 * ak * (141422 / 100000 / 109 + 95917 / 10000 / 109^2) +
      8 / 109^4 + 2 * (141422 / 100000 / 109 + (95917 / 10000 + 2) / 109^2)^2 ≤ R)
    (hfin : (2205 / 1000)^2 / 109^2 +
      2 * (2205 / 1000) * (19659 / 10^6) * (101453 / 100000) / 109 +
      R * (101453 / 100000)^2 +
      (d1 + 2 * eta) * (m^2 + (155702 / 100000)^2 / 109^2) ≤ kE) :
    e3s_bound n ((mA n : ℝ) * (kdot (s3c1 n 46 c) / 2 + eta)) (√(2 * 46))
      (e4_b n ((mA n : ℝ) * (1 / 2 + eta)) 46)
      (e4_b n ((mA n : ℝ) * (kdot cp / 2 + eta)) 46 ^ 2)
      (e4_b n 2 46) ≤ n * kE := by
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set r := √(n : ℝ) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hn0
  have hr2 : r^2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hrlo : (109 : ℝ) ≤ r := Real.le_sqrt_of_sq_le (by nlinarith)
  have hrscale : r ≤ (n : ℝ) / 109 := by rw [← hr2]; nlinarith
  have hscale : (1 : ℝ) ≤ (n : ℝ) / 109^2 := by linarith
  have hη : 0 ≤ eta := by norm_num [eta]
  have hk0 := kdot_nonneg cp
  have hk1 := kdot_nonneg (s3c1 n 46 c)
  have hd1 : 0 ≤ d1 + 2 * eta := by linarith
  have hℓ := eb_bound hn (k := 1 / 2 + eta) (a := 1000405 / 10^6)
    (by positivity) (by norm_num) (by norm_num [eta])
  have hℓ' : e4_b n ((mA n : ℝ) * (1 / 2 + eta)) 46 ≤ r * (101453 / 100000) :=
    hℓ.trans (mul_le_mul_of_nonneg_left (by norm_num) hr0.le)
  have hL := eb_bound hn (k := kdot cp / 2 + eta) (a := a)
    (by positivity) ha (by linarith)
  have hL' : e4_b n ((mA n : ℝ) * (kdot cp / 2 + eta)) 46 ≤ r * m := by
    refine hL.trans (mul_le_mul_of_nonneg_left ?_ hr0.le)
    convert hm using 1 <;> ring
  have hp : e4_b n 2 46 ≤ (155702 / 100000 : ℝ) :=
    (pi_bound hn).trans (by norm_num)
  have ht : √(2 / (mA n : ℝ)) * (√(mA n : ℝ) + √2 + √(2 * 46)) ≤
      (141553 / 100000 : ℝ) := (tauf_bound hn).trans (by norm_num)
  have htau : √(2 / (mA n : ℝ)) * (√(mA n : ℝ) + √2 + √(2 * 46)) *
      e4_b n 2 46 ≤ (2205 / 1000 : ℝ) := by
    exact (mul_le_mul ht hp (by unfold e4_b; positivity) (by norm_num)).trans (by norm_num)
  have hz := zeta_bound hn
  have hrad := gram_radius_bound hn (k := kdot (s3c1 n 46 c) / 2 + eta)
    (by positivity) hak (by linarith) hR
  have hrad0 : 0 ≤ 2 / (mA n : ℝ) *
      (2 * √((mA n : ℝ) * (kdot (s3c1 n 46 c) / 2 + eta)) *
        (√(2 * (n : ℝ)) + √(2 * 46)) + 4 +
        (√(2 * (n : ℝ)) + √(2 * 46) + 2)^2) := by positivity
  have hR0 : 0 ≤ R := hrad0.trans hrad
  have hcoeff : 2 / (mA n : ℝ) *
      ((mA n : ℝ) * (kdot (s3c1 n 46 c) / 2 + eta)) ≤ d1 + 2 * eta := by
    have hm0 : (mA n : ℝ) ≠ 0 := by rw [en_M]; positivity
    field_simp
    nlinarith
  have hm0 : 0 ≤ m := by
    have : 0 ≤ a + 141422 / 100000 / 109 + 135647 / 10000 / 109^2 := by positivity
    linarith
  have hℓ0 : 0 ≤ e4_b n ((mA n : ℝ) * (1 / 2 + eta)) 46 := by unfold e4_b; positivity
  have hL0 : 0 ≤ e4_b n ((mA n : ℝ) * (kdot cp / 2 + eta)) 46 := by unfold e4_b; positivity
  have hp0 : 0 ≤ e4_b n 2 46 := by unfold e4_b; positivity
  have hmain : e3s_bound n ((mA n : ℝ) * (kdot (s3c1 n 46 c) / 2 + eta)) (√(2 * 46))
      (e4_b n ((mA n : ℝ) * (1 / 2 + eta)) 46)
      (e4_b n ((mA n : ℝ) * (kdot cp / 2 + eta)) 46 ^ 2)
      (e4_b n 2 46) ≤
      (2205 / 1000)^2 + 2 * (2205 / 1000) * (19659 / 10^6) *
        (r * (101453 / 100000)) + R * (r * (101453 / 100000))^2 +
        (d1 + 2 * eta) * ((r * m)^2 + (155702 / 100000)^2) := by
    unfold e3s_bound
    gcongr
  refine hmain.trans ?_
  have hA := mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ (2205 / 1000)^2)
  have hB := mul_le_mul_of_nonneg_left hrscale
    (by norm_num : (0 : ℝ) ≤ 2 * (2205 / 1000) * (19659 / 10^6) * (101453 / 100000))
  have hC := mul_le_mul_of_nonneg_left hscale
    (mul_nonneg hd1 (sq_nonneg (155702 / 100000)))
  have hD := mul_le_mul_of_nonneg_left hfin hn0.le
  rw [mul_pow, mul_pow, hr2]
  nlinarith only [hA, hB, hC, hD]

end BstLean.Part247
