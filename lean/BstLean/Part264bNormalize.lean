import BstLean.Part255Bounds
import BstLean.Part246TI

/-! Exact dimension normalization for the TI scalar formulas. -/
namespace BstLean.Part264b
open BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197 BstLean.Part246

noncomputable def invN (n : ℕ) : ℝ := 1 / n
noncomputable def nap (x : ℝ) : ℝ := 1 + √184 * x
noncomputable def nam (x : ℝ) : ℝ := √(1 - 2 * x ^ 2) - √184 * x
noncomputable def ndm (x c : ℝ) : ℝ := √(2 * (1 - kappa c) - 8 * x ^ 2) - 2 * √184 * x
noncomputable def nc1 (x c : ℝ) : ℝ := (2 * nap x ^ 2 - ndm x c ^ 2) / (2 * nam x ^ 2)
noncomputable def npa (c : ℝ) : ℝ := √(1 - c ^ 2) * kdot c
noncomputable def npp (c : ℝ) : ℝ := √(1 - c ^ 2) / π - c * kdot c
noncomputable def nr1 (x : ℝ) : ℝ := 12 * (√92 + 46 * x) * x
noncomputable def nrpp (x : ℝ) : ℝ := 8 * (√92 + 46 * x) * x
noncomputable def ne0 (x : ℝ) : ℝ := √184 * x
noncomputable def nlam (x c : ℝ) : ℝ := (npa c + nr1 x) / nam x + ne0 x
noncomputable def nrs (x : ℝ) : ℝ :=
  8 * (√(1 / 2 + √23 * x) + √92 * x) ^ 2 * (√92 + 46 * x) * x
noncomputable def nu (x c : ℝ) : ℝ :=
  (if 0 ≤ npp c + nrpp x then kdot (nc1 x c) * (npp c + nrpp x)
    else (npp c + nrpp x) / 2) +
  nlam x c ^ 2 / (π * √(1 - nc1 x c ^ 2)) + ne0 x ^ 2 + nrs x
noncomputable def nl (x c : ℝ) : ℝ :=
  kdot (nc1 x c) * min (npp c - nrpp x) 0 - ne0 x ^ 2 - nrs x
noncomputable def ns (x c : ℝ) : ℝ := max |nu x c| |nl x c|

theorem invN_bounds {n : ℕ} (hn : 12227 ≤ n) : B 0 (1 / 12227) (invN n) := by
  have hn' : (12227 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · unfold invN; positivity
  · unfold invN; gcongr

theorem root_div {n : ℕ} (hn : 0 < n) :
    √(2 / (n : ℝ)) = √2 / √(n : ℝ) :=
  sqrt_div (by norm_num) _

theorem root_mA {n : ℕ} : √(mA n : ℝ) = n := by
  simp [mA, Nat.cast_pow, sqrt_sq_eq_abs]

theorem root_mA92 {n : ℕ} : √(2 * (mA n : ℝ) * 46) = (n : ℝ) * √92 := by
  have he : 2 * (mA n : ℝ) * 46 = (n : ℝ) ^ 2 * 92 := by simp [mA]; ring
  rw [he, sqrt_mul (sq_nonneg _)]
  simp

theorem norm_ap {n : ℕ} (hn : 0 < n) : s3ap n 46 = √(n : ℝ) * nap (invN n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have ht0 : √(n : ℝ) ≠ 0 := by positivity
  have ht : √(n : ℝ) ^ 2 = n := sq_sqrt (by positivity)
  have hv : √92 * √2 = √184 := by rw [← sqrt_mul (by norm_num)]; norm_num
  unfold s3ap nap invN
  norm_num only
  rw [root_div hn]
  rw [← hv]
  field_simp
  generalize √(n : ℝ) = a at ht ⊢
  rw [← ht]
  ring

theorem norm_am {n : ℕ} (hn : 0 < n) : s3am n 46 = √(n : ℝ) * nam (invN n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hnr : (0 : ℝ) ≤ n := by positivity
  have he : (n : ℝ) - 2 / n = (n : ℝ) * (1 - 2 * invN n ^ 2) := by
    unfold invN; field_simp <;> ring
  have ha := norm_ap hn
  unfold s3am nam
  rw [he, sqrt_mul hnr]
  unfold s3ap nap at ha
  norm_num only at ha ⊢
  linarith

theorem norm_dm {n : ℕ} (hn : 0 < n) (c : ℝ) :
    s3dm n 46 c = √(n : ℝ) * ndm (invN n) c := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hnr : (0 : ℝ) ≤ n := by positivity
  have he : 2 * (n : ℝ) * (1 - kappa c) - 4 * (2 / n) =
      (n : ℝ) * (2 * (1 - kappa c) - 8 * invN n ^ 2) := by
    unfold invN; field_simp <;> ring
  have ha := norm_ap hn
  unfold s3dm ndm
  rw [he, sqrt_mul hnr]
  unfold s3ap nap at ha
  norm_num only at ha ⊢
  nlinarith

theorem norm_c1 {n : ℕ} (hn : 0 < n) (c : ℝ) : s3c1 n 46 c = nc1 (invN n) c := by
  have ht0 : √(n : ℝ) ≠ 0 := by positivity
  unfold s3c1 nc1
  rw [norm_ap hn, norm_am hn, norm_dm hn]
  simp only [mul_pow]
  have he : 2 * (√(n : ℝ)^2 * nap (invN n)^2) - √(n : ℝ)^2 * ndm (invN n) c^2 =
      √(n : ℝ)^2 * (2*nap (invN n)^2-ndm (invN n) c^2) := by ring
  rw [he, show 2*(√(n : ℝ)^2*nam (invN n)^2) =
    √(n : ℝ)^2*(2*nam (invN n)^2) by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero _ ht0)

theorem norm_pa {n : ℕ} (hn : 0 < n) (c : ℝ) : s3Cpa n c = (n : ℝ) * npa c := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold s3Cpa npa
  simp only [mA, Nat.cast_pow]
  field_simp <;> ring

theorem norm_pp {n : ℕ} (hn : 0 < n) (c : ℝ) : s3Cpp n c = (n : ℝ) * npp c := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold s3Cpp npp
  simp only [mA, Nat.cast_pow]
  field_simp <;> ring

theorem norm_r1 {n : ℕ} (hn : 0 < n) : s3r1 n 46 = (n : ℝ) * nr1 (invN n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold s3r1 nr1 invN
  rw [root_mA92]
  field_simp <;> ring

theorem norm_rpp {n : ℕ} (hn : 0 < n) : s3rpp n 46 = (n : ℝ) * nrpp (invN n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold s3rpp nrpp invN
  rw [root_mA92]
  field_simp <;> ring

theorem norm_e0 {n : ℕ} (hn : 0 < n) : s3e0 n 46 = √(n : ℝ) * ne0 (invN n) := by
  have ha := norm_ap hn
  unfold s3ap nap at ha
  unfold s3e0 ne0
  norm_num only at ha ⊢
  nlinarith

theorem norm_lam {n : ℕ} (hn : 0 < n) (c : ℝ) :
    s3Lam n 46 c = √(n : ℝ) * nlam (invN n) c := by
  have ht0 : √(n : ℝ) ≠ 0 := by positivity
  have ht : √(n : ℝ) ^ 2 = n := sq_sqrt (by positivity)
  unfold s3Lam nlam
  rw [norm_pa hn, norm_r1 hn, norm_am hn, norm_e0 hn]
  by_cases h : nam (invN n) = 0
  · simp [h]
  · field_simp
    generalize √(n : ℝ) = a at ht ⊢
    rw [← ht]
    ring

theorem root_K {n : ℕ} (b : ℝ) : √((mA n : ℝ) * b) = (n : ℝ) * √b := by
  simp only [mA, Nat.cast_pow]
  rw [sqrt_mul (sq_nonneg _)]
  simp

theorem norm_rs {n : ℕ} (hn : 0 < n) :
    s3rs n 46 (√23 / n) = (n : ℝ) * nrs (invN n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have ht0 : √(n : ℝ) ≠ 0 := by positivity
  have ht : √(n : ℝ) ^ 2 = n := sq_sqrt (by positivity)
  unfold s3rs s3pp s3K nrs invN
  rw [root_K, root_div hn, root_mA92]
  simp only [mA, Nat.cast_pow]
  norm_num only
  field_simp
  generalize √(n : ℝ) = a at ht ⊢
  rw [← ht]
  have h2 : √(2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  ring_nf
  rw [h2]
  ring

theorem norm_u {n : ℕ} (hn : 0 < n) (c : ℝ) :
    s3U n 46 (√23 / n) c = (n : ℝ) * nu (invN n) c := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : √(n : ℝ) ^ 2 = n := sq_sqrt hn0.le
  unfold s3U nu
  rw [norm_pp hn, norm_rpp hn, norm_c1 hn, norm_lam hn, norm_e0 hn, norm_rs hn]
  have hc : (0 : ℝ) ≤ (n : ℝ) * npp c + (n : ℝ) * nrpp (invN n) ↔
      0 ≤ npp c + nrpp (invN n) := by
    rw [← mul_add, mul_nonneg_iff_of_pos_left hn0]
  simp only [hc, mul_pow, ht]
  split_ifs <;> ring

theorem norm_l {n : ℕ} (hn : 0 < n) (c : ℝ) :
    s3L n 46 (√23 / n) c = (n : ℝ) * nl (invN n) c := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : √(n : ℝ) ^ 2 = n := sq_sqrt hn0.le
  unfold s3L nl
  rw [norm_pp hn, norm_rpp hn, norm_c1 hn, norm_e0 hn, norm_rs hn]
  rw [← mul_sub, ← mul_zero (n : ℝ), ← mul_min_of_nonneg _ _ hn0.le]
  simp only [mul_pow, ht]
  ring

theorem norm_s {n : ℕ} (hn : 0 < n) (c : ℝ) :
    s3nks n 46 (√23 / n) c = (n : ℝ) * ns (invN n) c := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold s3nks ns
  rw [norm_u hn, norm_l hn, abs_mul, abs_mul, abs_of_pos hn0]
  exact (mul_max_of_nonneg _ _ hn0.le).symm

noncomputable def neb (x b : ℝ) : ℝ := √2 * (√b + √x + √92 * x)
noncomputable def np1 (x : ℝ) : ℝ := √2 * (√2 * √x + 1 + √92 * √x)
noncomputable def ntf (x p : ℝ) : ℝ := √2 * (1 + (√2 + √92) * x) * p
noncomputable def nz (x : ℝ) : ℝ := √2 * (√2 * √x + √2 + √92 * √x)
noncomputable def nrad (x b : ℝ) : ℝ :=
  2 * (2 * √b * (√2 * √x + √92 * x) + (√2 * √x + √92 * x) ^ 2)
noncomputable def ne (x b l L p : ℝ) : ℝ :=
  ntf x p ^ 2 * x + 2 * ntf x p * nz x * l * x + nrad x b * l ^ 2 +
    2 * b * (L + p ^ 2 * x)
noncomputable def no (x : ℝ) : ℝ :=
  (√2 * (1 + √92 * √x)) *
  (√2 * (1 + (√3 + √92) * x + √(1 / 2 + √23 * x) + √92 * x)) *
  (√184 * √2 * (1 + √92 * x) * x * √x +
    2 * √x * (√(1 / 2 + √23 * x) + √92 * x) ^ 2)

theorem root_invN {n : ℕ} : √(invN n) = 1 / √(n : ℝ) := by
  unfold invN
  rw [sqrt_div (by norm_num)]
  norm_num

theorem root_two_mA {n : ℕ} : √(2 / (mA n : ℝ)) = √2 / (n : ℝ) := by
  rw [sqrt_div (by norm_num), root_mA]

theorem norm_eb {n : ℕ} (hn : 0 < n) (b : ℝ) :
    e4_b n ((mA n : ℝ) * b) 46 = √(n : ℝ) * neb (invN n) b := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have ht0 : √(n : ℝ) ≠ 0 := by positivity
  have ht : √(n : ℝ) ^ 2 = n := sq_sqrt (by positivity)
  unfold e4_b neb
  rw [root_K, root_div hn, root_invN]
  unfold invN
  norm_num only
  field_simp
  generalize √(n : ℝ) = a at ht ⊢
  rw [← ht]
  ring

theorem norm_p1 {n : ℕ} (hn : 0 < n) : e4_b n 2 46 = np1 (invN n) := by
  have ht0 : √(n : ℝ) ≠ 0 := by positivity
  unfold e4_b np1
  rw [root_div hn, root_invN]
  norm_num only
  field_simp <;> ring

theorem norm_e {n : ℕ} (hn : 0 < n) (b l L p : ℝ) :
    e3s_bound n ((mA n : ℝ) * b) (√(2 * 46)) (√(n : ℝ) * l)
      ((n : ℝ) * L) p = (n : ℝ) * ne (invN n) b l L p := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have ht0 : √(n : ℝ) ≠ 0 := by positivity
  have ht : √(n : ℝ) ^ 2 = n := sq_sqrt (by positivity)
  unfold e3s_bound ne ntf nz nrad
  rw [root_two_mA, root_mA, root_K, show (2 * 46 : ℝ) = 92 by norm_num,
    sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (n : ℝ), root_invN]
  simp only [mA, Nat.cast_pow]
  unfold invN
  norm_num only
  field_simp
  generalize √(n : ℝ) = a at ht ⊢
  rw [← ht]
  ring

theorem norm_o {n : ℕ} (hn : 0 < n) :
    o3_kO n 46 ((mA n : ℝ) * (1 / 2 + √23 / n))
      ((mA n : ℝ) * (1 / 2 + √23 / n)) = (n : ℝ) * no (invN n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have ht0 : √(n : ℝ) ≠ 0 := by positivity
  have ht : √(n : ℝ) ^ 2 = n := sq_sqrt (by positivity)
  have hv : √92 * √2 = √184 := by rw [← sqrt_mul (by norm_num)]; norm_num
  have h2 : √(2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  unfold o3_kO no
  rw [root_two_mA, root_mA, root_K, root_div hn, root_invN]
  unfold invN
  norm_num only
  rw [← hv]
  field_simp
  generalize √(n : ℝ) = a at ht ⊢
  rw [← ht]
  ring_nf
  simp only [h2]
  ring

theorem e3_normalized {n : ℕ} (hn : 0 < n) (c cp : ℝ) :
    e3s_bound n ((mA n : ℝ) * (kdot (s3c1 n 46 c) / 2 + √23 / n)) (√(2*46))
      (e4_b n ((mA n : ℝ) * (1/2 + √23 / n)) 46)
      (e4_b n ((mA n : ℝ) * (kdot cp / 2 + √23 / n)) 46 ^ 2) (e4_b n 2 46) =
    (n : ℝ) * ne (invN n) (kdot (nc1 (invN n) c) / 2 + √23 * invN n)
      (neb (invN n) (1/2 + √23 * invN n))
      (neb (invN n) (kdot cp/2 + √23 * invN n)^2) (np1 (invN n)) := by
  rw [norm_c1 hn, norm_eb hn, norm_eb hn, norm_p1 hn]
  simp only [mul_pow, sq_sqrt (by positivity : (0 : ℝ) ≤ n)]
  rw [norm_e hn]
  congr 1 <;> unfold invN <;> ring

end BstLean.Part264b
