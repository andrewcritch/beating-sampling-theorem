import BstLean.Part182OBlk3
import BstLean.Part182SBlk3
import BstLean.Part183UENum
import BstLean.Part182TIA

/-!
# Part 183 (file `USNum`): the numerics of Lemma TI's S and O blocks at `τ = 46`, `n ≥ 19 000`

No proof is left open; no `native_decide` or `axiom` is used. Rational constants were chosen with a
single-process python calculator; Lean checks every inequality.

A copy of Part 182's file `SNum` (names prefixed `u`, namespace `BstLean.Part183.U`) with the floor
`19 000` (`√n ≥ 137.8`), `η = 253/10⁶`, the window `0.374 ≤ c ≤ 0.65`, and the `n`-dependent
constants `ε₀/√n ≤ 714·10⁻⁶`, `a₋ ≥ √n(1 − 715·10⁻⁶)`, `r₁ ≤ 0.00606n`, `r_pp ≤ 0.00405n`,
`r_s ≤ 0.002025n`.
* **`usn_ko`**: `≤ 0.027·n` (value `≈ 0.0266`).
* **`usn_S`**: `s3nks n 46 η c ≤ 0.182·n` (twelve cells, worst `≈ 0.1805` at the first cell).
* **`usn_ta_num`** (with `uen_kE`: `k_E = 0.725`), **`usn_lam`** (`≤ 0.73`, value `≈ 0.7264`),
  **`usn_TI`**.
-/

namespace BstLean.Part183.U

open BstLean.Part182

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130

lemma usn_inv_sqrt_le {t : ℝ} (h1 : 0 ≤ t) (h2 : t ≤ 3 / 4) :
    1 / Real.sqrt (1 - t ^ 2) ≤ 1 + t ^ 2 / 2 + 3 / 8 * t ^ 4 + 7 / 10 * t ^ 6 := by
  set y := t ^ 2 with hy
  have hy0 : 0 ≤ y := sq_nonneg t
  have hy1 : y ≤ 9 / 16 := by rw [hy]; nlinarith
  have hpos : 0 < 1 - y := by linarith
  have hs : 0 < Real.sqrt (1 - y) := Real.sqrt_pos.mpr hpos
  have hss : Real.sqrt (1 - y) ^ 2 = 1 - y := Real.sq_sqrt hpos.le
  have e4 : t ^ 4 = y ^ 2 := by rw [hy]; ring
  have e6 : t ^ 6 = y ^ 3 := by rw [hy]; ring
  rw [e4, e6]
  have hq : 0 < 1 + y / 2 + 3 / 8 * y ^ 2 + 7 / 10 * y ^ 3 := by positivity
  have hid : (1 + y / 2 + 3 / 8 * y ^ 2 + 7 / 10 * y ^ 3) ^ 2 * (1 - y) =
      1 + y ^ 3 * (31 / 40 - 299 / 320 * y - 101 / 320 * y ^ 2 - 7 / 200 * y ^ 3 - 49 / 100 * y ^ 4) := by
    ring
  have hy2 : y ^ 2 ≤ (9 / 16) ^ 2 := pow_le_pow_left₀ hy0 hy1 2
  have hy3 : y ^ 3 ≤ (9 / 16) ^ 3 := pow_le_pow_left₀ hy0 hy1 3
  have hy4 : y ^ 4 ≤ (9 / 16) ^ 4 := pow_le_pow_left₀ hy0 hy1 4
  have hin : 0 ≤ 31 / 40 - 299 / 320 * y - 101 / 320 * y ^ 2 - 7 / 200 * y ^ 3 - 49 / 100 * y ^ 4 := by
    nlinarith
  have hsq : 1 ≤ ((1 + y / 2 + 3 / 8 * y ^ 2 + 7 / 10 * y ^ 3) * Real.sqrt (1 - y)) ^ 2 := by
    rw [mul_pow, hss, hid]
    have := mul_nonneg (pow_nonneg hy0 3) hin
    linarith
  have hle : 1 ≤ (1 + y / 2 + 3 / 8 * y ^ 2 + 7 / 10 * y ^ 3) * Real.sqrt (1 - y) := by
    have hm := mul_pos hq hs
    by_contra hc
    rw [not_le] at hc
    nlinarith
  rw [div_le_iff₀ hs]
  exact hle

lemma usn_hasDerivAt_polyU (t : ℝ) :
    HasDerivAt (fun t : ℝ => t + t ^ 3 / 6 + 3 * t ^ 5 / 40 + t ^ 7 / 10)
      (1 + t ^ 2 / 2 + 3 / 8 * t ^ 4 + 7 / 10 * t ^ 6) t := by
  have h := (((hasDerivAt_id' t).add ((hasDerivAt_pow 3 t).div_const 6)).add
    (((hasDerivAt_pow 5 t).const_mul 3).div_const 40)).add ((hasDerivAt_pow 7 t).div_const 10)
  refine h.congr_deriv ?_
  norm_num
  ring

/-- `arcsin t ≤ t + t³/6 + 3t⁵/40 + t⁷/10` on `[0, 3/4]`. -/
theorem usn_arcsin_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 3 / 4) :
    Real.arcsin t ≤ t + t ^ 3 / 6 + 3 * t ^ 5 / 40 + t ^ 7 / 10 := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) (3 / 4), HasDerivAt
      (fun x : ℝ => (x + x ^ 3 / 6 + 3 * x ^ 5 / 40 + x ^ 7 / 10) - Real.arcsin x)
      ((1 + x ^ 2 / 2 + 3 / 8 * x ^ 4 + 7 / 10 * x ^ 6) - 1 / Real.sqrt (1 - x ^ 2)) x :=
    fun x hx => (usn_hasDerivAt_polyU x).sub
      (Real.hasDerivAt_arcsin (by linarith [hx.1]) (by linarith [hx.2]))
  have hmono : MonotoneOn
      (fun x : ℝ => (x + x ^ 3 / 6 + 3 * x ^ 5 / 40 + x ^ 7 / 10) - Real.arcsin x)
      (Icc 0 (3 / 4)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · have := Real.continuous_arcsin
      exact (by fun_prop : Continuous
        (fun x : ℝ => (x + x ^ 3 / 6 + 3 * x ^ 5 / 40 + x ^ 7 / 10) - Real.arcsin x)).continuousOn
    · rw [interior_Icc]
      exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hd x hx).deriv]
      have := usn_inv_sqrt_le hx.1.le hx.2.le
      linarith
  have h := hmono (left_mem_Icc.mpr (by norm_num)) ⟨h0, h1⟩ h0
  simp only [Real.arcsin_zero] at h
  norm_num at h
  linarith

lemma usn_sqrt_ge_poly {t : ℝ} (h1 : 0 ≤ t) (h2 : t < 1) :
    1 + t ^ 2 / 2 + 3 / 8 * t ^ 4 ≤ 1 / Real.sqrt (1 - t ^ 2) := by
  set y := t ^ 2 with hy
  have hy0 : 0 ≤ y := sq_nonneg t
  have hy1 : y < 1 := by rw [hy]; nlinarith
  have hpos : 0 < 1 - y := by linarith
  have hs : 0 < Real.sqrt (1 - y) := Real.sqrt_pos.mpr hpos
  have hss : Real.sqrt (1 - y) ^ 2 = 1 - y := Real.sq_sqrt hpos.le
  have e4 : t ^ 4 = y ^ 2 := by rw [hy]; ring
  rw [e4, le_div_iff₀ hs]
  have hq : 0 ≤ 1 + y / 2 + 3 / 8 * y ^ 2 := by positivity
  have hid : ((1 + y / 2 + 3 / 8 * y ^ 2) * Real.sqrt (1 - y)) ^ 2 =
      1 - y ^ 3 * (5 / 8 + 15 / 64 * y + 9 / 64 * y ^ 2) := by
    rw [mul_pow, hss]; ring
  have hle : ((1 + y / 2 + 3 / 8 * y ^ 2) * Real.sqrt (1 - y)) ^ 2 ≤ 1 := by
    rw [hid]; have : 0 ≤ y ^ 3 * (5 / 8 + 15 / 64 * y + 9 / 64 * y ^ 2) := by positivity
    linarith
  have h0 : 0 ≤ (1 + y / 2 + 3 / 8 * y ^ 2) * Real.sqrt (1 - y) := by positivity
  nlinarith

/-- `t + t³/6 + 3t⁵/40 ≤ arcsin t` on `[0, 1)`. -/
theorem usn_arcsin_ge {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 3 / 4) :
    t + t ^ 3 / 6 + 3 * t ^ 5 / 40 ≤ Real.arcsin t := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) (3 / 4), HasDerivAt
      (fun x : ℝ => Real.arcsin x - (x + x ^ 3 / 6 + 3 * x ^ 5 / 40))
      (1 / Real.sqrt (1 - x ^ 2) - (1 + x ^ 2 / 2 + 3 / 8 * x ^ 4)) x := by
    intro x hx
    have h := ((hasDerivAt_id' x).add ((hasDerivAt_pow 3 x).div_const 6)).add
      (((hasDerivAt_pow 5 x).const_mul 3).div_const 40)
    refine (Real.hasDerivAt_arcsin (by linarith [hx.1]) (by linarith [hx.2])).sub
      (h.congr_deriv ?_)
    norm_num; ring
  have hmono : MonotoneOn (fun x : ℝ => Real.arcsin x - (x + x ^ 3 / 6 + 3 * x ^ 5 / 40))
      (Icc 0 (3 / 4)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · have := Real.continuous_arcsin
      exact (by fun_prop : Continuous
        (fun x : ℝ => Real.arcsin x - (x + x ^ 3 / 6 + 3 * x ^ 5 / 40))).continuousOn
    · rw [interior_Icc]
      exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hd x hx).deriv]
      have := usn_sqrt_ge_poly hx.1.le (by linarith [hx.2])
      linarith
  have h := hmono (left_mem_Icc.mpr (by norm_num)) ⟨h0, h1⟩ h0
  simp only [Real.arcsin_zero] at h
  norm_num at h
  linarith

lemma usn_kdot_eq (q : ℝ) : kdot q = 1 / 2 + Real.arcsin q / π := by
  unfold kdot
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  field_simp
  ring

lemma usn_kappa_eq (t : ℝ) :
    kappa t = (√(1 - t ^ 2) + t * (π / 2 + Real.arcsin t)) / π := by
  unfold kappa
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  ring_nf

lemma usn_pi_lo : (3141592 / 1000000 : ℝ) < π := by have := Real.pi_gt_d6; norm_num at this ⊢; linarith
lemma usn_pi_hi : π < (3141593 / 1000000 : ℝ) := by have := Real.pi_lt_d6; norm_num at this ⊢; linarith

/-- `κ̇(t) ≤ 1/2 + (t + t³/6 + 3t⁵/40 + t⁷/10)/3.141592` on `[0, 3/4]`. -/
lemma usn_kdot_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 3 / 4) :
    kdot t ≤ 1 / 2 + (t + t ^ 3 / 6 + 3 * t ^ 5 / 40 + t ^ 7 / 10) / (3141592 / 1000000) := by
  rw [usn_kdot_eq]
  have ha := usn_arcsin_le h0 h1
  have hp := usn_pi_lo
  have hpos : 0 ≤ Real.arcsin t := Real.arcsin_nonneg.2 h0
  have : Real.arcsin t / π ≤ Real.arcsin t / (3141592 / 1000000) :=
    div_le_div_of_nonneg_left hpos (by norm_num) hp.le
  have : Real.arcsin t / (3141592 / 1000000) ≤
      (t + t ^ 3 / 6 + 3 * t ^ 5 / 40 + t ^ 7 / 10) / (3141592 / 1000000) :=
    div_le_div_of_nonneg_right ha (by norm_num)
  linarith

/-- `1/2 + (t + t³/6 + 3t⁵/40)/3.141593 ≤ κ̇(t)` on `[0, 3/4]`. -/
lemma usn_kdot_ge {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 3 / 4) :
    1 / 2 + (t + t ^ 3 / 6 + 3 * t ^ 5 / 40) / (3141593 / 1000000) ≤ kdot t := by
  rw [usn_kdot_eq]
  have ha := usn_arcsin_ge h0 h1
  have hp := usn_pi_hi
  have hp0 : 0 < π := Real.pi_pos
  have hq : 0 ≤ t + t ^ 3 / 6 + 3 * t ^ 5 / 40 := by positivity
  have : (t + t ^ 3 / 6 + 3 * t ^ 5 / 40) / (3141593 / 1000000) ≤
      (t + t ^ 3 / 6 + 3 * t ^ 5 / 40) / π := div_le_div_of_nonneg_left hq hp0 hp.le
  have : (t + t ^ 3 / 6 + 3 * t ^ 5 / 40) / π ≤ Real.arcsin t / π :=
    div_le_div_of_nonneg_right ha hp0.le
  linarith

/-- `κ(t) ≤ (s + t(3.141593/2 + t + t³/6 + 3t⁵/40 + t⁷/10))/3.141592` when `√(1 − t²) ≤ s`. -/
lemma usn_kappa_le {t s : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 3 / 4) (hs : √(1 - t ^ 2) ≤ s) :
    kappa t ≤ (s + t * (3141593 / 2000000 + (t + t ^ 3 / 6 + 3 * t ^ 5 / 40 + t ^ 7 / 10))) /
      (3141592 / 1000000) := by
  rw [usn_kappa_eq]
  have ha := usn_arcsin_le h0 h1
  have hp := usn_pi_lo
  have hp2 := usn_pi_hi
  have hnum : √(1 - t ^ 2) + t * (π / 2 + Real.arcsin t) ≤
      s + t * (3141593 / 2000000 + (t + t ^ 3 / 6 + 3 * t ^ 5 / 40 + t ^ 7 / 10)) := by
    have : t * (π / 2 + Real.arcsin t) ≤
        t * (3141593 / 2000000 + (t + t ^ 3 / 6 + 3 * t ^ 5 / 40 + t ^ 7 / 10)) :=
      mul_le_mul_of_nonneg_left (by linarith) h0
    linarith
  have hn0 : 0 ≤ √(1 - t ^ 2) + t * (π / 2 + Real.arcsin t) := by
    have := Real.arcsin_nonneg.2 h0
    have := Real.pi_pos
    positivity
  calc (√(1 - t ^ 2) + t * (π / 2 + Real.arcsin t)) / π
      ≤ (√(1 - t ^ 2) + t * (π / 2 + Real.arcsin t)) / (3141592 / 1000000) :=
        div_le_div_of_nonneg_left hn0 (by norm_num) hp.le
    _ ≤ _ := div_le_div_of_nonneg_right hnum (by norm_num)

/-- The fixed mask slack `η = 23/100000` (the same as Part182ENum). -/
noncomputable def usnEta : ℝ := 253 / 1000000

/-- `2η²m ≥ 46` for `n ≥ 21 000` (so `e^{−2η²m} ≤ e^{−46}`). -/
lemma usn_eta_ok {n : ℕ} (hn : 19000 ≤ n) : 46 ≤ 2 * usnEta ^ 2 * ((mA n : ℕ) : ℝ) := by
  have hnR : (19000 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  rw [hm, usnEta]
  nlinarith

lemma usn_sqrt_le {a b : ℝ} (hb : 0 ≤ b) (h : a ≤ b ^ 2) : √a ≤ b :=
  (Real.sqrt_le_sqrt h).trans (le_of_eq (Real.sqrt_sq hb))

/-- **The O-block constant**: `o3_kO n 46 K K ≤ 0.026·n` for `K = m(1/2 + 23/100000)`, every
`n ≥ 21 000` (paper `k_o ≈ 0.0246`). -/
theorem usn_ko {n : ℕ} (hn : 19000 ≤ n) :
    o3_kO n 46 (((mA n : ℕ) : ℝ) * (1 / 2 + usnEta)) (((mA n : ℕ) : ℝ) * (1 / 2 + usnEta)) ≤
      (n : ℝ) * (27 / 1000) := by
  have hnR : (19000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set r := √(n : ℝ) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hn0
  have hrr : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hr1 : (1378 / 10 : ℝ) ≤ r := by
    rw [hr]; exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hsm : √(((mA n : ℕ) : ℝ)) = n := by rw [hm, Real.sqrt_sq hn0.le]
  set s := √(1 / 2 + usnEta) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 70729 / 100000 := usn_sqrt_le (by norm_num) (by rw [usnEta]; norm_num)
  have hK : √(((mA n : ℕ) : ℝ) * (1 / 2 + usnEta)) = n * s := by
    rw [Real.sqrt_mul (by positivity), hsm]
  set v := √(2 * (46 : ℝ)) with hv
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hv1 : v ≤ 95917 / 10000 := usn_sqrt_le (by norm_num) (by norm_num)
  set t3 := √(3 : ℝ) with ht3
  have ht30 : 0 ≤ t3 := Real.sqrt_nonneg _
  have ht31 : t3 ≤ 17321 / 10000 := usn_sqrt_le (by norm_num) (by norm_num)
  have h2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hg : √(2 / (n : ℝ)) = √2 / r := by rw [Real.sqrt_div (by norm_num)]
  have hgm : √(2 / ((mA n : ℕ) : ℝ)) = √2 / n := by
    rw [Real.sqrt_div (by norm_num), hsm]
  unfold o3_kO
  rw [hK, hg, hgm, hsm, ← hv]
  set u := 1 / r with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 10 / 1378 := by
    rw [hu, div_le_div_iff₀ hr0 (by norm_num)]; linarith
  have hnr : (n : ℝ) = 1 / u ^ 2 := by rw [hu, ← hrr]; field_simp
  have hru : r = 1 / u := by rw [hu]; field_simp
  -- the closed form `n·G(u)`
  have key : (√2 / r * (r + v)) * (√2 / n * ((n + t3 + v) + (n * s + v))) *
      (√2 / r * v * (√2 / n * (n + v)) + √2 / n * (n * s + v) * (√2 / r * (n * s + v))) =
      (n : ℝ) * (4 * (1 + v * u) * ((1 + s) + (t3 + 2 * v) * u ^ 2) *
        (v * u ^ 3 * (1 + v * u ^ 2) + u * (s + v * u ^ 2) ^ 2)) := by
    have hu' : u ≠ 0 := by positivity
    rw [hnr, hru]
    have h4 : √(2 : ℝ) ^ 4 = 4 := by rw [show √(2 : ℝ) ^ 4 = (√2 ^ 2) ^ 2 by ring, h2]; norm_num
    field_simp
    rw [h4]
    ring
  rw [key]
  refine mul_le_mul_of_nonneg_left ?_ hn0.le
  have e1 : 1 + v * u ≤ 1 + 95917 / 10000 * (10 / 1378) := by gcongr
  have e2 : (1 + s) + (t3 + 2 * v) * u ^ 2 ≤
      (1 + 70729 / 100000) + (17321 / 10000 + 2 * (95917 / 10000)) * (10 / 1378) ^ 2 := by gcongr
  have e3 : v * u ^ 3 * (1 + v * u ^ 2) + u * (s + v * u ^ 2) ^ 2 ≤
      95917 / 10000 * (10 / 1378) ^ 3 * (1 + 95917 / 10000 * (10 / 1378) ^ 2) +
        10 / 1378 * (70729 / 100000 + 95917 / 10000 * (10 / 1378) ^ 2) ^ 2 := by gcongr
  calc 4 * (1 + v * u) * ((1 + s) + (t3 + 2 * v) * u ^ 2) *
        (v * u ^ 3 * (1 + v * u ^ 2) + u * (s + v * u ^ 2) ^ 2)
      ≤ 4 * (1 + 95917 / 10000 * (10 / 1378)) *
          ((1 + 70729 / 100000) + (17321 / 10000 + 2 * (95917 / 10000)) * (10 / 1378) ^ 2) *
          (95917 / 10000 * (10 / 1378) ^ 3 * (1 + 95917 / 10000 * (10 / 1378) ^ 2) +
            10 / 1378 * (70729 / 100000 + 95917 / 10000 * (10 / 1378) ^ 2) ^ 2) := by
        gcongr
    _ ≤ 27 / 1000 := by norm_num

/-! ## The S block: reduction of the constants to numbers -/

/-- `M(c) = √(1 − c²)/π − c·κ̇(c)`. -/
noncomputable def usnM (c : ℝ) : ℝ := √(1 - c ^ 2) / π - c * kdot c

/-- `V(c) = √(1 − c²)·κ̇(c)`. -/
noncomputable def usnV (c : ℝ) : ℝ := √(1 - c ^ 2) * kdot c

lemma usn_inv_le {x a k : ℝ} (hx : 19000 ≤ x) (ha : 0 ≤ a) (hk : a ≤ k * 19000 * 19000) :
    a / x ≤ k * x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hk0 : 0 ≤ k := by nlinarith
  rw [div_le_iff₀ hx0]
  have : k * 19000 * 19000 ≤ k * x * x := by
    have h1 : (19000 : ℝ) * 19000 ≤ x * x := mul_le_mul hx hx (by norm_num) hx0.le
    nlinarith
  linarith

lemma usn_rs_le {n : ℕ} (hn : 19000 ≤ n) : s3rs n 46 usnEta ≤ n * (2025 / 10 ^ 6) := by
  have hnR : (19000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hsm : √(((mA n : ℕ) : ℝ)) = n := by rw [hm, Real.sqrt_sq hn0.le]
  set s := √(1 / 2 + usnEta) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 70729 / 100000 := usn_sqrt_le (by norm_num) (by rw [usnEta]; norm_num)
  have hK : √(s3K n usnEta) = n * s := by
    unfold s3K; rw [Real.sqrt_mul (by positivity), hsm]
  set v := √(2 * (46 : ℝ)) with hv
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hv1 : v ≤ 95917 / 10000 := usn_sqrt_le (by norm_num) (by norm_num)
  have hsq2 : √(2 * ((mA n : ℕ) : ℝ) * 46) = n * v := by
    rw [hm, show 2 * (n : ℝ) ^ 2 * 46 = (n : ℝ) ^ 2 * (2 * 46) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hn0.le]
  have hpp : s3pp n 46 usnEta ^ 2 = 2 / n * (n * s + v) ^ 2 := by
    unfold s3pp; rw [hK, ← hv, mul_pow, Real.sq_sqrt (by positivity)]
  have hrs : s3rs n 46 usnEta = 8 * (n * s + v) ^ 2 * (n * v + 46) / (n : ℝ) ^ 3 := by
    unfold s3rs; rw [hpp, hsq2, hm]; field_simp; ring
  rw [hrs, div_le_iff₀ (by positivity)]
  have hA : n * s + v ≤ n * (70780 / 100000) := by
    have : v ≤ n * (51 / 100000) := by nlinarith
    nlinarith
  have hB : n * v + 46 ≤ n * (95942 / 10000) := by
    have : (46 : ℝ) ≤ n * (25 / 10000) := by nlinarith
    nlinarith
  have hA0 : 0 ≤ n * s + v := by positivity
  have h1 : (n * s + v) ^ 2 ≤ (n * (70780 / 100000)) ^ 2 := pow_le_pow_left₀ hA0 hA 2
  have h2 : (n * s + v) ^ 2 * (n * v + 46) ≤ (n * (70780 / 100000)) ^ 2 * (n * (95942 / 10000)) :=
    mul_le_mul h1 hB (by positivity) (by positivity)
  have h3 : 8 * ((n * (70780 / 100000)) ^ 2 * (n * (95942 / 10000))) ≤
      n * (2025 / 10 ^ 6) * (n : ℝ) ^ 3 := by
    have e : 8 * ((n * (70780 / 100000)) ^ 2 * (n * (95942 / 10000))) =
        (8 * (70780 / 100000) ^ 2 * (95942 / 10000)) * (n : ℝ) ^ 3 := by ring
    rw [e]
    have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
    have : (8 * (70780 / 100000) ^ 2 * (95942 / 10000) : ℝ) ≤ n * (2025 / 10 ^ 6) := by
      norm_num; linarith
    exact mul_le_mul_of_nonneg_right this hn3
  linarith

/-- **The S-block core**: numeric bounds on `κ(c)`, `V(c)`, `M(c)`, on `κ̇` and `1/√(1 − ·²)` at a
bound `C1` of `c₁⁺` give the side conditions of `s3_Sblock` and `s3nks n 46 η c ≤ n·ks`, every
`n ≥ 21 000`. -/
theorem usn_part1 {n : ℕ} (hn : 19000 ≤ n) {c κh Vl Vh Mh Ml dlo C1 kd1 q1 ks : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hκ : kappa c ≤ κh) (hVl : Vl ≤ usnV c) (hVh : usnV c ≤ Vh) (hMh : usnM c ≤ Mh)
    (hMl : Ml ≤ usnM c)
    (hdlo : 0 ≤ dlo) (hd : (dlo + 1428 / 10 ^ 6) ^ 2 ≤ 2 * (1 - κh) - 1 / 10 ^ 7)
    (hC1 : (2 * (1 + 714 / 10 ^ 6) ^ 2 - dlo ^ 2) / (2 * (1 - 715 / 10 ^ 6) ^ 2) ≤ C1)
    (hC1' : C1 < 1) (hkd1 : kdot C1 ≤ kd1) (hq1 : 1 / √(1 - C1 ^ 2) ≤ q1)
    (hVl' : 606 / 100000 + 715 / 10 ^ 6 ≤ Vl)
    (hU : kd1 * max (Mh + 405 / 100000) 0 +
      ((Vh + 606 / 100000) / (1 - 715 / 10 ^ 6) + 714 / 10 ^ 6) ^ 2 * q1 / (3141592 / 1000000) +
      203 / 100000 ≤ ks)
    (hU' : -Ml / 2 ≤ ks)
    (hL : kd1 * max (405 / 100000 - Ml) 0 + 203 / 100000 ≤ ks) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ 0 ≤ s3c1 n 46 c ∧
      s3c1 n 46 c ≤ C1 ∧ √(n : ℝ) * (1 - 715 / 10 ^ 6) ≤ s3am n 46 ∧
      s3ap n 46 ≤ √(n : ℝ) * (1 + 714 / 10 ^ 6) ∧ s3e0 n 46 ≤ 714 / 10 ^ 6 * √(n : ℝ) ∧
      0 ≤ s3e0 n 46 ∧ √(n : ℝ) ≤ s3ap n 46 ∧ 0 ≤ C1 := by
  have hnR : (19000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set r := √(n : ℝ) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hn0
  have hrr : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hrr' : r * r = n := by rw [← pow_two]; exact hrr
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  set v := √(2 * (46 : ℝ)) with hv
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hv1 : v ≤ 95917 / 10000 := usn_sqrt_le (by norm_num) (by norm_num)
  have hvv : v ^ 2 = 92 := by rw [hv, Real.sq_sqrt (by norm_num)]; norm_num
  have h2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2le : √(2 : ℝ) ≤ 141422 / 100000 := usn_sqrt_le (by norm_num) (by norm_num)
  have h20 : 0 ≤ √(2 : ℝ) := Real.sqrt_nonneg _
  have hg : √(2 / (n : ℝ)) = √2 / r := by rw [Real.sqrt_div (by norm_num)]
  have hκ1 : kappa c ≤ 1 := (kappa_mem (by linarith) hc1).2
  have hκ0 : 0 ≤ kappa c := (kappa_mem (by linarith) hc1).1
  have hkdC : 0 ≤ kd1 := le_trans (kdot_nonneg _) hkd1
  have hks0 : 0 ≤ ks := by
    have : 0 ≤ kd1 * max (405 / 100000 - Ml) 0 := mul_nonneg hkdC (le_max_right _ _)
    linarith
  -- `e₀ = υ√γ ≤ 0.000647·r`
  have he0' : √(2 * (46 : ℝ)) * √(2 / (n : ℝ)) = s3e0 n 46 := by unfold s3e0; ring
  have he0 : s3e0 n 46 = v * √2 / r := by unfold s3e0; rw [hg, ← hv]; ring
  have hvr : v * √2 ≤ 714 / 10 ^ 6 * (n : ℝ) := by
    have : v * √2 ≤ 95917 / 10000 * (141422 / 100000) := mul_le_mul hv1 h2le h20 (by norm_num)
    linarith
  have he0r : s3e0 n 46 ≤ 714 / 10 ^ 6 * r := by
    rw [he0, div_le_iff₀ hr0, mul_assoc, hrr']; exact hvr
  have he00 : 0 ≤ s3e0 n 46 := by rw [he0]; positivity
  -- `a₊ ≤ r(1 + δ)`, `a₋ ≥ r(1 − δ')`
  have hap : s3ap n 46 = r + s3e0 n 46 := by unfold s3ap s3e0; ring
  have hap1 : s3ap n 46 ≤ r * (1 + 714 / 10 ^ 6) := by rw [hap]; linarith
  have hap0 : r ≤ s3ap n 46 := by rw [hap]; linarith
  have hsq : r * (1 - 1 / 10 ^ 8) ≤ √((n : ℝ) - 2 / n) := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, hrr]
    have h1 : 2 / (n : ℝ) ≤ (2 / 10 ^ 8 - 1 / 10 ^ 16) * n :=
      usn_inv_le hnR (by norm_num) (by norm_num)
    have e : (n : ℝ) * (1 - 1 / 10 ^ 8) ^ 2 = n - (2 / 10 ^ 8 - 1 / 10 ^ 16) * n := by ring
    linarith
  have ham : r * (1 - 715 / 10 ^ 6) ≤ s3am n 46 := by
    unfold s3am; rw [he0']; linarith
  have ham0 : 0 < s3am n 46 := lt_of_lt_of_le (by positivity) ham
  -- `d₋ ≥ r·dlo`
  have hX0 : (r * (dlo + 1428 / 10 ^ 6)) ^ 2 ≤ 2 * n * (1 - kappa c) - 4 * (2 / n) := by
    rw [mul_pow, hrr]
    have h8 : 8 / (n : ℝ) ≤ (1 / 10 ^ 7) * n := usn_inv_le hnR (by norm_num) (by norm_num)
    have h1 : (n : ℝ) * (dlo + 1428 / 10 ^ 6) ^ 2 ≤ n * (2 * (1 - κh) - 1 / 10 ^ 7) :=
      mul_le_mul_of_nonneg_left hd hn0.le
    have h2' : (n : ℝ) * (2 * (1 - κh)) ≤ 2 * n * (1 - kappa c) := by
      have := mul_le_mul_of_nonneg_left hκ (by positivity : (0 : ℝ) ≤ 2 * n)
      have e3 : (n : ℝ) * (2 * (1 - κh)) = 2 * n - 2 * n * κh := by ring
      have e4 : 2 * (n : ℝ) * (1 - kappa c) = 2 * n - 2 * n * kappa c := by ring
      linarith
    have e : 4 * (2 / (n : ℝ)) = 8 / n := by ring
    have e1 : (n : ℝ) * (2 * (1 - κh) - 1 / 10 ^ 7) = n * (2 * (1 - κh)) - (1 / 10 ^ 7) * n := by ring
    rw [e]; linarith
  have hdm : r * dlo ≤ s3dm n 46 c := by
    unfold s3dm
    have hs := Real.le_sqrt_of_sq_le hX0
    rw [he0']
    have : 2 * s3e0 n 46 ≤ r * (1428 / 10 ^ 6) := by linarith
    have e : r * (dlo + 1428 / 10 ^ 6) = r * dlo + r * (1428 / 10 ^ 6) := by ring
    linarith
  have hdm0 : 0 ≤ s3dm n 46 c := le_trans (by positivity) hdm
  -- `d₋² ≤ 2a₊²`
  have hXnn : 0 ≤ 2 * n * (1 - kappa c) - 4 * (2 / n) := le_trans (sq_nonneg _) hX0
  have hdm2 : s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 := by
    have hle : s3dm n 46 c ≤ √(2 * n * (1 - kappa c) - 4 * (2 / n)) := by
      unfold s3dm; rw [he0']; linarith
    have h1 : s3dm n 46 c ^ 2 ≤ 2 * n * (1 - kappa c) - 4 * (2 / n) :=
      (pow_le_pow_left₀ hdm0 hle 2).trans (le_of_eq (Real.sq_sqrt hXnn))
    have h2' : 2 * (n : ℝ) * (1 - kappa c) - 4 * (2 / n) ≤ 2 * r ^ 2 := by
      rw [hrr]
      have : 0 ≤ 4 * (2 / (n : ℝ)) := by positivity
      have : 2 * (n : ℝ) * (1 - kappa c) ≤ 2 * n := by
        have h5 := mul_le_mul_of_nonneg_left hκ0 (by positivity : (0 : ℝ) ≤ 2 * n)
        have e4 : 2 * (n : ℝ) * (1 - kappa c) = 2 * n - 2 * n * kappa c := by ring
        rw [mul_zero] at h5; linarith
      linarith
    have h3 : r ^ 2 ≤ s3ap n 46 ^ 2 := pow_le_pow_left₀ hr0.le hap0 2
    linarith
  -- `c₁⁺ ≤ C1`
  have hdlo2 : dlo ^ 2 ≤ 2 := by
    have h1 : dlo ^ 2 ≤ (dlo + 1428 / 10 ^ 6) ^ 2 := pow_le_pow_left₀ hdlo (by linarith) 2
    have : 0 ≤ κh := le_trans hκ0 hκ
    linarith
  have hC10 : 0 ≤ C1 := by
    have : 0 ≤ (2 * (1 + 714 / 10 ^ 6) ^ 2 - dlo ^ 2) := by
      have : (2 : ℝ) ≤ 2 * (1 + 714 / 10 ^ 6) ^ 2 := by norm_num
      linarith
    have := div_nonneg this (by norm_num : (0 : ℝ) ≤ 2 * (1 - 715 / 10 ^ 6) ^ 2)
    linarith
  have hc1le : s3c1 n 46 c ≤ C1 := by
    unfold s3c1
    have hden : 0 < 2 * s3am n 46 ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    have hCnum : 2 * (1 + 714 / 10 ^ 6) ^ 2 - dlo ^ 2 ≤ C1 * (2 * (1 - 715 / 10 ^ 6) ^ 2) := by
      rwa [div_le_iff₀ (by norm_num)] at hC1
    have ha2 : s3ap n 46 ^ 2 ≤ (r * (1 + 714 / 10 ^ 6)) ^ 2 := pow_le_pow_left₀ (by linarith) hap1 2
    have hd2 : (r * dlo) ^ 2 ≤ s3dm n 46 c ^ 2 := pow_le_pow_left₀ (by positivity) hdm 2
    have hm2 : (r * (1 - 715 / 10 ^ 6)) ^ 2 ≤ s3am n 46 ^ 2 :=
      pow_le_pow_left₀ (by positivity) ham 2
    have h4 : r ^ 2 * (2 * (1 + 714 / 10 ^ 6) ^ 2 - dlo ^ 2) ≤
        r ^ 2 * (C1 * (2 * (1 - 715 / 10 ^ 6) ^ 2)) :=
      mul_le_mul_of_nonneg_left hCnum (by positivity)
    have h5 : C1 * (2 * (r * (1 - 715 / 10 ^ 6)) ^ 2) ≤ C1 * (2 * s3am n 46 ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hC10
    have e1 : (r * (1 + 714 / 10 ^ 6)) ^ 2 = r ^ 2 * (1 + 714 / 10 ^ 6) ^ 2 := by ring
    have e2 : (r * dlo) ^ 2 = r ^ 2 * dlo ^ 2 := by ring
    have e3 : C1 * (2 * (r * (1 - 715 / 10 ^ 6)) ^ 2) =
        r ^ 2 * (C1 * (2 * (1 - 715 / 10 ^ 6) ^ 2)) := by ring
    have e4 : r ^ 2 * (2 * (1 + 714 / 10 ^ 6) ^ 2 - dlo ^ 2) =
        2 * (r ^ 2 * (1 + 714 / 10 ^ 6) ^ 2) - r ^ 2 * dlo ^ 2 := by ring
    linarith
  have hc10 : 0 ≤ s3c1 n 46 c := by
    unfold s3c1; exact div_nonneg (by linarith) (by positivity)
  exact ⟨ham0, hdm0, hdm2, hc10, hc1le, ham, hap1, he0r, he00, hap0, hC10⟩

theorem usn_part2 {n : ℕ} (hn : 19000 ≤ n) {c κh Vl Vh Mh Ml dlo C1 kd1 q1 ks : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hκ : kappa c ≤ κh) (hVl : Vl ≤ usnV c) (hVh : usnV c ≤ Vh) (hMh : usnM c ≤ Mh)
    (hMl : Ml ≤ usnM c)
    (hdlo : 0 ≤ dlo) (hd : (dlo + 1428 / 10 ^ 6) ^ 2 ≤ 2 * (1 - κh) - 1 / 10 ^ 7)
    (hC1 : (2 * (1 + 714 / 10 ^ 6) ^ 2 - dlo ^ 2) / (2 * (1 - 715 / 10 ^ 6) ^ 2) ≤ C1)
    (hC1' : C1 < 1) (hkd1 : kdot C1 ≤ kd1) (hq1 : 1 / √(1 - C1 ^ 2) ≤ q1)
    (hVl' : 606 / 100000 + 715 / 10 ^ 6 ≤ Vl)
    (hU : kd1 * max (Mh + 405 / 100000) 0 +
      ((Vh + 606 / 100000) / (1 - 715 / 10 ^ 6) + 714 / 10 ^ 6) ^ 2 * q1 / (3141592 / 1000000) +
      203 / 100000 ≤ ks)
    (hU' : -Ml / 2 ≤ ks)
    (hL : kd1 * max (405 / 100000 - Ml) 0 + 203 / 100000 ≤ ks) :
    0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 := by
  have hnR : (19000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨ham0, hdm0, hdm2, hc10, hc1le, ham, hap1, he0r, he00, hap0, hC10⟩ := usn_part1 hn hc0 hc1 hκ hVl hVh hMh hMl hdlo hd hC1 hC1' hkd1 hq1 hVl' hU hU' hL
  set r := √(n : ℝ) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hn0
  have hrr : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hrr' : r * r = n := by rw [← pow_two]; exact hrr
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  set v := √(2 * (46 : ℝ)) with hv
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hv1 : v ≤ 95917 / 10000 := usn_sqrt_le (by norm_num) (by norm_num)
  have hvv : v ^ 2 = 92 := by rw [hv, Real.sq_sqrt (by norm_num)]; norm_num
  have h2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2le : √(2 : ℝ) ≤ 141422 / 100000 := usn_sqrt_le (by norm_num) (by norm_num)
  have h20 : 0 ≤ √(2 : ℝ) := Real.sqrt_nonneg _
  have hg : √(2 / (n : ℝ)) = √2 / r := by rw [Real.sqrt_div (by norm_num)]
  have hκ1 : kappa c ≤ 1 := (kappa_mem (by linarith) hc1).2
  have hκ0 : 0 ≤ kappa c := (kappa_mem (by linarith) hc1).1
  have hkdC : 0 ≤ kd1 := le_trans (kdot_nonneg _) hkd1
  have hks0 : 0 ≤ ks := by
    have : 0 ≤ kd1 * max (405 / 100000 - Ml) 0 := mul_nonneg hkdC (le_max_right _ _)
    linarith
  have he0' : √(2 * (46 : ℝ)) * √(2 / (n : ℝ)) = s3e0 n 46 := by unfold s3e0; ring
  have he0 : s3e0 n 46 = v * √2 / r := by unfold s3e0; rw [hg, ← hv]; ring
  -- `nV`, `r₁`, `nM`, `r_pp`, `r_s`
  have hCpa : s3Cpa n c = n * usnV c := by unfold s3Cpa usnV; rw [hm]; field_simp
  have hCpp : s3Cpp n c = n * usnM c := by unfold s3Cpp usnM; rw [hm]; field_simp
  have hsq2 : √(2 * ((mA n : ℕ) : ℝ) * 46) = n * v := by
    rw [hm, show 2 * (n : ℝ) ^ 2 * 46 = (n : ℝ) ^ 2 * (2 * 46) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hn0.le]
  have hr1e : s3r1 n 46 = 12 * v + 552 / n := by
    unfold s3r1; rw [hsq2]; field_simp; ring
  have hr1le : s3r1 n 46 ≤ n * (606 / 100000) := by
    rw [hr1e]
    have : 552 / (n : ℝ) ≤ 3 / 100 := by rw [div_le_iff₀ hn0]; linarith
    linarith
  have hr10 : 0 ≤ s3r1 n 46 := by rw [hr1e]; positivity
  have hrpp : s3rpp n 46 = 8 * v + 368 / n := by
    unfold s3rpp; rw [hsq2]; field_simp; ring
  have hrpp0 : 0 ≤ s3rpp n 46 := by rw [hrpp]; positivity
  have hrpple : s3rpp n 46 ≤ n * (405 / 100000) := by
    rw [hrpp]
    have : 368 / (n : ℝ) ≤ 1 / 10 := by rw [div_le_iff₀ hn0]; linarith
    linarith
  have hnV : n * Vl ≤ n * usnV c := mul_le_mul_of_nonneg_left hVl hn0.le
  have hnV' : n * usnV c ≤ n * Vh := mul_le_mul_of_nonneg_left hVh hn0.le
  have hCr : 0 ≤ s3Cpa n c - s3r1 n 46 := by
    rw [hCpa]
    have : n * (606 / 100000) ≤ n * Vl := mul_le_mul_of_nonneg_left (by linarith) hn0.le
    linarith
  refine ⟨hCr, ?_⟩
  · rw [le_div_iff₀ (by linarith)]
    have h1 : s3e0 n 46 * s3ap n 46 ≤ 714 / 10 ^ 6 * r * (r * (1 + 714 / 10 ^ 6)) :=
      mul_le_mul he0r hap1 (by linarith) (by positivity)
    have e : 714 / 10 ^ 6 * r * (r * (1 + 714 / 10 ^ 6)) = n * (714 / 10 ^ 6 * (1 + 714 / 10 ^ 6)) := by
      rw [← hrr]; ring
    have h2' : n * (714 / 10 ^ 6 * (1 + 714 / 10 ^ 6)) ≤ n * (Vl - 606 / 100000) :=
      mul_le_mul_of_nonneg_left (by norm_num; linarith) hn0.le
    rw [hCpa]
    have e2 : n * (Vl - 606 / 100000) = n * Vl - n * (606 / 100000) := by ring
    linarith

theorem usn_part3U {n : ℕ} (hn : 19000 ≤ n) {c κh Vl Vh Mh Ml dlo C1 kd1 q1 ks : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hκ : kappa c ≤ κh) (hVl : Vl ≤ usnV c) (hVh : usnV c ≤ Vh) (hMh : usnM c ≤ Mh)
    (hMl : Ml ≤ usnM c)
    (hdlo : 0 ≤ dlo) (hd : (dlo + 1428 / 10 ^ 6) ^ 2 ≤ 2 * (1 - κh) - 1 / 10 ^ 7)
    (hC1 : (2 * (1 + 714 / 10 ^ 6) ^ 2 - dlo ^ 2) / (2 * (1 - 715 / 10 ^ 6) ^ 2) ≤ C1)
    (hC1' : C1 < 1) (hkd1 : kdot C1 ≤ kd1) (hq1 : 1 / √(1 - C1 ^ 2) ≤ q1)
    (hVl' : 606 / 100000 + 715 / 10 ^ 6 ≤ Vl)
    (hU : kd1 * max (Mh + 405 / 100000) 0 +
      ((Vh + 606 / 100000) / (1 - 715 / 10 ^ 6) + 714 / 10 ^ 6) ^ 2 * q1 / (3141592 / 1000000) +
      203 / 100000 ≤ ks)
    (hU' : -Ml / 2 ≤ ks)
    (hL : kd1 * max (405 / 100000 - Ml) 0 + 203 / 100000 ≤ ks) :
    |s3U n 46 usnEta c| ≤ (n : ℝ) * ks := by
  have hnR : (19000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨ham0, hdm0, hdm2, hc10, hc1le, ham, hap1, he0r, he00, hap0, hC10⟩ := usn_part1 hn hc0 hc1 hκ hVl hVh hMh hMl hdlo hd hC1 hC1' hkd1 hq1 hVl' hU hU' hL
  set r := √(n : ℝ) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hn0
  have hrr : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hrr' : r * r = n := by rw [← pow_two]; exact hrr
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  set v := √(2 * (46 : ℝ)) with hv
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hv1 : v ≤ 95917 / 10000 := usn_sqrt_le (by norm_num) (by norm_num)
  have hvv : v ^ 2 = 92 := by rw [hv, Real.sq_sqrt (by norm_num)]; norm_num
  have h2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2le : √(2 : ℝ) ≤ 141422 / 100000 := usn_sqrt_le (by norm_num) (by norm_num)
  have h20 : 0 ≤ √(2 : ℝ) := Real.sqrt_nonneg _
  have hg : √(2 / (n : ℝ)) = √2 / r := by rw [Real.sqrt_div (by norm_num)]
  have hκ1 : kappa c ≤ 1 := (kappa_mem (by linarith) hc1).2
  have hκ0 : 0 ≤ kappa c := (kappa_mem (by linarith) hc1).1
  have hkdC : 0 ≤ kd1 := le_trans (kdot_nonneg _) hkd1
  have hks0 : 0 ≤ ks := by
    have : 0 ≤ kd1 * max (405 / 100000 - Ml) 0 := mul_nonneg hkdC (le_max_right _ _)
    linarith
  have he0' : √(2 * (46 : ℝ)) * √(2 / (n : ℝ)) = s3e0 n 46 := by unfold s3e0; ring
  have he0 : s3e0 n 46 = v * √2 / r := by unfold s3e0; rw [hg, ← hv]; ring
  -- `nV`, `r₁`, `nM`, `r_pp`, `r_s`
  have hCpa : s3Cpa n c = n * usnV c := by unfold s3Cpa usnV; rw [hm]; field_simp
  have hCpp : s3Cpp n c = n * usnM c := by unfold s3Cpp usnM; rw [hm]; field_simp
  have hsq2 : √(2 * ((mA n : ℕ) : ℝ) * 46) = n * v := by
    rw [hm, show 2 * (n : ℝ) ^ 2 * 46 = (n : ℝ) ^ 2 * (2 * 46) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hn0.le]
  have hr1e : s3r1 n 46 = 12 * v + 552 / n := by
    unfold s3r1; rw [hsq2]; field_simp; ring
  have hr1le : s3r1 n 46 ≤ n * (606 / 100000) := by
    rw [hr1e]
    have : 552 / (n : ℝ) ≤ 3 / 100 := by rw [div_le_iff₀ hn0]; linarith
    linarith
  have hr10 : 0 ≤ s3r1 n 46 := by rw [hr1e]; positivity
  have hrpp : s3rpp n 46 = 8 * v + 368 / n := by
    unfold s3rpp; rw [hsq2]; field_simp; ring
  have hrpp0 : 0 ≤ s3rpp n 46 := by rw [hrpp]; positivity
  have hrpple : s3rpp n 46 ≤ n * (405 / 100000) := by
    rw [hrpp]
    have : 368 / (n : ℝ) ≤ 1 / 10 := by rw [div_le_iff₀ hn0]; linarith
    linarith
  have hnV : n * Vl ≤ n * usnV c := mul_le_mul_of_nonneg_left hVl hn0.le
  have hnV' : n * usnV c ≤ n * Vh := mul_le_mul_of_nonneg_left hVh hn0.le
  have hCr : 0 ≤ s3Cpa n c - s3r1 n 46 := by
    rw [hCpa]
    have : n * (606 / 100000) ≤ n * Vl := mul_le_mul_of_nonneg_left (by linarith) hn0.le
    linarith
  -- the main bound
  have he0sq : s3e0 n 46 ^ 2 ≤ n * (1 / 10 ^ 6) := by
    rw [he0, div_pow, mul_pow, hvv, h2, hrr]
    have := usn_inv_le (a := 92 * 2) (k := 1 / 10 ^ 6) hnR (by norm_num) (by norm_num)
    linarith
  have hrs := usn_rs_le hn
  have hrs0 : 0 ≤ s3rs n 46 usnEta := by unfold s3rs; positivity
  have hkd0 : 0 ≤ kdot (s3c1 n 46 c) := kdot_nonneg _
  have hmem1 : s3c1 n 46 c ∈ Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hmem2 : C1 ∈ Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr ⟨by linarith, hC1'.le⟩
  have hkd : kdot (s3c1 n 46 c) ≤ kd1 := (kdot_monotoneOn hmem1 hmem2 hc1le).trans hkd1
  set Lh := (Vh + 606 / 100000) / (1 - 715 / 10 ^ 6) + 714 / 10 ^ 6 with hLh
  have hLam : s3Lam n 46 c ≤ r * Lh := by
    unfold s3Lam
    have hnum : s3Cpa n c + s3r1 n 46 ≤ n * (Vh + 606 / 100000) := by rw [hCpa]; linarith
    have hnum0 : 0 ≤ s3Cpa n c + s3r1 n 46 := by rw [hCpa]; linarith
    have hden : 0 < r * (1 - 715 / 10 ^ 6) := by positivity
    have h1 : (s3Cpa n c + s3r1 n 46) / s3am n 46 ≤ n * (Vh + 606 / 100000) / (r * (1 - 715 / 10 ^ 6)) :=
      div_le_div₀ (by linarith) hnum hden ham
    have h2' : n * (Vh + 606 / 100000) / (r * (1 - 715 / 10 ^ 6)) =
        r * ((Vh + 606 / 100000) / (1 - 715 / 10 ^ 6)) := by
      rw [← hrr]; field_simp
    have e : r * Lh = r * ((Vh + 606 / 100000) / (1 - 715 / 10 ^ 6)) + 714 / 10 ^ 6 * r := by
      rw [hLh]; ring
    linarith
  have hLam0 : 0 ≤ s3Lam n 46 c := by
    unfold s3Lam
    have : 0 ≤ s3Cpa n c + s3r1 n 46 := by rw [hCpa]; linarith
    positivity
  have hC1sq : C1 ^ 2 < 1 := pow_lt_one₀ hC10 hC1' (by norm_num)
  have hcc : s3c1 n 46 c ^ 2 ≤ C1 ^ 2 := pow_le_pow_left₀ hc10 hc1le 2
  have hsqc : 0 < √(1 - s3c1 n 46 c ^ 2) := Real.sqrt_pos.2 (by linarith)
  have hq : 1 / √(1 - s3c1 n 46 c ^ 2) ≤ q1 := by
    refine le_trans ?_ hq1
    apply one_div_le_one_div_of_le (Real.sqrt_pos.2 (by linarith))
    exact Real.sqrt_le_sqrt (by linarith)
  have hq' : 1 ≤ q1 * √(1 - s3c1 n 46 c ^ 2) := by
    rw [div_le_iff₀ hsqc] at hq; linarith
  have hq0 : 0 ≤ q1 := le_trans (by positivity) hq
  have hpi := usn_pi_lo
  have hT2 : s3Lam n 46 c ^ 2 / (π * √(1 - s3c1 n 46 c ^ 2)) ≤
      n * (Lh ^ 2 * q1 / (3141592 / 1000000)) := by
    have hL2 : s3Lam n 46 c ^ 2 ≤ n * Lh ^ 2 := by
      have := pow_le_pow_left₀ hLam0 hLam 2; rw [mul_pow, hrr] at this; exact this
    rw [div_le_iff₀ (by positivity)]
    have hA : s3Lam n 46 c ^ 2 ≤ n * Lh ^ 2 * (q1 * √(1 - s3c1 n 46 c ^ 2)) :=
      hL2.trans (le_mul_of_one_le_right (by positivity) hq')
    have e : n * (Lh ^ 2 * q1 / (3141592 / 1000000)) * (π * √(1 - s3c1 n 46 c ^ 2)) =
        n * Lh ^ 2 * (q1 * √(1 - s3c1 n 46 c ^ 2)) * (π / (3141592 / 1000000)) := by
      field_simp
    rw [e]
    refine hA.trans (le_mul_of_one_le_right (by positivity) ?_)
    rw [le_div_iff₀ (by norm_num)]; linarith
  have hT20 : 0 ≤ s3Lam n 46 c ^ 2 / (π * √(1 - s3c1 n 46 c ^ 2)) := by
    have := Real.pi_pos; positivity
  have hX : s3Cpp n c + s3rpp n 46 ≤ n * (Mh + 405 / 100000) := by
    rw [hCpp]; have := mul_le_mul_of_nonneg_left hMh hn0.le; linarith
  have hXl : n * Ml ≤ s3Cpp n c + s3rpp n 46 := by
    rw [hCpp]; have := mul_le_mul_of_nonneg_left hMl hn0.le; linarith
  have hfirst : (if 0 ≤ s3Cpp n c + s3rpp n 46 then kdot (s3c1 n 46 c) * (s3Cpp n c + s3rpp n 46)
      else (s3Cpp n c + s3rpp n 46) / 2) ≤ n * (kd1 * max (Mh + 405 / 100000) 0) := by
    split_ifs with h
    · calc kdot (s3c1 n 46 c) * (s3Cpp n c + s3rpp n 46)
          ≤ kd1 * (s3Cpp n c + s3rpp n 46) := mul_le_mul_of_nonneg_right hkd h
        _ ≤ kd1 * (n * max (Mh + 405 / 100000) 0) :=
            mul_le_mul_of_nonneg_left (hX.trans (mul_le_mul_of_nonneg_left (le_max_left _ _)
              hn0.le)) hkdC
        _ = n * (kd1 * max (Mh + 405 / 100000) 0) := by ring
    · have : 0 ≤ n * (kd1 * max (Mh + 405 / 100000) 0) :=
        mul_nonneg hn0.le (mul_nonneg hkdC (le_max_right _ _))
      linarith
  have hfirst' : -(n * ks) ≤ (if 0 ≤ s3Cpp n c + s3rpp n 46 then
      kdot (s3c1 n 46 c) * (s3Cpp n c + s3rpp n 46) else (s3Cpp n c + s3rpp n 46) / 2) := by
    split_ifs with h
    · have : 0 ≤ kdot (s3c1 n 46 c) * (s3Cpp n c + s3rpp n 46) := mul_nonneg hkd0 h
      have : 0 ≤ n * ks := mul_nonneg hn0.le hks0
      linarith
    · have : n * (-Ml / 2) ≤ n * ks := mul_le_mul_of_nonneg_left hU' hn0.le
      have e : n * (-Ml / 2) = -(n * Ml) / 2 := by ring
      linarith
  have hsum : n * (kd1 * max (Mh + 405 / 100000) 0) + n * (Lh ^ 2 * q1 / (3141592 / 1000000)) +
      n * (1 / 10 ^ 6) + n * (2025 / 10 ^ 6) ≤ n * ks := by
    have := mul_le_mul_of_nonneg_left hU hn0.le
    have e : n * (kd1 * max (Mh + 405 / 100000) 0 + Lh ^ 2 * q1 / (3141592 / 1000000) +
        203 / 100000) = n * (kd1 * max (Mh + 405 / 100000) 0) +
        n * (Lh ^ 2 * q1 / (3141592 / 1000000)) + n * (203 / 100000) := by ring
    have : (n : ℝ) * (1 / 10 ^ 6) + n * (2025 / 10 ^ 6) ≤ n * (203 / 100000) := by
      have e2 : (n : ℝ) * (1 / 10 ^ 6) + n * (2025 / 10 ^ 6) = n * (2026 / 10 ^ 6) := by ring
      rw [e2]; exact mul_le_mul_of_nonneg_left (by norm_num) hn0.le
    linarith
  have hUup : s3U n 46 usnEta c ≤ n * ks := by unfold s3U; linarith
  have hUlo : -(n * ks) ≤ s3U n 46 usnEta c := by
    unfold s3U; have := sq_nonneg (s3e0 n 46); linarith
  exact abs_le.2 ⟨hUlo, hUup⟩

theorem usn_part3L {n : ℕ} (hn : 19000 ≤ n) {c κh Vl Vh Mh Ml dlo C1 kd1 q1 ks : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hκ : kappa c ≤ κh) (hVl : Vl ≤ usnV c) (hVh : usnV c ≤ Vh) (hMh : usnM c ≤ Mh)
    (hMl : Ml ≤ usnM c)
    (hdlo : 0 ≤ dlo) (hd : (dlo + 1428 / 10 ^ 6) ^ 2 ≤ 2 * (1 - κh) - 1 / 10 ^ 7)
    (hC1 : (2 * (1 + 714 / 10 ^ 6) ^ 2 - dlo ^ 2) / (2 * (1 - 715 / 10 ^ 6) ^ 2) ≤ C1)
    (hC1' : C1 < 1) (hkd1 : kdot C1 ≤ kd1) (hq1 : 1 / √(1 - C1 ^ 2) ≤ q1)
    (hVl' : 606 / 100000 + 715 / 10 ^ 6 ≤ Vl)
    (hU : kd1 * max (Mh + 405 / 100000) 0 +
      ((Vh + 606 / 100000) / (1 - 715 / 10 ^ 6) + 714 / 10 ^ 6) ^ 2 * q1 / (3141592 / 1000000) +
      203 / 100000 ≤ ks)
    (hU' : -Ml / 2 ≤ ks)
    (hL : kd1 * max (405 / 100000 - Ml) 0 + 203 / 100000 ≤ ks) :
    |s3L n 46 usnEta c| ≤ (n : ℝ) * ks := by
  have hnR : (19000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨ham0, hdm0, hdm2, hc10, hc1le, ham, hap1, he0r, he00, hap0, hC10⟩ := usn_part1 hn hc0 hc1 hκ hVl hVh hMh hMl hdlo hd hC1 hC1' hkd1 hq1 hVl' hU hU' hL
  set r := √(n : ℝ) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hn0
  have hrr : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hrr' : r * r = n := by rw [← pow_two]; exact hrr
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  set v := √(2 * (46 : ℝ)) with hv
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hv1 : v ≤ 95917 / 10000 := usn_sqrt_le (by norm_num) (by norm_num)
  have hvv : v ^ 2 = 92 := by rw [hv, Real.sq_sqrt (by norm_num)]; norm_num
  have h2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2le : √(2 : ℝ) ≤ 141422 / 100000 := usn_sqrt_le (by norm_num) (by norm_num)
  have h20 : 0 ≤ √(2 : ℝ) := Real.sqrt_nonneg _
  have hg : √(2 / (n : ℝ)) = √2 / r := by rw [Real.sqrt_div (by norm_num)]
  have hκ1 : kappa c ≤ 1 := (kappa_mem (by linarith) hc1).2
  have hκ0 : 0 ≤ kappa c := (kappa_mem (by linarith) hc1).1
  have hkdC : 0 ≤ kd1 := le_trans (kdot_nonneg _) hkd1
  have hks0 : 0 ≤ ks := by
    have : 0 ≤ kd1 * max (405 / 100000 - Ml) 0 := mul_nonneg hkdC (le_max_right _ _)
    linarith
  have he0' : √(2 * (46 : ℝ)) * √(2 / (n : ℝ)) = s3e0 n 46 := by unfold s3e0; ring
  have he0 : s3e0 n 46 = v * √2 / r := by unfold s3e0; rw [hg, ← hv]; ring
  -- `nV`, `r₁`, `nM`, `r_pp`, `r_s`
  have hCpa : s3Cpa n c = n * usnV c := by unfold s3Cpa usnV; rw [hm]; field_simp
  have hCpp : s3Cpp n c = n * usnM c := by unfold s3Cpp usnM; rw [hm]; field_simp
  have hsq2 : √(2 * ((mA n : ℕ) : ℝ) * 46) = n * v := by
    rw [hm, show 2 * (n : ℝ) ^ 2 * 46 = (n : ℝ) ^ 2 * (2 * 46) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hn0.le]
  have hr1e : s3r1 n 46 = 12 * v + 552 / n := by
    unfold s3r1; rw [hsq2]; field_simp; ring
  have hr1le : s3r1 n 46 ≤ n * (606 / 100000) := by
    rw [hr1e]
    have : 552 / (n : ℝ) ≤ 3 / 100 := by rw [div_le_iff₀ hn0]; linarith
    linarith
  have hr10 : 0 ≤ s3r1 n 46 := by rw [hr1e]; positivity
  have hrpp : s3rpp n 46 = 8 * v + 368 / n := by
    unfold s3rpp; rw [hsq2]; field_simp; ring
  have hrpp0 : 0 ≤ s3rpp n 46 := by rw [hrpp]; positivity
  have hrpple : s3rpp n 46 ≤ n * (405 / 100000) := by
    rw [hrpp]
    have : 368 / (n : ℝ) ≤ 1 / 10 := by rw [div_le_iff₀ hn0]; linarith
    linarith
  have hnV : n * Vl ≤ n * usnV c := mul_le_mul_of_nonneg_left hVl hn0.le
  have hnV' : n * usnV c ≤ n * Vh := mul_le_mul_of_nonneg_left hVh hn0.le
  have hCr : 0 ≤ s3Cpa n c - s3r1 n 46 := by
    rw [hCpa]
    have : n * (606 / 100000) ≤ n * Vl := mul_le_mul_of_nonneg_left (by linarith) hn0.le
    linarith
  -- the main bound
  have he0sq : s3e0 n 46 ^ 2 ≤ n * (1 / 10 ^ 6) := by
    rw [he0, div_pow, mul_pow, hvv, h2, hrr]
    have := usn_inv_le (a := 92 * 2) (k := 1 / 10 ^ 6) hnR (by norm_num) (by norm_num)
    linarith
  have hrs := usn_rs_le hn
  have hrs0 : 0 ≤ s3rs n 46 usnEta := by unfold s3rs; positivity
  have hkd0 : 0 ≤ kdot (s3c1 n 46 c) := kdot_nonneg _
  have hmem1 : s3c1 n 46 c ∈ Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hmem2 : C1 ∈ Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr ⟨by linarith, hC1'.le⟩
  have hkd : kdot (s3c1 n 46 c) ≤ kd1 := (kdot_monotoneOn hmem1 hmem2 hc1le).trans hkd1
  have hmin : -(n * max (405 / 100000 - Ml) 0) ≤ min (s3Cpp n c - s3rpp n 46) 0 := by
    apply le_min
    · have h1 : (n : ℝ) * (405 / 100000 - Ml) ≤ n * max (405 / 100000 - Ml) 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hn0.le
      have e : (n : ℝ) * (405 / 100000 - Ml) = n * (405 / 100000) - n * Ml := by ring
      have h3 := mul_le_mul_of_nonneg_left hMl hn0.le
      rw [hCpp]
      linarith
    · have : 0 ≤ n * max (405 / 100000 - Ml) 0 := mul_nonneg hn0.le (le_max_right _ _)
      linarith
  have hm0 : min (s3Cpp n c - s3rpp n 46) 0 ≤ 0 := min_le_right _ _
  have hLprod : kd1 * (-(n * max (405 / 100000 - Ml) 0)) ≤
      kdot (s3c1 n 46 c) * min (s3Cpp n c - s3rpp n 46) 0 := by
    have h1 : kd1 * min (s3Cpp n c - s3rpp n 46) 0 ≤
        kdot (s3c1 n 46 c) * min (s3Cpp n c - s3rpp n 46) 0 :=
      mul_le_mul_of_nonpos_right hkd hm0
    have h2' : kd1 * (-(n * max (405 / 100000 - Ml) 0)) ≤ kd1 * min (s3Cpp n c - s3rpp n 46) 0 :=
      mul_le_mul_of_nonneg_left hmin hkdC
    linarith
  have hLlo : -(n * ks) ≤ s3L n 46 usnEta c := by
    unfold s3L
    have := mul_le_mul_of_nonneg_left hL hn0.le
    have e : n * (kd1 * max (405 / 100000 - Ml) 0 + 203 / 100000) =
        -(kd1 * (-(n * max (405 / 100000 - Ml) 0))) + n * (203 / 100000) := by ring
    have : (n : ℝ) * (1 / 10 ^ 6) + n * (2025 / 10 ^ 6) ≤ n * (203 / 100000) := by
      have e2 : (n : ℝ) * (1 / 10 ^ 6) + n * (2025 / 10 ^ 6) = n * (2026 / 10 ^ 6) := by ring
      rw [e2]; exact mul_le_mul_of_nonneg_left (by norm_num) hn0.le
    linarith
  have hLup : s3L n 46 usnEta c ≤ n * ks := by
    unfold s3L
    have : kdot (s3c1 n 46 c) * min (s3Cpp n c - s3rpp n 46) 0 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hkd0 hm0
    have : 0 ≤ n * ks := mul_nonneg hn0.le hks0
    have := sq_nonneg (s3e0 n 46)
    linarith
  exact abs_le.2 ⟨hLlo, hLup⟩

theorem usn_part3 {n : ℕ} (hn : 19000 ≤ n) {c κh Vl Vh Mh Ml dlo C1 kd1 q1 ks : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hκ : kappa c ≤ κh) (hVl : Vl ≤ usnV c) (hVh : usnV c ≤ Vh) (hMh : usnM c ≤ Mh)
    (hMl : Ml ≤ usnM c)
    (hdlo : 0 ≤ dlo) (hd : (dlo + 1428 / 10 ^ 6) ^ 2 ≤ 2 * (1 - κh) - 1 / 10 ^ 7)
    (hC1 : (2 * (1 + 714 / 10 ^ 6) ^ 2 - dlo ^ 2) / (2 * (1 - 715 / 10 ^ 6) ^ 2) ≤ C1)
    (hC1' : C1 < 1) (hkd1 : kdot C1 ≤ kd1) (hq1 : 1 / √(1 - C1 ^ 2) ≤ q1)
    (hVl' : 606 / 100000 + 715 / 10 ^ 6 ≤ Vl)
    (hU : kd1 * max (Mh + 405 / 100000) 0 +
      ((Vh + 606 / 100000) / (1 - 715 / 10 ^ 6) + 714 / 10 ^ 6) ^ 2 * q1 / (3141592 / 1000000) +
      203 / 100000 ≤ ks)
    (hU' : -Ml / 2 ≤ ks)
    (hL : kd1 * max (405 / 100000 - Ml) 0 + 203 / 100000 ≤ ks) :
    s3nks n 46 usnEta c ≤ (n : ℝ) * ks := by
  unfold s3nks
  exact max_le (usn_part3U hn hc0 hc1 hκ hVl hVh hMh hMl hdlo hd hC1 hC1' hkd1 hq1 hVl' hU hU' hL) (usn_part3L hn hc0 hc1 hκ hVl hVh hMh hMl hdlo hd hC1 hC1' hkd1 hq1 hVl' hU hU' hL)

theorem usn_core {n : ℕ} (hn : 19000 ≤ n) {c κh Vl Vh Mh Ml dlo C1 kd1 q1 ks : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hκ : kappa c ≤ κh) (hVl : Vl ≤ usnV c) (hVh : usnV c ≤ Vh) (hMh : usnM c ≤ Mh)
    (hMl : Ml ≤ usnM c)
    (hdlo : 0 ≤ dlo) (hd : (dlo + 1428 / 10 ^ 6) ^ 2 ≤ 2 * (1 - κh) - 1 / 10 ^ 7)
    (hC1 : (2 * (1 + 714 / 10 ^ 6) ^ 2 - dlo ^ 2) / (2 * (1 - 715 / 10 ^ 6) ^ 2) ≤ C1)
    (hC1' : C1 < 1) (hkd1 : kdot C1 ≤ kd1) (hq1 : 1 / √(1 - C1 ^ 2) ≤ q1)
    (hVl' : 606 / 100000 + 715 / 10 ^ 6 ≤ Vl)
    (hU : kd1 * max (Mh + 405 / 100000) 0 +
      ((Vh + 606 / 100000) / (1 - 715 / 10 ^ 6) + 714 / 10 ^ 6) ^ 2 * q1 / (3141592 / 1000000) +
      203 / 100000 ≤ ks)
    (hU' : -Ml / 2 ≤ ks)
    (hL : kd1 * max (405 / 100000 - Ml) 0 + 203 / 100000 ≤ ks) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 usnEta c ≤ (n : ℝ) * ks := by
  obtain ⟨ham0, hdm0, hdm2, hc10, hc1le, -⟩ := usn_part1 hn hc0 hc1 hκ hVl hVh hMh hMl hdlo hd hC1 hC1' hkd1 hq1 hVl' hU hU' hL
  obtain ⟨hCr, hpos⟩ := usn_part2 hn hc0 hc1 hκ hVl hVh hMh hMl hdlo hd hC1 hC1' hkd1 hq1 hVl' hU hU' hL
  exact ⟨ham0, hdm0, hdm2, lt_of_le_of_lt hc1le hC1', hCr, hpos, usn_part3 hn hc0 hc1 hκ hVl hVh hMh hMl hdlo hd hC1 hC1' hkd1 hq1 hVl' hU hU' hL⟩


/-! ## Cells in `c` -/

/-- `t + t³/6 + 3t⁵/40 + t⁷/10`. -/
noncomputable def usnP7 (t : ℝ) : ℝ := t + t ^ 3 / 6 + 3 * t ^ 5 / 40 + t ^ 7 / 10
/-- `t + t³/6 + 3t⁵/40`. -/
noncomputable def usnP5 (t : ℝ) : ℝ := t + t ^ 3 / 6 + 3 * t ^ 5 / 40
/-- Upper bound of `κ̇` on `[0, 3/4]`. -/
noncomputable def usnKU (t : ℝ) : ℝ := 1 / 2 + usnP7 t / (3141592 / 1000000)
/-- Lower bound of `κ̇` on `[0, 3/4]`. -/
noncomputable def usnKL (t : ℝ) : ℝ := 1 / 2 + usnP5 t / (3141593 / 1000000)

lemma usn_kU {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 3 / 4) : kdot t ≤ usnKU t := usn_kdot_le h0 h1
lemma usn_kL {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 3 / 4) : usnKL t ≤ kdot t := usn_kdot_ge h0 h1

lemma usn_sqrt_ge {a b : ℝ} (hb : 0 ≤ b) (h : b ^ 2 ≤ a) : b ≤ √a :=
  Real.le_sqrt_of_sq_le h

/-- **One cell `[cl, ch]` of the S block.** -/
theorem usn_cell {n : ℕ} (hn : 19000 ≤ n) {c cl ch Su Sd Sc dlo C1 q1 ks : ℝ}
    (hcl0 : 0 ≤ cl) (hcl : cl ≤ c) (hch : c ≤ ch) (hch1 : ch ≤ 3 / 4)
    (hSu0 : 0 ≤ Su) (hSu : 1 - cl ^ 2 ≤ Su ^ 2) (hSd0 : 0 ≤ Sd) (hSd : Sd ^ 2 ≤ 1 - ch ^ 2)
    (hSc0 : 0 ≤ Sc) (hSc : 1 - ch ^ 2 ≤ Sc ^ 2)
    (hdlo : 0 ≤ dlo)
    (hd : (dlo + 1428 / 10 ^ 6) ^ 2 ≤
      2 * (1 - (Sc + ch * (3141593 / 2000000 + usnP7 ch)) / (3141592 / 1000000)) - 1 / 10 ^ 7)
    (hC1 : (2 * (1 + 714 / 10 ^ 6) ^ 2 - dlo ^ 2) / (2 * (1 - 715 / 10 ^ 6) ^ 2) ≤ C1)
    (hC10 : 0 ≤ C1) (hC1' : C1 ≤ 3 / 4) (hq10 : 0 ≤ q1) (hq1 : 1 ≤ q1 ^ 2 * (1 - C1 ^ 2))
    (hVl' : 606 / 100000 + 715 / 10 ^ 6 ≤ Sd * usnKL cl)
    (hU : usnKU C1 * max (Su / (3141592 / 1000000) - cl * usnKL cl + 405 / 100000) 0 +
      ((Su * usnKU ch + 606 / 100000) / (1 - 715 / 10 ^ 6) + 714 / 10 ^ 6) ^ 2 * q1 /
        (3141592 / 1000000) + 203 / 100000 ≤ ks)
    (hU' : -(Sd / (3141593 / 1000000) - ch * usnKU ch) / 2 ≤ ks)
    (hL : usnKU C1 * max (405 / 100000 - (Sd / (3141593 / 1000000) - ch * usnKU ch)) 0 +
      203 / 100000 ≤ ks) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 usnEta c ≤ (n : ℝ) * ks := by
  have hc0 : 0 ≤ c := hcl0.trans hcl
  have hc1 : c ≤ 3 / 4 := hch.trans hch1
  have hcl1 : cl ≤ 3 / 4 := hcl.trans hc1
  have hch0 : 0 ≤ ch := hc0.trans hch
  have hpl := usn_pi_lo
  have hph := usn_pi_hi
  have hpi := Real.pi_pos
  -- square roots
  have hsc : √(1 - c ^ 2) ≤ Su := by
    refine (Real.sqrt_le_sqrt (by nlinarith)).trans (usn_sqrt_le hSu0 hSu)
  have hsc' : Sd ≤ √(1 - c ^ 2) := by
    refine (usn_sqrt_ge hSd0 hSd).trans (Real.sqrt_le_sqrt (by nlinarith))
  have hsch : √(1 - ch ^ 2) ≤ Sc := usn_sqrt_le hSc0 hSc
  have hs0 : 0 ≤ √(1 - c ^ 2) := Real.sqrt_nonneg _
  -- κ̇ bounds
  have hmc : c ∈ Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hmch : ch ∈ Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hmcl : cl ∈ Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hk1 : kdot c ≤ usnKU ch := (kdot_monotoneOn hmc hmch hch).trans (usn_kU hch0 hch1)
  have hk2 : usnKL cl ≤ kdot c := (usn_kL hcl0 hcl1).trans (kdot_monotoneOn hmcl hmc hcl)
  have hkl0 : 0 ≤ usnKL cl := by unfold usnKL usnP5; positivity
  have hkc0 : 0 ≤ kdot c := kdot_nonneg c
  -- κ
  have hκ : kappa c ≤ (Sc + ch * (3141593 / 2000000 + usnP7 ch)) / (3141592 / 1000000) :=
    (kappa_monotoneOn hmc hmch hch).trans (usn_kappa_le hch0 hch1 hsch)
  -- V and M
  have hVh : usnV c ≤ Su * usnKU ch := mul_le_mul hsc hk1 hkc0 hSu0
  have hVl : Sd * usnKL cl ≤ usnV c := mul_le_mul hsc' hk2 hkl0 hs0
  have hMh : usnM c ≤ Su / (3141592 / 1000000) - cl * usnKL cl := by
    unfold usnM
    have h1 : √(1 - c ^ 2) / π ≤ Su / (3141592 / 1000000) :=
      (div_le_div_of_nonneg_left hs0 (by norm_num) hpl.le).trans
        (div_le_div_of_nonneg_right hsc (by norm_num))
    have h2 : cl * usnKL cl ≤ c * kdot c := mul_le_mul hcl hk2 hkl0 hc0
    linarith
  have hMl : Sd / (3141593 / 1000000) - ch * usnKU ch ≤ usnM c := by
    unfold usnM
    have h1 : Sd / (3141593 / 1000000) ≤ √(1 - c ^ 2) / π :=
      (div_le_div_of_nonneg_right hsc' (by norm_num)).trans
        (div_le_div_of_nonneg_left hs0 hpi hph.le)
    have h2 : c * kdot c ≤ ch * usnKU ch := mul_le_mul hch hk1 hkc0 hch0
    linarith
  -- `c₁⁺`-side bounds
  have hkd1 : kdot C1 ≤ usnKU C1 := usn_kU hC10 hC1'
  have hq : 1 / √(1 - C1 ^ 2) ≤ q1 := by
    have hpos : 0 < 1 - C1 ^ 2 := by nlinarith
    have hs : 0 < √(1 - C1 ^ 2) := Real.sqrt_pos.2 hpos
    rw [div_le_iff₀ hs]
    have : 1 ≤ √(q1 ^ 2 * (1 - C1 ^ 2)) := by
      have := Real.sqrt_le_sqrt hq1
      rwa [Real.sqrt_one] at this
    rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hq10] at this
  exact usn_core hn hc0 (by linarith) hκ hVl hVh hMh hMl hdlo hd hC1 (by linarith) hkd1 hq
    (hVl'.trans le_rfl) hU hU' hL


lemma usn_cell_0 {n : ℕ} (hn : 19000 ≤ n) {c : ℝ} (h0 : (187 / 500 : ℝ) ≤ c) (h1 : c ≤ (397 / 1000 : ℝ)) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 usnEta c ≤ (n : ℝ) * (182 / 1000) :=
  usn_cell hn (cl := (187 / 500 : ℝ)) (ch := (397 / 1000 : ℝ)) (Su := (927429 / 1000000 : ℝ)) (Sd := (458909 / 500000 : ℝ))
    (Sc := (917819 / 1000000 : ℝ)) (dlo := (238847 / 250000 : ℝ)) (C1 := (272913 / 500000 : ℝ)) (q1 := (1193463 / 1000000 : ℝ))
    (by norm_num) h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [usnP7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [usnKL, usnP5])
    (by norm_num [usnKU, usnKL, usnP7, usnP5, max_def])
    (by norm_num [usnKU, usnP7])
    (by norm_num [usnKU, usnP7, max_def])

lemma usn_cell_1 {n : ℕ} (hn : 19000 ≤ n) {c : ℝ} (h0 : (397 / 1000 : ℝ) ≤ c) (h1 : c ≤ (21 / 50 : ℝ)) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 usnEta c ≤ (n : ℝ) * (182 / 1000) :=
  usn_cell hn (cl := (397 / 1000 : ℝ)) (ch := (21 / 50 : ℝ)) (Su := (917819 / 1000000 : ℝ)) (Sd := (226881 / 250000 : ℝ))
    (Sc := (36301 / 40000 : ℝ)) (dlo := (940019 / 1000000 : ℝ)) (C1 := (140103 / 250000 : ℝ)) (q1 := (1207419 / 1000000 : ℝ))
    (by norm_num) h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [usnP7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [usnKL, usnP5])
    (by norm_num [usnKU, usnKL, usnP7, usnP5, max_def])
    (by norm_num [usnKU, usnP7])
    (by norm_num [usnKU, usnP7, max_def])

lemma usn_cell_2 {n : ℕ} (hn : 19000 ≤ n) {c : ℝ} (h0 : (21 / 50 : ℝ) ≤ c) (h1 : c ≤ (443 / 1000 : ℝ)) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 usnEta c ≤ (n : ℝ) * (182 / 1000) :=
  usn_cell hn (cl := (21 / 50 : ℝ)) (ch := (443 / 1000 : ℝ)) (Su := (36301 / 40000 : ℝ)) (Sd := (896521 / 1000000 : ℝ))
    (Sc := (448261 / 500000 : ℝ)) (dlo := (462097 / 500000 : ℝ)) (C1 := (35949 / 62500 : ℝ)) (q1 := (1222459 / 1000000 : ℝ))
    (by norm_num) h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [usnP7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [usnKL, usnP5])
    (by norm_num [usnKU, usnKL, usnP7, usnP5, max_def])
    (by norm_num [usnKU, usnP7])
    (by norm_num [usnKU, usnP7, max_def])

lemma usn_cell_3 {n : ℕ} (hn : 19000 ≤ n) {c : ℝ} (h0 : (443 / 1000 : ℝ) ≤ c) (h1 : c ≤ (233 / 500 : ℝ)) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 usnEta c ≤ (n : ℝ) * (182 / 1000) :=
  usn_cell hn (cl := (443 / 1000 : ℝ)) (ch := (233 / 500 : ℝ)) (Su := (448261 / 500000 : ℝ)) (Sd := (55299 / 62500 : ℝ))
    (Sc := (176957 / 200000 : ℝ)) (dlo := (453941 / 500000 : ℝ)) (C1 := (147537 / 250000 : ℝ)) (q1 := (619353 / 500000 : ℝ))
    (by norm_num) h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [usnP7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [usnKL, usnP5])
    (by norm_num [usnKU, usnKL, usnP7, usnP5, max_def])
    (by norm_num [usnKU, usnP7])
    (by norm_num [usnKU, usnP7, max_def])

lemma usn_cell_4 {n : ℕ} (hn : 19000 ≤ n) {c : ℝ} (h0 : (233 / 500 : ℝ) ≤ c) (h1 : c ≤ (489 / 1000 : ℝ)) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 usnEta c ≤ (n : ℝ) * (182 / 1000) :=
  usn_cell hn (cl := (233 / 500 : ℝ)) (ch := (489 / 1000 : ℝ)) (Su := (176957 / 200000 : ℝ)) (Sd := (872283 / 1000000 : ℝ))
    (Sc := (218071 / 250000 : ℝ)) (dlo := (178211 / 200000 : ℝ)) (C1 := (121061 / 200000 : ℝ)) (q1 := (1256293 / 1000000 : ℝ))
    (by norm_num) h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [usnP7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [usnKL, usnP5])
    (by norm_num [usnKU, usnKL, usnP7, usnP5, max_def])
    (by norm_num [usnKU, usnP7])
    (by norm_num [usnKU, usnP7, max_def])

lemma usn_cell_5 {n : ℕ} (hn : 19000 ≤ n) {c : ℝ} (h0 : (489 / 1000 : ℝ) ≤ c) (h1 : c ≤ (64 / 125 : ℝ)) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 usnEta c ≤ (n : ℝ) * (182 / 1000) :=
  usn_cell hn (cl := (489 / 1000 : ℝ)) (ch := (64 / 125 : ℝ)) (Su := (218071 / 250000 : ℝ)) (Sd := (171797 / 200000 : ℝ))
    (Sc := (429493 / 500000 : ℝ)) (dlo := (436839 / 500000 : ℝ)) (C1 := (31033 / 50000 : ℝ)) (q1 := (637691 / 500000 : ℝ))
    (by norm_num) h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [usnP7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [usnKL, usnP5])
    (by norm_num [usnKU, usnKL, usnP7, usnP5, max_def])
    (by norm_num [usnKU, usnP7])
    (by norm_num [usnKU, usnP7, max_def])

lemma usn_cell_6 {n : ℕ} (hn : 19000 ≤ n) {c : ℝ} (h0 : (64 / 125 : ℝ) ≤ c) (h1 : c ≤ (107 / 200 : ℝ)) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 usnEta c ≤ (n : ℝ) * (182 / 1000) :=
  usn_cell hn (cl := (64 / 125 : ℝ)) (ch := (107 / 200 : ℝ)) (Su := (429493 / 500000 : ℝ)) (Sd := (211213 / 250000 : ℝ))
    (Sc := (844853 / 1000000 : ℝ)) (dlo := (855713 / 1000000 : ℝ)) (C1 := (79527 / 125000 : ℝ)) (q1 := (1296159 / 1000000 : ℝ))
    (by norm_num) h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [usnP7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [usnKL, usnP5])
    (by norm_num [usnKU, usnKL, usnP7, usnP5, max_def])
    (by norm_num [usnKU, usnP7])
    (by norm_num [usnKU, usnP7, max_def])

lemma usn_cell_7 {n : ℕ} (hn : 19000 ≤ n) {c : ℝ} (h0 : (107 / 200 : ℝ) ≤ c) (h1 : c ≤ (279 / 500 : ℝ)) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 usnEta c ≤ (n : ℝ) * (182 / 1000) :=
  usn_cell hn (cl := (107 / 200 : ℝ)) (ch := (279 / 500 : ℝ)) (Su := (844853 / 1000000 : ℝ)) (Sd := (10373 / 12500 : ℝ))
    (Sc := (829841 / 1000000 : ℝ)) (dlo := (837117 / 1000000 : ℝ)) (C1 := (651979 / 1000000 : ℝ)) (q1 := (26377 / 20000 : ℝ))
    (by norm_num) h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [usnP7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [usnKL, usnP5])
    (by norm_num [usnKU, usnKL, usnP7, usnP5, max_def])
    (by norm_num [usnKU, usnP7])
    (by norm_num [usnKU, usnP7, max_def])

lemma usn_cell_8 {n : ℕ} (hn : 19000 ≤ n) {c : ℝ} (h0 : (279 / 500 : ℝ) ≤ c) (h1 : c ≤ (581 / 1000 : ℝ)) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 usnEta c ≤ (n : ℝ) * (182 / 1000) :=
  usn_cell hn (cl := (279 / 500 : ℝ)) (ch := (581 / 1000 : ℝ)) (Su := (829841 / 1000000 : ℝ)) (Sd := (813903 / 1000000 : ℝ))
    (Sc := (50869 / 62500 : ℝ)) (dlo := (817839 / 1000000 : ℝ)) (C1 := (333977 / 500000 : ℝ)) (q1 := (671861 / 500000 : ℝ))
    (by norm_num) h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [usnP7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [usnKL, usnP5])
    (by norm_num [usnKU, usnKL, usnP7, usnP5, max_def])
    (by norm_num [usnKU, usnP7])
    (by norm_num [usnKU, usnP7, max_def])

lemma usn_cell_9 {n : ℕ} (hn : 19000 ≤ n) {c : ℝ} (h0 : (581 / 1000 : ℝ) ≤ c) (h1 : c ≤ (151 / 250 : ℝ)) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 usnEta c ≤ (n : ℝ) * (182 / 1000) :=
  usn_cell hn (cl := (581 / 1000 : ℝ)) (ch := (151 / 250 : ℝ)) (Su := (50869 / 62500 : ℝ)) (Sd := (99623 / 125000 : ℝ))
    (Sc := (159397 / 200000 : ℝ)) (dlo := (12466 / 15625 : ℝ)) (C1 := (136829 / 200000 : ℝ)) (q1 := (1371093 / 1000000 : ℝ))
    (by norm_num) h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [usnP7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [usnKL, usnP5])
    (by norm_num [usnKU, usnKL, usnP7, usnP5, max_def])
    (by norm_num [usnKU, usnP7])
    (by norm_num [usnKU, usnP7, max_def])

lemma usn_cell_10 {n : ℕ} (hn : 19000 ≤ n) {c : ℝ} (h0 : (151 / 250 : ℝ) ≤ c) (h1 : c ≤ (627 / 1000 : ℝ)) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 usnEta c ≤ (n : ℝ) * (182 / 1000) :=
  usn_cell hn (cl := (151 / 250 : ℝ)) (ch := (627 / 1000 : ℝ)) (Su := (159397 / 200000 : ℝ)) (Sd := (779019 / 1000000 : ℝ))
    (Sc := (38951 / 50000 : ℝ)) (dlo := (777009 / 1000000 : ℝ)) (C1 := (700559 / 1000000 : ℝ)) (q1 := (700679 / 500000 : ℝ))
    (by norm_num) h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [usnP7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [usnKL, usnP5])
    (by norm_num [usnKU, usnKL, usnP7, usnP5, max_def])
    (by norm_num [usnKU, usnP7])
    (by norm_num [usnKU, usnP7, max_def])

lemma usn_cell_11 {n : ℕ} (hn : 19000 ≤ n) {c : ℝ} (h0 : (627 / 1000 : ℝ) ≤ c) (h1 : c ≤ (13 / 20 : ℝ)) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 usnEta c ≤ (n : ℝ) * (182 / 1000) :=
  usn_cell hn (cl := (627 / 1000 : ℝ)) (ch := (13 / 20 : ℝ)) (Su := (38951 / 50000 : ℝ)) (Sd := (379967 / 500000 : ℝ))
    (Sc := (151987 / 200000 : ℝ)) (dlo := (755319 / 1000000 : ℝ)) (C1 := (717201 / 1000000 : ℝ)) (q1 := (1434997 / 1000000 : ℝ))
    (by norm_num) h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [usnP7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [usnKL, usnP5])
    (by norm_num [usnKU, usnKL, usnP7, usnP5, max_def])
    (by norm_num [usnKU, usnP7])
    (by norm_num [usnKU, usnP7, max_def])


/-- **The S block, numerics**: for every `n ≥ 19 000` and `0.374 ≤ c ≤ 0.65`, the side conditions
of `s3_Sblock` hold and `s3nks n 46 (253/10⁶) c ≤ 0.182·n` (twelve cells). -/
theorem usn_S {n : ℕ} (hn : 19000 ≤ n) {c : ℝ} (h0 : (374 / 1000 : ℝ) ≤ c) (h1 : c ≤ 650 / 1000) :
    0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
      0 ≤ s3Cpa n c - s3r1 n 46 ∧ s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
      s3nks n 46 usnEta c ≤ (n : ℝ) * (182 / 1000) := by
  replace h0 : (187 / 500 : ℝ) ≤ c := by linarith
  replace h1 : c ≤ (13 / 20 : ℝ) := by linarith
  by_cases hc0 : c ≤ (397 / 1000 : ℝ)
  · exact (usn_cell_0 hn h0 hc0).2
  have hl1 : (397 / 1000 : ℝ) ≤ c := (not_le.mp hc0).le
  by_cases hc1 : c ≤ (21 / 50 : ℝ)
  · exact (usn_cell_1 hn hl1 hc1).2
  have hl2 : (21 / 50 : ℝ) ≤ c := (not_le.mp hc1).le
  by_cases hc2 : c ≤ (443 / 1000 : ℝ)
  · exact (usn_cell_2 hn hl2 hc2).2
  have hl3 : (443 / 1000 : ℝ) ≤ c := (not_le.mp hc2).le
  by_cases hc3 : c ≤ (233 / 500 : ℝ)
  · exact (usn_cell_3 hn hl3 hc3).2
  have hl4 : (233 / 500 : ℝ) ≤ c := (not_le.mp hc3).le
  by_cases hc4 : c ≤ (489 / 1000 : ℝ)
  · exact (usn_cell_4 hn hl4 hc4).2
  have hl5 : (489 / 1000 : ℝ) ≤ c := (not_le.mp hc4).le
  by_cases hc5 : c ≤ (64 / 125 : ℝ)
  · exact (usn_cell_5 hn hl5 hc5).2
  have hl6 : (64 / 125 : ℝ) ≤ c := (not_le.mp hc5).le
  by_cases hc6 : c ≤ (107 / 200 : ℝ)
  · exact (usn_cell_6 hn hl6 hc6).2
  have hl7 : (107 / 200 : ℝ) ≤ c := (not_le.mp hc6).le
  by_cases hc7 : c ≤ (279 / 500 : ℝ)
  · exact (usn_cell_7 hn hl7 hc7).2
  have hl8 : (279 / 500 : ℝ) ≤ c := (not_le.mp hc7).le
  by_cases hc8 : c ≤ (581 / 1000 : ℝ)
  · exact (usn_cell_8 hn hl8 hc8).2
  have hl9 : (581 / 1000 : ℝ) ≤ c := (not_le.mp hc8).le
  by_cases hc9 : c ≤ (151 / 250 : ℝ)
  · exact (usn_cell_9 hn hl9 hc9).2
  have hl10 : (151 / 250 : ℝ) ≤ c := (not_le.mp hc9).le
  by_cases hc10 : c ≤ (627 / 1000 : ℝ)
  · exact (usn_cell_10 hn hl10 hc10).2
  have hl11 : (627 / 1000 : ℝ) ≤ c := (not_le.mp hc10).le
  exact (usn_cell_11 hn hl11 h1).2

/-- `0 < a₋` at `τ = 46`, every `n ≥ 19 000`. -/
theorem usn_am {n : ℕ} (hn : 19000 ≤ n) : 0 < s3am n 46 :=
  (usn_cell_0 hn (c := 187 / 500) (by norm_num) (by norm_num)).1

lemma usnEta_eq : usnEta = 253 / 1000000 := rfl

/-- **All numeric hypotheses of `ta_num`** at `cm = 0.374`, `cp = 0.65`, `kE = 0.725`, `ko = 0.027`,
`ks = 0.182`, `η = 253/10⁶`, `τ = 46`, every `n ≥ 19 000`. -/
theorem usn_ta_num {n : ℕ} (hn : 19000 ≤ n) :
    ta_num n (374 / 1000) (650 / 1000) (725 / 1000) (27 / 1000) (182 / 1000) (253 / 1000000) 46 := by
  refine ⟨?_, usn_am hn, fun c h0 h1 => ?_⟩
  · have h := usn_ko hn; rwa [usnEta_eq] at h
  · obtain ⟨hdm, h6, hc1, hr1, hpos, hks⟩ := usn_S hn h0 h1
    rw [usnEta_eq] at hks
    exact ⟨hdm, h6, hc1, hr1, hpos, uen_kE hn (by linarith) h1, hks⟩

/-- `ta_lam 0.725 0.027 0.182 ≤ 0.73` (`≈ 0.7264`). -/
theorem usn_lam : ta_lam (725 / 1000) (27 / 1000) (182 / 1000) ≤ 73 / 100 := by
  unfold ta_lam
  have h : √(((725 / 1000 - 182 / 1000 : ℝ) / 2) ^ 2 + (27 / 1000) ^ 2) ≤ 2729 / 10000 :=
    usn_sqrt_le (by norm_num) (by norm_num)
  linarith

/-- **Lemma TI (TI-lite) at `n ≥ 19 000`**:
`TI_hyp n 0.374 0.65 (ta_lam 0.725 0.027 0.182) 10⁻¹⁸`. -/
theorem usn_TI {n : ℕ} (hn : 19000 ≤ n) :
    TI_hyp n (374 / 1000) (650 / 1000) (ta_lam (725 / 1000) (27 / 1000) (182 / 1000)) (1 / 10 ^ 18) :=
  ta_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (uen_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (usn_ta_num hn)

end BstLean.Part183.U

open BstLean.Part183.U in
#print axioms usn_ko
open BstLean.Part183.U in
#print axioms usn_S
open BstLean.Part183.U in
#print axioms usn_am
open BstLean.Part183.U in
#print axioms usn_eta_ok
open BstLean.Part183.U in
#print axioms usn_ta_num
open BstLean.Part183.U in
#print axioms usn_lam
open BstLean.Part183.U in
#print axioms usn_TI
