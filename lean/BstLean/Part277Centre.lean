import BstLean.Part277Caps
import BstLean.Part264EnergyLower

/-! Part 277, centre: the finite-centre cap and the `g±` guards on a base dimension `n0 ≥ 8000`.
Rational witnesses carry rational hypotheses. `r` is a lower bound of `√n0`; `t` is an upper
bound of `√12`. The old lemmas at 12225 are instances with the old witnesses. -/
namespace BstLean.Part277
open Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem wn_upperP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {r w : ℝ} (hr0 : 0 < r)
    (hr : r ^ 2 ≤ n0) (hw : (1 + 2 / r) ^ 2 ≤ w) : wn n ≤ w := by
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hrs : r ≤ √(n : ℝ) := le_sqrt_of_sq_le (hr.trans hnn)
  unfold wn
  refine le_trans ?_ hw
  gcongr

theorem deltaChi_upperP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {d : ℝ}
    (hd : 2 * 3.464102 / n0 + 24 / (n0 : ℝ) ^ 2 ≤ d) : deltaChi n 12 ≤ d := by
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : (0 : ℝ) < n0 := by linarith
  unfold deltaChi
  refine le_trans ?_ hd
  have h1 : 2 * √(12 : ℝ) / n ≤ 2 * 3.464102 / n0 := by gcongr
  have h2 : 2 * (12 : ℝ) / (n : ℝ) ^ 2 ≤ 24 / (n0 : ℝ) ^ 2 := by
    have : (n0 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hn0.le hnn 2
    calc 2 * (12 : ℝ) / (n : ℝ) ^ 2 = 24 / (n : ℝ) ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity) this
  linarith

/-- **The finite-centre cap on `n ≥ n0`.** The cap is the explicit rational function of
`n0` and the witnesses `r, w, d, s1, s2, s3`. -/
theorem finite_centre_upperP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n)
    {r w d s1 s2 s3 : ℝ} (hr0 : 0 < r) (hr : r ^ 2 ≤ n0) (hw : (1 + 2 / r) ^ 2 ≤ w)
    (hd : 2 * 3.464102 / n0 + 24 / (n0 : ℝ) ^ 2 ≤ d)
    (hs1 : 2 * (1 + 11 / 1000) * (1 + 2 * w * (81 / 1000 / n0)) ≤ s1 ^ 2) (hs10 : 0 ≤ s1)
    (hs2 : 2 * (1 + 11 / 1000) * w * (1 + d + 2 / 3.141592) / 1.29521 ≤ s2 ^ 2) (hs20 : 0 ≤ s2)
    (hs3 : 1 / 1.29521 ≤ s3 ^ 2) (hs30 : 0 ≤ s3) :
    finiteEnergy n n (11 / 1000) ≤
      (1792 / 10000 * s1 + 2 * (1792 / 10000) * s2 +
        4 * (1 / 2.506628) * w * s3 * (81 / 1000 + (1792 / 10000) ^ 2 / n0)) / r := by
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hn00 : (0 : ℝ) < n0 := by linarith
  have hrs : r ≤ √(n : ℝ) := le_sqrt_of_sq_le (hr.trans hnn)
  have hnrpos : 0 < √(n : ℝ) := sqrt_pos.mpr hnpos
  have ha := alphaJ_le (by omega : 1000 ≤ n)
  have hb := betaJ_le (by omega : 4096 ≤ n)
  have ha0 := alphaJ_nonneg n
  have hb0 := betaJ_nonneg n
  have hwn := wn_upperP h8 hn hr0 hr hw
  have hw0 : 0 ≤ wn n := by unfold wn; positivity
  have hw00 : 0 ≤ w := le_trans hw0 hwn
  have hc := BstLean.Part253.cs_lower
  have hdc := deltaChi_upperP h8 hn hd
  have hdc0 : 0 ≤ deltaChi n 12 := by unfold deltaChi; positivity
  have hd0 : 0 ≤ d := hdc0.trans hdc
  have hp := pi_gt_d6.le
  have h2pi : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith)
  have hbmax : betaJ n ≤ 81 / 1000 / (n0 : ℝ) :=
    hb.trans (div_le_div_of_nonneg_left (by norm_num) hn00 hnn)
  have hroot1 : √(2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * wn n * betaJ n) * n) ≤
      s1 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * (1 + 2 * w * (81 / 1000 / n0)) * n := by gcongr
      _ ≤ s1 ^ 2 * n := by gcongr
      _ = _ := by rw [mul_pow, sq_sqrt hn0]
  have hroot2 : √(2 * (1 + (11 / 1000 : ℝ)) * wn n * n *
      (1 + deltaChi n 12 + 2 / π) / csC) ≤ s2 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hpi : 2 / π ≤ 2 / (3.141592 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp
    calc
      _ ≤ 2 * (1 + (11 / 1000 : ℝ)) * w * n * (1 + d + 2 / 3.141592) / 1.29521 := by
        gcongr
      _ = (2 * (1 + (11 / 1000 : ℝ)) * w * (1 + d + 2 / 3.141592) / 1.29521) * n := by ring
      _ ≤ s2 ^ 2 * n := by gcongr
      _ = _ := by rw [mul_pow, sq_sqrt hn0]
  have hroot3 : √((n : ℝ) / csC) ≤ s3 * √(n : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (n : ℝ) / 1.29521 := div_le_div_of_nonneg_left hn0 (by norm_num) hc
      _ = (1 / 1.29521) * n := by ring
      _ ≤ s3 ^ 2 * n := by gcongr
      _ = _ := by rw [mul_pow, sq_sqrt hn0]
  have hα : alphaJ n ≤ 1792 / 10000 / n := ha
  have hinner : (81 / 1000 / (n : ℝ) + (1792 / 10000 / n) ^ 2) ≤
      (81 / 1000 + (1792 / 10000) ^ 2 / n0) / n := by
    have h1 : (1792 / 10000 / (n : ℝ)) ^ 2 = (1792 / 10000) ^ 2 / n ^ 2 := by
      rw [div_pow]
    have h2 : (1792 / 10000 : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤ (1792 / 10000) ^ 2 / n0 / n := by
      rw [div_div]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    rw [h1]
    calc 81 / 1000 / (n : ℝ) + (1792 / 10000) ^ 2 / (n : ℝ) ^ 2
        ≤ 81 / 1000 / (n : ℝ) + (1792 / 10000) ^ 2 / n0 / n := by linarith
      _ = _ := by ring
  calc
    _ ≤ (1792 / 10000 / (n : ℝ)) * (s1 * √(n : ℝ)) +
        2 * (1792 / 10000 / n) * (s2 * √(n : ℝ)) +
        4 * (1 / 2.506628) * w * (s3 * √(n : ℝ)) *
          ((81 / 1000 + (1792 / 10000) ^ 2 / n0) / n) := by
      unfold finiteEnergy epsJ
      have hs3' : 0 ≤ s3 * √(n : ℝ) := by positivity
      have hβ : betaJ n + alphaJ n ^ 2 ≤ (81 / 1000 + (1792 / 10000) ^ 2 / n0) / n := by
        refine le_trans ?_ hinner
        have : alphaJ n ^ 2 ≤ (1792 / 10000 / (n : ℝ)) ^ 2 := by gcongr
        have hb' : betaJ n ≤ 81 / 1000 / (n : ℝ) := hb
        linarith
      gcongr
    _ = (1792 / 10000 * s1 + 2 * (1792 / 10000) * s2 +
        4 * (1 / 2.506628) * w * s3 * (81 / 1000 + (1792 / 10000) ^ 2 / n0)) / √(n : ℝ) := by
      have he : (n : ℝ) = √(n : ℝ) ^ 2 := (sq_sqrt hn0).symm
      rw [he]
      rw [sqrt_sq (sqrt_nonneg (n : ℝ))]
      field_simp
    _ ≤ _ := by
      have hnum : 0 ≤ 1792 / 10000 * s1 + 2 * (1792 / 10000) * s2 +
          4 * (1 / 2.506628) * w * s3 * (81 / 1000 + (1792 / 10000) ^ 2 / n0) := by
        positivity
      exact div_le_div_of_nonneg_left hnum hr0 hrs

/-- The old `Part264.finite_centre_upper`, as an instance. -/
theorem finite_centre_12225 {n : ℕ} (hn : 12225 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (0.008646 : ℝ) :=
  (finite_centre_upperP (n0 := 12225) (by norm_num) hn (r := 110.566721) (w := 1.036505)
    (d := 0.0005669) (s1 := 1.421981) (s2 := 1.62763) (s3 := 0.878679)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num)

/-! ## `g±` guards -/

theorem gMinus_lowerP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {s t : ℝ}
    (ht : √(12 : ℝ) ≤ t) (hs : s ≤ √(1 - 2 / (n0 : ℝ) ^ 2)) (hst : 2 * t / n0 ≤ s) :
    (s - 2 * t / n0) ^ 2 ≤ gMinus n := by
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hn00 : (0 : ℝ) < n0 := by linarith
  have hns : (n0 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hn00.le hnn 2
  have hi : 2 / (n : ℝ) ^ 2 ≤ 2 / (n0 : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hns
  have hs' : s ≤ √(1 - 2 / (n : ℝ) ^ 2) := hs.trans (sqrt_le_sqrt (by linarith))
  have hd : 2 * √(12 : ℝ) / n ≤ 2 * t / n0 := by
    have hnp : (0 : ℝ) < n := by linarith
    calc 2 * √(12 : ℝ) / n ≤ 2 * t / n := by gcongr
      _ ≤ 2 * t / n0 := by
        have ht0 : 0 ≤ t := (sqrt_nonneg _).trans ht
        exact div_le_div_of_nonneg_left (by positivity) hn00 hnn
  unfold gMinus
  gcongr

theorem gPlus_upperP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {t : ℝ}
    (ht : √(12 : ℝ) ≤ t) : BstLean.Part211.gPlus n ≤ (1 + 2 * t / n0) ^ 2 := by
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hn00 : (0 : ℝ) < n0 := by linarith
  have ht0 : 0 ≤ t := (sqrt_nonneg _).trans ht
  unfold BstLean.Part211.gPlus
  have : 2 * √(12 : ℝ) / n ≤ 2 * t / n0 := by
    calc 2 * √(12 : ℝ) / n ≤ 2 * t / n := by gcongr
      _ ≤ 2 * t / n0 := div_le_div_of_nonneg_left (by positivity) hn00 hnn
  gcongr

theorem energy_root_guardP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {s t : ℝ}
    (ht : √(12 : ℝ) ≤ t) (hs : s ≤ √(1 - 2 / (n0 : ℝ) ^ 2)) (hst : 2 * t / n0 < s) :
    2 * √(12 : ℝ) / n < √(1 - 2 / (n : ℝ) ^ 2) := by
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hn00 : (0 : ℝ) < n0 := by linarith
  have hnp : (0 : ℝ) < n := by linarith
  have hns : (n0 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hn00.le hnn 2
  have hi : 2 / (n : ℝ) ^ 2 ≤ 2 / (n0 : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hns
  have hs' : s ≤ √(1 - 2 / (n : ℝ) ^ 2) := hs.trans (sqrt_le_sqrt (by linarith))
  have ht0 : 0 ≤ t := (sqrt_nonneg _).trans ht
  have hd : 2 * √(12 : ℝ) / n ≤ 2 * t / n0 :=
    calc 2 * √(12 : ℝ) / n ≤ 2 * t / n := by gcongr
      _ ≤ 2 * t / n0 := div_le_div_of_nonneg_left (by positivity) hn00 hnn
  linarith

/-- The old `Part264.gMinus_lower` at 12225, as an instance. -/
theorem gMinus_lower_12225 {n : ℕ} (hn : 12225 ≤ n) : (0.99886685 : ℝ) ≤ gMinus n := by
  have h := gMinus_lowerP (n0 := 12225) (by norm_num) hn (s := 0.9999999933) (t := 3.464102)
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num)
  exact le_trans (by norm_num) h

/-- The old `Part264.gPlus_upper` at 12225, as an instance. -/
theorem gPlus_upper_12225 {n : ℕ} (hn : 12225 ≤ n) :
    BstLean.Part211.gPlus n ≤ 1.00113378 :=
  (gPlus_upperP (n0 := 12225) (by norm_num) hn (t := 3.464102)
    (sqrt_le_iff.mpr (by norm_num))).trans (by norm_num)

theorem energy_root_guard_12225 {n : ℕ} (hn : 12225 ≤ n) :
    2 * √(12 : ℝ) / n < √(1 - 2 / (n : ℝ) ^ 2) :=
  energy_root_guardP (n0 := 12225) (by norm_num) hn (s := 0.9999999933) (t := 3.464102)
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num)

end BstLean.Part277
