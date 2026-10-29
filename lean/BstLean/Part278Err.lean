import BstLean.Part278Ref
import BstLean.Part159Pi

/-!
# Part 278 (O2): the error of the odd arithmetic rule

Paper: `theorem7-01-statement-program.tex`, Lemma `t7:p01:odd-error`.

`ε₀ = eps0 n = 1/(10¹¹⁰ n²⁰)`.
* `piO_err`: `|π_o − π| ≤ 4ε₀` (Machin with `T_{π,o}` terms).
* `arcsin_half_angle`: `arcsin v = π/2 − 2 arcsin √((1 − v)/2)` on `[−1, 1]`.
* `asinO_err`: `|arcsin_o v − arcsin v| ≤ 4ε₀` for `|v| ≤ 1`.
* `KK_err`: `|K_r^{o}(d) − K_r(d)| ≤ 6ε₀` for `|d| ≤ 1` and every `r`.
* `oddA_err`, `oddE_err`: the moment combinations, errors `5nε₀a` and `13nε₀a²`.
* `odd_rule_err`: for odd `n ≥ 8001`, `|m| ≤ a`, `0 ≤ k ≤ a`, the clipped arithmetic rule is within
  `10⁻⁹⁰ n⁻¹⁰ a` (first moment) and `3·10⁻⁹⁰ n⁻¹⁰ a²` (second moment) of the exact moments.
-/

namespace BstLean.Part278

open Real MeasureTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53)
open BstLean.Part130 (relu measurable_relu)
open BstLean.Part157 (ATsum QTsum)
open BstLean.Part272 (DD Todd Tpio piO asinPos asinO oddA oddE sphAodd sphEodd
  integrable_coord_comp relu_bound relu_sq_bound)

/-- `ε₀ = 1/(10¹¹⁰ n²⁰)`. -/
noncomputable def eps0 (n : ℕ) : ℝ := 1 / (10 ^ 110 * (n : ℝ) ^ 20)

theorem eps0_pos {n : ℕ} (hn : 1 ≤ n) : 0 < eps0 n := by
  have : (0:ℝ) < n := by exact_mod_cast hn
  unfold eps0
  exact div_pos one_pos (mul_pos (by norm_num) (pow_pos this 20))

theorem eps0_small {n : ℕ} (hn : 1 ≤ n) : eps0 n ≤ 1 / 10 ^ 110 := by
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (1:ℝ) ≤ (n:ℝ) ^ 20 := one_le_pow₀ h1
  unfold eps0
  exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)

/-- `n·ε₀·n¹⁰ ≤ 10⁻¹¹⁰`. -/
theorem neps_small {n : ℕ} (hn : 1 ≤ n) : (n : ℝ) * eps0 n * (n : ℝ) ^ 10 ≤ 1 / 10 ^ 110 := by
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h11 : (n:ℝ) ^ 11 ≤ (n:ℝ) ^ 20 := pow_le_pow_right₀ h1 (by norm_num)
  have e : (n : ℝ) * eps0 n * (n : ℝ) ^ 10 = (n:ℝ) ^ 11 / (10 ^ 110 * (n:ℝ) ^ 20) := by
    unfold eps0; ring
  have hn0 : (0:ℝ) < n := by linarith
  rw [e, div_le_div_iff₀ (mul_pos (by norm_num) (pow_pos hn0 20)) (by norm_num)]
  nlinarith

theorem Todd_spec (n : ℕ) : 1 ≤ Todd n ∧ 10 ^ 110 * n ^ 20 ≤ 4 ^ Todd n := by
  have hne : {T : ℕ | 1 ≤ T ∧ 10 ^ 110 * n ^ 20 ≤ 4 ^ T}.Nonempty := by
    refine ⟨10 ^ 110 * n ^ 20 + 1, by omega, ?_⟩
    have h := Nat.lt_pow_self (by norm_num : 1 < 4) (n := 10 ^ 110 * n ^ 20 + 1)
    omega
  exact Nat.sInf_mem hne

theorem Tpio_spec (n : ℕ) : 1 ≤ Tpio n ∧ 10 ^ 110 * n ^ 20 ≤ 25 ^ Tpio n := by
  have hne : {T : ℕ | 1 ≤ T ∧ 10 ^ 110 * n ^ 20 ≤ 25 ^ T}.Nonempty := by
    refine ⟨10 ^ 110 * n ^ 20 + 1, by omega, ?_⟩
    have h := Nat.lt_pow_self (by norm_num : 1 < 25) (n := 10 ^ 110 * n ^ 20 + 1)
    omega
  exact Nat.sInf_mem hne

theorem quarter_pow_le {n : ℕ} (hn : 1 ≤ n) : (1 / 4 : ℝ) ^ Todd n ≤ eps0 n := by
  have hb : ((10:ℝ) ^ 110 * (n:ℝ) ^ 20) ≤ (4:ℝ) ^ Todd n := by exact_mod_cast (Todd_spec n).2
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  rw [div_pow, one_pow]; unfold eps0
  exact one_div_le_one_div_of_le (mul_pos (by norm_num) (pow_pos hnpos 20)) hb

theorem pow25_le {n : ℕ} (hn : 1 ≤ n) : (1 / 25 : ℝ) ^ Tpio n ≤ eps0 n := by
  have hb : ((10:ℝ) ^ 110 * (n:ℝ) ^ 20) ≤ (25:ℝ) ^ Tpio n := by exact_mod_cast (Tpio_spec n).2
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  rw [div_pow, one_pow]; unfold eps0
  exact one_div_le_one_div_of_le (mul_pos (by norm_num) (pow_pos hnpos 20)) hb

/-- The inverse sine series on `[0, 1/2]` with `T_o` terms: error at most `ε₀`. -/
theorem QT_err {n : ℕ} (hn : 1 ≤ n) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1 / 2) :
    0 ≤ arcsin w - QTsum (Todd n) w ∧ arcsin w - QTsum (Todd n) w ≤ eps0 n := by
  obtain ⟨hT1, _⟩ := Todd_spec n
  obtain ⟨h0, h1⟩ := BstLean.Part159.QTsum_err hT1 hw0 (by linarith : w < 1)
  refine ⟨h0, h1.trans ?_⟩
  have hden : 0 < 1 - w ^ 2 := by nlinarith
  have hq1 : (w ^ 2) ^ (Todd n) ≤ (1 / 4) ^ (Todd n) :=
    pow_le_pow_left₀ (sq_nonneg w) (by nlinarith) _
  have hX : (0:ℝ) ≤ (1 / 4) ^ (Todd n) := by positivity
  have hq : w * (w ^ 2) ^ (Todd n) / (1 - w ^ 2) ≤ (1 / 4) ^ (Todd n) := by
    rw [div_le_iff₀ hden]
    calc w * (w ^ 2) ^ (Todd n) ≤ (1 / 2) * (1 / 4) ^ (Todd n) :=
          mul_le_mul hw1 hq1 (by positivity) (by norm_num)
      _ ≤ (1 / 4) ^ (Todd n) * (1 - w ^ 2) := by
          nlinarith [mul_nonneg hX (by nlinarith : (0:ℝ) ≤ 1 / 2 - w ^ 2)]
  exact hq.trans (quarter_pow_le hn)

/-- Machin's sums with `T` terms. -/
theorem piSum_err (T : ℕ) :
    |16 * ATsum T (1 / 5) - 4 * ATsum T (1 / 239) - π| ≤ 4 * (1 / 25 : ℝ) ^ T := by
  have h1 := BstLean.Part159.ATsum_err T (x := 1 / 5) (by norm_num) (by norm_num)
  have h2 := BstLean.Part159.ATsum_err T (x := 1 / 239) (by norm_num) (by norm_num)
  have e1 : ((1 / 5 : ℝ) ^ 2) = 1 / 25 := by norm_num
  have e2 : ((1 / 239 : ℝ) ^ 2) ^ T ≤ (1 / 25 : ℝ) ^ T :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  rw [e1] at h1
  have hp : (0 : ℝ) ≤ (1 / 25 : ℝ) ^ T := by positivity
  have h2' : |ATsum T (1 / 239) - arctan (1 / 239)| ≤
      1 / 239 * (1 / 25 : ℝ) ^ T / (1 - (1 / 239) ^ 2) := by
    refine h2.trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left e2 (by norm_num)) (by norm_num)
  have e : 16 * ATsum T (1 / 5) - 4 * ATsum T (1 / 239) - π =
      16 * (ATsum T (1 / 5) - arctan (1 / 5)) - 4 * (ATsum T (1 / 239) - arctan (1 / 239)) := by
    rw [BstLean.Part159.machin]
    ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16),
    abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have a1 : 16 * |ATsum T (1 / 5) - arctan (1 / 5)| ≤
      16 * (1 / 5 * (1 / 25 : ℝ) ^ T / (1 - 1 / 25)) :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  have a2 : 4 * |ATsum T (1 / 239) - arctan (1 / 239)| ≤
      4 * (1 / 239 * (1 / 25 : ℝ) ^ T / (1 - (1 / 239) ^ 2)) :=
    mul_le_mul_of_nonneg_left h2' (by norm_num)
  have a3 : 16 * (1 / 5 * (1 / 25 : ℝ) ^ T / (1 - 1 / 25)) +
      4 * (1 / 239 * (1 / 25 : ℝ) ^ T / (1 - (1 / 239) ^ 2)) ≤ 4 * (1 / 25 : ℝ) ^ T := by
    have e3 : 16 * (1 / 5 * (1 / 25 : ℝ) ^ T / (1 - 1 / 25)) +
        4 * (1 / 239 * (1 / 25 : ℝ) ^ T / (1 - (1 / 239) ^ 2)) =
        (16 * (1 / 5) / (1 - 1 / 25) + 4 * (1 / 239) / (1 - (1 / 239) ^ 2)) *
          (1 / 25 : ℝ) ^ T := by ring
    rw [e3]
    exact mul_le_mul_of_nonneg_right (by norm_num) hp
  linarith

/-- `|π_o − π| ≤ 4ε₀`. -/
theorem piO_err {n : ℕ} (hn : 1 ≤ n) : |piO n - π| ≤ 4 * eps0 n := by
  have h := piSum_err (Tpio n)
  have h25 := pow25_le hn
  unfold piO
  exact h.trans (by linarith)

/-- The half-angle identity. -/
theorem arcsin_half_angle {v : ℝ} (h1 : -1 ≤ v) (h2 : v ≤ 1) :
    arcsin v = π / 2 - 2 * arcsin (√((1 - v) / 2)) := by
  have hw0 : 0 ≤ √((1 - v) / 2) := sqrt_nonneg _
  have hww : √((1 - v) / 2) ^ 2 = (1 - v) / 2 := sq_sqrt (by linarith)
  have hw1 : √((1 - v) / 2) ≤ 1 := by nlinarith
  have hθ0 : 0 ≤ arcsin (√((1 - v) / 2)) := arcsin_nonneg.mpr hw0
  have hθ1 : arcsin (√((1 - v) / 2)) ≤ π / 2 := arcsin_le_pi_div_two _
  have hs : sin (π / 2 - 2 * arcsin (√((1 - v) / 2))) = v := by
    rw [sin_pi_div_two_sub, cos_two_mul, cos_sq', sin_arcsin (by linarith) hw1, hww]
    ring
  calc arcsin v = arcsin (sin (π / 2 - 2 * arcsin (√((1 - v) / 2)))) := by rw [hs]
    _ = π / 2 - 2 * arcsin (√((1 - v) / 2)) := arcsin_sin (by linarith) (by linarith)

theorem asinPos_err {n : ℕ} (hn : 1 ≤ n) {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    |asinPos n v - arcsin v| ≤ 4 * eps0 n := by
  have he := eps0_pos hn
  unfold asinPos
  split_ifs with h
  · obtain ⟨a, b⟩ := QT_err hn h0 h
    rw [abs_sub_comm, abs_of_nonneg a]
    linarith
  · have hv : 1 / 2 < v := lt_of_not_ge h
    have hw0 : 0 ≤ √((1 - v) / 2) := sqrt_nonneg _
    have hww : √((1 - v) / 2) ^ 2 = (1 - v) / 2 := sq_sqrt (by linarith)
    have hw1 : √((1 - v) / 2) ≤ 1 / 2 := by nlinarith
    obtain ⟨a, b⟩ := QT_err hn hw0 hw1
    have hp := piO_err hn
    rw [arcsin_half_angle (by linarith) h1]
    rw [abs_le] at hp ⊢
    constructor <;> linarith [hp.1, hp.2]

/-- `|arcsin_o v − arcsin v| ≤ 4ε₀` for `|v| ≤ 1`. -/
theorem asinO_err {n : ℕ} (hn : 1 ≤ n) {v : ℝ} (hv : |v| ≤ 1) :
    |asinO n v - arcsin v| ≤ 4 * eps0 n := by
  have h := abs_le.mp hv
  unfold asinO
  split_ifs with h0
  · exact asinPos_err hn h0 h.2
  · have h' := asinPos_err hn (v := -v) (by linarith [lt_of_not_ge h0]) (by linarith)
    rw [arcsin_neg] at h'
    rw [show -asinPos n (-v) - arcsin v = -(asinPos n (-v) - -arcsin v) by ring, abs_neg]
    exact h'

/-- `|K_r^{o}(d) − K_r(d)| ≤ 6ε₀`. -/
theorem KK_err {n : ℕ} (hn : 1 ≤ n) {d : ℝ} (hd : |d| ≤ 1) (r : ℕ) :
    |BstLean.Part272.KK n d r - KK r d| ≤ 6 * eps0 n := by
  induction r with
  | zero =>
    have e1 : BstLean.Part272.KK n d 0 = piO n / 2 - asinO n d := by
      first | rfl | simp [BstLean.Part272.KK]
    have e2 : KK 0 d = π / 2 - arcsin d := by rw [KK_zero_fun]
    rw [e1, e2]
    have h1 := piO_err hn
    have h2 := asinO_err hn hd
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  | succ r ih =>
    have e1 : BstLean.Part272.KK n d (r + 1) =
        (2 * ((r : ℝ) + 1) - 1) / (2 * ((r : ℝ) + 1)) * BstLean.Part272.KK n d r -
          d * ((1 - d ^ 2) ^ r * √(1 - d ^ 2)) / (2 * ((r : ℝ) + 1)) := by
      first | rfl | simp [BstLean.Part272.KK]
    have e2 : KK (r + 1) d =
        (2 * ((r : ℝ) + 1) - 1) / (2 * ((r : ℝ) + 1)) * KK r d -
          d * ((1 - d ^ 2) ^ r * √(1 - d ^ 2)) / (2 * ((r : ℝ) + 1)) := by
      rw [KK_succ_fun]
    have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
    have hc0 : 0 ≤ (2 * ((r : ℝ) + 1) - 1) / (2 * ((r : ℝ) + 1)) :=
      div_nonneg (by linarith) (by positivity)
    have hc1 : (2 * ((r : ℝ) + 1) - 1) / (2 * ((r : ℝ) + 1)) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    rw [e1, e2, show ∀ a b c e : ℝ, a * b - e - (a * c - e) = a * (b - c) from
      fun a b c e => by ring, abs_mul, abs_of_nonneg hc0]
    exact (mul_le_of_le_one_left (abs_nonneg _) hc1).trans ih

/-! ## Bounds on `K_r`, `D_P` and `J₁` -/

theorem KK_diff (r : ℕ) {a b : ℝ} (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∫ z in a..b, (1 - z ^ 2) ^ r / √(1 - z ^ 2) = KK r a - KK r b := by
  have hcont : ContinuousOn (fun y => -KK r y) (Icc a b) := (continuous_KK r).neg.continuousOn
  have hderiv : ∀ x ∈ Ioo a b, HasDerivAt (fun y => -KK r y)
      ((1 - x ^ 2) ^ r / √(1 - x ^ 2)) x := fun x hx =>
    (hasDerivAt_KK r ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩).fun_neg.congr_deriv
      (neg_neg _)
  have hpos : ∀ x ∈ Ioo a b, 0 ≤ (1 - x ^ 2) ^ r / √(1 - x ^ 2) := fun x hx =>
    div_nonneg (pow_nonneg (one_sub_sq_nonneg ⟨ha.trans hx.1.le, hx.2.le.trans hb⟩) r)
      (sqrt_nonneg _)
  have hint : IntervalIntegrable (fun x => (1 - x ^ 2) ^ r / √(1 - x ^ 2)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv hpos)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint]
  ring

theorem KK_nonneg (r : ℕ) {d : ℝ} (hd : |d| ≤ 1) : 0 ≤ KK r d := by
  have h := abs_le.mp hd
  have e := KK_diff r h.1 h.2 le_rfl
  rw [KK_one, sub_zero] at e
  rw [← e]
  exact intervalIntegral.integral_nonneg h.2 fun u hu =>
    div_nonneg (pow_nonneg (one_sub_sq_nonneg ⟨h.1.trans hu.1, hu.2⟩) r) (sqrt_nonneg _)

theorem KK_neg_one_le (r : ℕ) : KK r (-1) ≤ π := by
  induction r with
  | zero =>
    rw [KK_zero_fun]
    show π / 2 - arcsin (-1) ≤ π
    rw [arcsin_neg_one]
    linarith
  | succ r ih =>
    rw [KK_succ_neg_one]
    have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
    have hc1 : (2 * ((r : ℝ) + 1) - 1) / (2 * ((r : ℝ) + 1)) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    have hK := KK_nonneg r (d := -1) (by norm_num)
    calc (2 * ((r : ℝ) + 1) - 1) / (2 * ((r : ℝ) + 1)) * KK r (-1) ≤ 1 * KK r (-1) :=
          mul_le_mul_of_nonneg_right hc1 hK
      _ ≤ π := by linarith

theorem KK_le_pi (r : ℕ) {d : ℝ} (hd : |d| ≤ 1) : KK r d ≤ π := by
  have h := abs_le.mp hd
  have e := KK_diff r (le_refl (-1)) h.1 h.2
  have hI : 0 ≤ ∫ z in (-1:ℝ)..d, (1 - z ^ 2) ^ r / √(1 - z ^ 2) :=
    intervalIntegral.integral_nonneg h.1 fun u hu =>
      div_nonneg (pow_nonneg (one_sub_sq_nonneg ⟨hu.1, hu.2.trans h.2⟩) r) (sqrt_nonneg _)
  linarith [KK_neg_one_le r]

theorem DD_le (r : ℕ) : DD r ≤ 2 * ((r : ℝ) + 1) := by
  induction r with
  | zero => norm_num [DD]
  | succ r ih =>
    simp only [DD]
    push_cast
    have h0 := DD_pos r
    have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right ih (by positivity : (0:ℝ) ≤ 2 * ((r:ℝ) + 1) + 2)]

/-- `J₁ = (1 − d²)^{P+3/2}/(2P+3)`. -/
noncomputable def Jv (P : ℕ) (d : ℝ) : ℝ :=
  (1 - d ^ 2) ^ (P + 1) * √(1 - d ^ 2) / (2 * (P : ℝ) + 3)

theorem Jv_nonneg (P : ℕ) {d : ℝ} (hd : |d| ≤ 1) : 0 ≤ Jv P d := by
  have h := abs_le.mp hd
  unfold Jv
  exact div_nonneg (mul_nonneg (pow_nonneg (one_sub_sq_nonneg ⟨h.1, h.2⟩) _) (sqrt_nonneg _))
    (by positivity)

theorem Jv_le_one (P : ℕ) {d : ℝ} (hd : |d| ≤ 1) : Jv P d ≤ 1 := by
  have h := abs_le.mp hd
  have hW0 := one_sub_sq_nonneg ⟨h.1, h.2⟩
  have hW1 : 1 - d ^ 2 ≤ 1 := by nlinarith [sq_nonneg d]
  have h1 : (1 - d ^ 2) ^ (P + 1) ≤ 1 := pow_le_one₀ hW0 hW1
  have h2 : √(1 - d ^ 2) ≤ 1 := (sqrt_le_sqrt hW1).trans_eq sqrt_one
  have hP0 : (0:ℝ) ≤ P := Nat.cast_nonneg P
  unfold Jv
  rw [div_le_one (by positivity)]
  calc (1 - d ^ 2) ^ (P + 1) * √(1 - d ^ 2) ≤ 1 * 1 :=
        mul_le_mul h1 h2 (sqrt_nonneg _) zero_le_one
    _ ≤ 2 * (P : ℝ) + 3 := by linarith

theorem oddA_eq (n : ℕ) (m k : ℝ) : oddA n m k = DD ((n - 5) / 2) / piO n *
    (m * BstLean.Part272.KK n (-m / k) ((n - 5) / 2 + 1) + k * Jv ((n - 5) / 2) (-m / k)) := rfl

theorem oddARef_eq (n : ℕ) (m k : ℝ) : oddARef n m k = DD ((n - 5) / 2) / π *
    (m * KK ((n - 5) / 2 + 1) (-m / k) + k * Jv ((n - 5) / 2) (-m / k)) := rfl

theorem oddE_eq (n : ℕ) (m k : ℝ) : oddE n m k = DD ((n - 5) / 2) / piO n *
    (m ^ 2 * BstLean.Part272.KK n (-m / k) ((n - 5) / 2 + 1) +
      2 * m * k * Jv ((n - 5) / 2) (-m / k) +
      k ^ 2 * (BstLean.Part272.KK n (-m / k) ((n - 5) / 2 + 1) -
        BstLean.Part272.KK n (-m / k) ((n - 5) / 2 + 2))) := rfl

theorem oddERef_eq (n : ℕ) (m k : ℝ) : oddERef n m k = DD ((n - 5) / 2) / π *
    (m ^ 2 * KK ((n - 5) / 2 + 1) (-m / k) + 2 * m * k * Jv ((n - 5) / 2) (-m / k) +
      k ^ 2 * (KK ((n - 5) / 2 + 1) (-m / k) - KK ((n - 5) / 2 + 2) (-m / k))) := rfl

/-! ## The abstract assembly -/

/-- `D/p·X_o − D/π·(X_o − δ)`, with `|p − π| ≤ 4e`. -/
theorem assemble {D p Xo dX nn e B C : ℝ} (hD : 0 < D) (hDn : D ≤ nn) (hp : |p - π| ≤ 4 * e)
    (he : 0 ≤ e) (he1 : e ≤ 1 / 1000) (hXo : |Xo| ≤ B) (hdX : |dX| ≤ C) :
    |D / p * Xo - D / π * (Xo - dX)| ≤ nn * (4 * e / 9) * B + nn / 3 * C := by
  have hpa := abs_le.mp hp
  have hpi1 := pi_gt_d2
  have hpi3 := pi_gt_three
  have hp3 : 3 ≤ p := by norm_num at hpi1; linarith [hpa.1]
  have hp0 : 0 < p := by linarith
  have h9 : 9 ≤ p * π := by nlinarith
  have hB : 0 ≤ B := (abs_nonneg _).trans hXo
  have hC : 0 ≤ C := (abs_nonneg _).trans hdX
  have hid : D / p * Xo - D / π * (Xo - dX) = D * ((π - p) / (p * π)) * Xo + D / π * dX := by
    field_simp
    ring
  rw [hid]
  have h1 : |D * ((π - p) / (p * π))| ≤ nn * (4 * e / 9) := by
    rw [abs_mul, abs_of_pos hD, abs_div, abs_of_pos (mul_pos hp0 pi_pos)]
    refine mul_le_mul hDn ?_ (div_nonneg (abs_nonneg _) (mul_pos hp0 pi_pos).le) (hD.le.trans hDn)
    rw [div_le_iff₀ (mul_pos hp0 pi_pos), abs_sub_comm]
    nlinarith [mul_nonneg he (sub_nonneg.mpr h9)]
  have h2 : |D / π| ≤ nn / 3 := by
    rw [abs_div, abs_of_pos hD, abs_of_pos pi_pos, div_le_div_iff₀ pi_pos (by norm_num)]
    nlinarith [mul_nonneg (hD.le.trans hDn) (sub_nonneg.mpr hpi3.le)]
  calc |D * ((π - p) / (p * π)) * Xo + D / π * dX|
      ≤ |D * ((π - p) / (p * π)) * Xo| + |D / π * dX| := abs_add_le _ _
    _ = |D * ((π - p) / (p * π))| * |Xo| + |D / π| * |dX| := by
        rw [abs_mul (D * ((π - p) / (p * π))) Xo, abs_mul (D / π) dX]
    _ ≤ nn * (4 * e / 9) * B + nn / 3 * C :=
        add_le_add (mul_le_mul h1 hXo (abs_nonneg _) (mul_nonneg (hD.le.trans hDn) (by linarith)))
          (mul_le_mul h2 hdX (abs_nonneg _) (div_nonneg (hD.le.trans hDn) (by norm_num)))

theorem errA_abs {D p Ko K J m k a e nn : ℝ} (hD : 0 < D) (hDn : D ≤ nn)
    (hp : |p - π| ≤ 4 * e) (he : 0 ≤ e) (he1 : e ≤ 1 / 1000) (hKK : |Ko - K| ≤ 6 * e)
    (hK0 : 0 ≤ K) (hKpi : K ≤ π) (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (hk : 0 < k)
    (hma : |m| ≤ a) (hka : k ≤ a) :
    |D / p * (m * Ko + k * J) - D / π * (m * K + k * J)| ≤ 5 * nn * e * a := by
  have ha : 0 ≤ a := (abs_nonneg m).trans hma
  have hpi := pi_lt_d2
  norm_num at hpi
  have hKo : |Ko| ≤ 4 := by
    have := abs_le.mp hKK
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hXo : |m * Ko + k * J| ≤ 5 * a := by
    calc |m * Ko + k * J| ≤ |m * Ko| + |k * J| := abs_add_le _ _
      _ = |m| * |Ko| + k * J := by rw [abs_mul, abs_mul, abs_of_pos hk, abs_of_nonneg hJ0]
      _ ≤ a * 4 + a * 1 :=
          add_le_add (mul_le_mul hma hKo (abs_nonneg _) ha) (mul_le_mul hka hJ1 hJ0 ha)
      _ = 5 * a := by ring
  have hdX : |m * (Ko - K)| ≤ a * (6 * e) := by
    rw [abs_mul]; exact mul_le_mul hma hKK (abs_nonneg _) ha
  have h := assemble hD hDn hp he he1 hXo hdX
  have e1 : m * K + k * J = m * Ko + k * J - m * (Ko - K) := by ring
  rw [e1]
  have hnn : 0 ≤ nn := hD.le.trans hDn
  refine h.trans ?_
  nlinarith [mul_nonneg (mul_nonneg hnn he) ha]

theorem errE_abs {D p Ko1 Ko2 K1 K2 J m k a e nn : ℝ} (hD : 0 < D) (hDn : D ≤ nn)
    (hp : |p - π| ≤ 4 * e) (he : 0 ≤ e) (he1 : e ≤ 1 / 1000)
    (hK1 : |Ko1 - K1| ≤ 6 * e) (hK2 : |Ko2 - K2| ≤ 6 * e)
    (hK10 : 0 ≤ K1) (hK1pi : K1 ≤ π) (hK20 : 0 ≤ K2) (hK2pi : K2 ≤ π)
    (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (hk : 0 < k) (hma : |m| ≤ a) (hka : k ≤ a) :
    |D / p * (m ^ 2 * Ko1 + 2 * m * k * J + k ^ 2 * (Ko1 - Ko2)) -
      D / π * (m ^ 2 * K1 + 2 * m * k * J + k ^ 2 * (K1 - K2))| ≤ 13 * nn * e * a ^ 2 := by
  have ha : 0 ≤ a := (abs_nonneg m).trans hma
  have hpi := pi_lt_d2
  norm_num at hpi
  have hm2 : m ^ 2 ≤ a ^ 2 := by
    rw [← sq_abs m]; exact pow_le_pow_left₀ (abs_nonneg _) hma 2
  have hk2 : k ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hk.le hka 2
  have hKo1 : |Ko1| ≤ 4 := by
    have := abs_le.mp hK1
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hKo12 : |Ko1 - Ko2| ≤ 8 := by
    have := abs_le.mp hK1
    have := abs_le.mp hK2
    rw [abs_le]; constructor <;> linarith
  have hmk : |2 * m * k * J| ≤ 2 * a ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hk, abs_of_nonneg hJ0, abs_two]
    have h1 : |m| * k ≤ a * a := mul_le_mul hma hka hk.le ha
    have h2 : 0 ≤ |m| * k := mul_nonneg (abs_nonneg _) hk.le
    nlinarith [mul_le_mul_of_nonneg_left hJ1 h2]
  have hXo : |m ^ 2 * Ko1 + 2 * m * k * J + k ^ 2 * (Ko1 - Ko2)| ≤ 14 * a ^ 2 := by
    calc |m ^ 2 * Ko1 + 2 * m * k * J + k ^ 2 * (Ko1 - Ko2)|
        ≤ |m ^ 2 * Ko1 + 2 * m * k * J| + |k ^ 2 * (Ko1 - Ko2)| := abs_add_le _ _
      _ ≤ |m ^ 2 * Ko1| + |2 * m * k * J| + |k ^ 2 * (Ko1 - Ko2)| := by
          linarith [abs_add_le (m ^ 2 * Ko1) (2 * m * k * J)]
      _ = m ^ 2 * |Ko1| + |2 * m * k * J| + k ^ 2 * |Ko1 - Ko2| := by
          rw [abs_mul (m ^ 2) Ko1, abs_mul (k ^ 2) (Ko1 - Ko2), abs_of_nonneg (sq_nonneg m),
            abs_of_nonneg (sq_nonneg k)]
      _ ≤ a ^ 2 * 4 + 2 * a ^ 2 + a ^ 2 * 8 := by
          have := mul_le_mul hm2 hKo1 (abs_nonneg _) (sq_nonneg a)
          have := mul_le_mul hk2 hKo12 (abs_nonneg _) (sq_nonneg a)
          linarith
      _ = 14 * a ^ 2 := by ring
  have hdX : |m ^ 2 * (Ko1 - K1) + k ^ 2 * ((Ko1 - K1) - (Ko2 - K2))| ≤ a ^ 2 * (18 * e) := by
    have h12 : |(Ko1 - K1) - (Ko2 - K2)| ≤ 12 * e := by
      have := abs_le.mp hK1
      have := abs_le.mp hK2
      rw [abs_le]; constructor <;> linarith
    calc |m ^ 2 * (Ko1 - K1) + k ^ 2 * ((Ko1 - K1) - (Ko2 - K2))|
        ≤ |m ^ 2 * (Ko1 - K1)| + |k ^ 2 * ((Ko1 - K1) - (Ko2 - K2))| := abs_add_le _ _
      _ = m ^ 2 * |Ko1 - K1| + k ^ 2 * |(Ko1 - K1) - (Ko2 - K2)| := by
          rw [abs_mul (m ^ 2) (Ko1 - K1), abs_mul (k ^ 2) ((Ko1 - K1) - (Ko2 - K2)),
            abs_of_nonneg (sq_nonneg m), abs_of_nonneg (sq_nonneg k)]
      _ ≤ a ^ 2 * (6 * e) + a ^ 2 * (12 * e) := by
          have := mul_le_mul hm2 hK1 (abs_nonneg _) (sq_nonneg a)
          have := mul_le_mul hk2 h12 (abs_nonneg _) (sq_nonneg a)
          linarith
      _ = a ^ 2 * (18 * e) := by ring
  have h := assemble hD hDn hp he he1 hXo hdX
  have e1 : m ^ 2 * K1 + 2 * m * k * J + k ^ 2 * (K1 - K2) =
      (m ^ 2 * Ko1 + 2 * m * k * J + k ^ 2 * (Ko1 - Ko2)) -
        (m ^ 2 * (Ko1 - K1) + k ^ 2 * ((Ko1 - K1) - (Ko2 - K2))) := by ring
  rw [e1]
  have hnn : 0 ≤ nn := hD.le.trans hDn
  refine h.trans ?_
  nlinarith [mul_nonneg (mul_nonneg hnn he) (sq_nonneg a)]

/-! ## The moment combinations -/

theorem DD_le_n {n : ℕ} (hn : 9 ≤ n) : DD ((n - 5) / 2) ≤ n := by
  have h := DD_le ((n - 5) / 2)
  have hc : 2 * ((n - 5) / 2) + 2 ≤ n := by omega
  have hc' : (2 * (((n - 5) / 2 : ℕ) : ℝ) + 2) ≤ n := by exact_mod_cast hc
  linarith

theorem oddA_err {n : ℕ} (hn : 9 ≤ n) {m k a : ℝ} (hk : 0 < k) (hm1 : -k < m) (hm2 : m < k)
    (hma : |m| ≤ a) (hka : k ≤ a) :
    |oddA n m k - oddARef n m k| ≤ 5 * n * eps0 n * a := by
  have hd := abs_d_le hk hm1 hm2
  have hn1 : 1 ≤ n := by omega
  rw [oddA_eq, oddARef_eq]
  exact errA_abs (DD_pos _) (DD_le_n hn) (piO_err hn1) (eps0_pos hn1).le
    ((eps0_small hn1).trans (by norm_num)) (KK_err hn1 hd _) (KK_nonneg _ hd) (KK_le_pi _ hd)
    (Jv_nonneg _ hd) (Jv_le_one _ hd) hk hma hka

theorem oddE_err {n : ℕ} (hn : 9 ≤ n) {m k a : ℝ} (hk : 0 < k) (hm1 : -k < m) (hm2 : m < k)
    (hma : |m| ≤ a) (hka : k ≤ a) :
    |oddE n m k - oddERef n m k| ≤ 13 * n * eps0 n * a ^ 2 := by
  have hd := abs_d_le hk hm1 hm2
  have hn1 : 1 ≤ n := by omega
  rw [oddE_eq, oddERef_eq]
  exact errE_abs (DD_pos _) (DD_le_n hn) (piO_err hn1) (eps0_pos hn1).le
    ((eps0_small hn1).trans (by norm_num)) (KK_err hn1 hd _) (KK_err hn1 hd _)
    (KK_nonneg _ hd) (KK_le_pi _ hd) (KK_nonneg _ hd) (KK_le_pi _ hd)
    (Jv_nonneg _ hd) (Jv_le_one _ hd) hk hma hka

/-! ## The clips -/

theorem clip0 {x y : ℝ} (hy : 0 ≤ y) : |max 0 x - y| ≤ |x - y| := by
  rcases le_total 0 x with h | h
  · simp only [max_eq_right h, le_refl]
  · rw [max_eq_left h, abs_le]
    constructor <;> linarith [neg_abs_le (x - y), abs_nonneg (x - y)]

theorem clipE {x Y y' y δ δE M : ℝ} (hY : y ^ 2 ≤ Y) (hy0 : 0 ≤ y) (hyM : y ≤ M)
    (hy'0 : 0 ≤ y') (hd : |y' - y| ≤ δ) (hx : |x - Y| ≤ δE) :
    |max x (y' ^ 2) - Y| ≤ δE + δ * (2 * M + δ) := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hd
  have hδE : 0 ≤ δE := (abs_nonneg _).trans hx
  have hM : 0 ≤ M := hy0.trans hyM
  have hprod : 0 ≤ δ * (2 * M + δ) := mul_nonneg hδ (by linarith)
  rcases le_total (y' ^ 2) x with h | h
  · rw [max_eq_left h]; linarith
  · rw [max_eq_right h, abs_le]
    have hd' := abs_le.mp hd
    have hx' := abs_le.mp hx
    constructor
    · linarith [hx'.1]
    · have h1 : y' ^ 2 ≤ (y + δ) ^ 2 := pow_le_pow_left₀ hy'0 (by linarith [hd'.2]) 2
      have h2 : 0 ≤ δ * (M - y) := mul_nonneg hδ (by linarith)
      nlinarith

/-- `(E f)² ≤ E f²` on a probability space. -/
theorem sq_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  have h0 : 0 ≤ ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have e : (fun x => (f x - ∫ y, f y ∂μ) ^ 2) =
      fun x => (f x ^ 2 - (2 * ∫ y, f y ∂μ) * f x) + (∫ y, f y ∂μ) ^ 2 := by
    funext x; ring
  have hc : ∫ _x, (∫ y, f y ∂μ) ^ 2 ∂μ = (∫ y, f y ∂μ) ^ 2 := by simp
  have i1 : Integrable (fun x => f x ^ 2 - (2 * ∫ y, f y ∂μ) * f x) μ := hf2.sub (hf.const_mul _)
  rw [e, integral_add i1 (integrable_const _),
    integral_sub hf2 (hf.const_mul _), integral_const_mul, hc] at h0
  nlinarith [h0]

/-! ## The final error statement -/

theorem rpow_neg_ten (n : ℕ) : (n : ℝ) ^ (-10 : ℝ) = 1 / (n : ℝ) ^ 10 := by
  rw [rpow_neg (Nat.cast_nonneg _), show (10:ℝ) = ((10:ℕ):ℝ) by norm_num, rpow_natCast,
    one_div]

/-- **O2.** The error of the odd arithmetic rule (with its two clips) against the exact
moments. -/
theorem odd_rule_err {n : ℕ} (hn : 8001 ≤ n) (ho : Odd n) (m : ℝ) {k a : ℝ} (hk : 0 ≤ k)
    (hm : |m| ≤ a) (hka : k ≤ a) :
    |sphAodd n m k - sphAoddRef n m k| ≤ 1 / 10 ^ 90 * (n : ℝ) ^ (-10 : ℝ) * a ∧
    |sphEodd n m k - sphEoddRef n m k| ≤ 3 / 10 ^ 90 * (n : ℝ) ^ (-10 : ℝ) * a ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hn9 : 9 ≤ n := by omega
  have ha : 0 ≤ a := (abs_nonneg m).trans hm
  have hq := neps_small hn1
  have hn10 : (1:ℝ) ≤ (n:ℝ) ^ 10 := one_le_pow₀ (by exact_mod_cast hn1)
  have hq0 : 0 ≤ (n : ℝ) * eps0 n := mul_nonneg (Nat.cast_nonneg _) (eps0_pos hn1).le
  have hq1 : (n : ℝ) * eps0 n ≤ 1 / 10 ^ 110 := by
    nlinarith [mul_le_mul_of_nonneg_left hn10 hq0]
  rw [rpow_neg_ten]
  have hA5 : 5 * (n : ℝ) * eps0 n ≤ 1 / 10 ^ 90 * (1 / (n : ℝ) ^ 10) := by
    rw [show 1 / 10 ^ 90 * (1 / (n : ℝ) ^ 10) = (1 / 10 ^ 90) / (n : ℝ) ^ 10 by ring,
      le_div_iff₀ (by linarith)]
    nlinarith
  have hE34 : 34 * (n : ℝ) * eps0 n ≤ 3 / 10 ^ 90 * (1 / (n : ℝ) ^ 10) := by
    rw [show 3 / 10 ^ 90 * (1 / (n : ℝ) ^ 10) = (3 / 10 ^ 90) / (n : ℝ) ^ 10 by ring,
      le_div_iff₀ (by linarith)]
    nlinarith
  have hR1 : 0 ≤ 1 / 10 ^ 90 * (1 / (n : ℝ) ^ 10) * a := mul_nonneg (by positivity) ha
  have hR2 : 0 ≤ 3 / 10 ^ 90 * (1 / (n : ℝ) ^ 10) * a ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg a)
  -- the exact moments in the middle branch
  have hmid : ∀ (h0 : ¬ k = 0) (h1 : ¬ k ≤ m) (h2 : ¬ m ≤ -k),
      0 ≤ oddARef n m k ∧ oddARef n m k ≤ 2 * a ∧ oddARef n m k ^ 2 ≤ oddERef n m k := by
    intro h0 h1 h2
    have hA := sphAoddRef_eq hn9 ho m hk
    have hE := sphEoddRef_eq hn9 ho m hk
    rw [sphAoddRef, if_neg h0, if_neg h1, if_neg h2] at hA
    rw [sphEoddRef, if_neg h0, if_neg h1, if_neg h2] at hE
    rw [← hA, ← hE]
    have hTm : ∀ v : Fin (n-1) → ℝ, unitF53 v ⟨0, by omega⟩ ∈ Icc (-1:ℝ) 1 :=
      fun v => BstLean.Part272.coord_mem v _
    have hI : Integrable (fun v => relu (m + k * unitF53 v ⟨0, by omega⟩))
        (stdGauss (Fin (n-1))) :=
      integrable_coord_comp _ (g := fun z => relu (m + k * z))
        (measurable_relu.comp (measurable_const.add (measurable_const.mul measurable_id)))
        (relu_bound m k hk)
    have hI2 : Integrable (fun v => relu (m + k * unitF53 v ⟨0, by omega⟩) ^ 2)
        (stdGauss (Fin (n-1))) :=
      integrable_coord_comp _ (g := fun z => relu (m + k * z) ^ 2)
        ((measurable_relu.comp (measurable_const.add (measurable_const.mul measurable_id))).pow_const 2)
        (relu_sq_bound m k hk)
    refine ⟨integral_nonneg fun v => le_max_left _ _, ?_, sq_integral_le hI hI2⟩
    have hle : ∀ v : Fin (n-1) → ℝ, relu (m + k * unitF53 v ⟨0, by omega⟩) ≤ 2 * a := by
      intro v
      unfold relu
      apply max_le (by linarith)
      have : k * unitF53 v ⟨0, by omega⟩ ≤ k := by nlinarith [(hTm v).2]
      linarith [le_abs_self m]
    calc ∫ v, relu (m + k * unitF53 v ⟨0, by omega⟩) ∂stdGauss (Fin (n-1))
        ≤ ∫ _v : Fin (n-1) → ℝ, 2 * a ∂stdGauss (Fin (n-1)) :=
          integral_mono hI (integrable_const _) hle
      _ = 2 * a := by simp
  constructor
  · unfold sphAodd sphAoddRef
    split_ifs with h0 h1 h2
    · rw [sub_self, abs_zero]; exact hR1
    · rw [sub_self, abs_zero]; exact hR1
    · rw [sub_self, abs_zero]; exact hR1
    · have hkp : 0 < k := lt_of_le_of_ne hk (Ne.symm h0)
      obtain ⟨hy0, _, _⟩ := hmid h0 h1 h2
      have h := oddA_err hn9 hkp (lt_of_not_ge h2) (lt_of_not_ge h1) hm hka
      refine (clip0 hy0).trans (h.trans ?_)
      exact mul_le_mul_of_nonneg_right hA5 ha
  · unfold sphEodd sphEoddRef
    split_ifs with h0 h1 h2
    · rw [sub_self, abs_zero]; exact hR2
    · rw [sub_self, abs_zero]; exact hR2
    · rw [sub_self, abs_zero]; exact hR2
    · have hkp : 0 < k := lt_of_le_of_ne hk (Ne.symm h0)
      obtain ⟨hy0, hy2a, hjen⟩ := hmid h0 h1 h2
      have hA := oddA_err hn9 hkp (lt_of_not_ge h2) (lt_of_not_ge h1) hm hka
      have hE := oddE_err hn9 hkp (lt_of_not_ge h2) (lt_of_not_ge h1) hm hka
      have hc := clipE hjen hy0 hy2a (le_max_left 0 (oddA n m k)) ((clip0 hy0).trans hA) hE
      refine hc.trans ?_
      have hδ : 5 * (n:ℝ) * eps0 n * a ≤ a / 10 := by
        nlinarith [mul_le_mul_of_nonneg_right hq1 ha]
      have hδ0 : 0 ≤ 5 * (n:ℝ) * eps0 n * a := by
        have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 5) hq0) ha
        linarith
      calc 13 * (n:ℝ) * eps0 n * a ^ 2 + 5 * n * eps0 n * a * (2 * (2 * a) + 5 * n * eps0 n * a)
          ≤ 13 * (n:ℝ) * eps0 n * a ^ 2 + 5 * n * eps0 n * a * (2 * (2 * a) + a / 10) := by
            have := mul_le_mul_of_nonneg_left (add_le_add_left hδ (2 * (2 * a))) hδ0
            linarith
        _ ≤ 34 * (n:ℝ) * eps0 n * a ^ 2 := by nlinarith [mul_nonneg hq0 (sq_nonneg a)]
        _ ≤ 3 / 10 ^ 90 * (1 / (n : ℝ) ^ 10) * a ^ 2 :=
            mul_le_mul_of_nonneg_right hE34 (sq_nonneg a)

end BstLean.Part278
