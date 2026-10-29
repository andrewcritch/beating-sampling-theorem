import BstLean.Part90Kernel
import BstLean.Part90Lin
import BstLean.Part90Mink

/-!
# Part 90: slice moments of the anchor features and of the residual kernel (`SliceMom`)

`sliceMom : SliceMom m (397/100) (27/5) (19/50)` for `m ≥ 10⁶`.

On the slice `x = S v + R w` (`w = perpDir v g`, `v·w = 0`, `|w| = 1` a.e.), with
`k₂ = (1 + p₄)/2`, `k₃ = (1 + 3p₄ + 2p₆)/6`, `c_j = 1/√k_j`, `β₂ = S² k₂ c₂`, `β₃ = S³ k₃ c₃`:
`b_j − β_j = c_j E_j`, and `|c₂E₂| + |c₃E₃| ≤ |R u₂·w| + |R u₃·w| + (26/5) Q` (`b_pt`), with
`‖u₂‖ ≤ 1`, `‖u₃‖ ≤ 2`, `Q = Σ v_i² (R w_i)²`. For the kernel, the terms linear in `w` cancel to
`2 S³ R³ (v³·w)` and `|τ − k̄| ≤ |R u_K·w| + 22 Q + (13/3) Σ (R w_i)⁴ + (|c₂E₂| + |c₃E₃|)²`
(`tau_pt`). The moments come from `sliceLin_moment` (also for the coordinates, `u = e_i`), Jensen
with the weights `v_i²` or `w_i²`, and Minkowski (`mink2`).
-/

namespace BstLean.Part90

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part56 (UnitV kJ tauR polarPoint perpDir axialR axialS)
open BstLean.Part78 (nsq)

noncomputable section

namespace MomAux

section pt
variable {n : ℕ} (v w : Fin n → ℝ) (S R : ℝ)

def p4 : ℝ := ∑ i, v i ^ 4
def p6 : ℝ := ∑ i, v i ^ 6
def s3 : ℝ := ∑ i, v i ^ 3 * w i
def s5 : ℝ := ∑ i, v i ^ 5 * w i
def q2 : ℝ := ∑ i, v i ^ 2 * w i ^ 2
def q4 : ℝ := ∑ i, v i ^ 4 * w i ^ 2
def q3 : ℝ := ∑ i, v i ^ 3 * w i ^ 3
def kk2 : ℝ := (1 + p4 v) / 2
def kk3 : ℝ := (1 + 3 * p4 v + 2 * p6 v) / 6
noncomputable def c2 : ℝ := 1 / Real.sqrt (kk2 v)
noncomputable def c3 : ℝ := 1 / Real.sqrt (kk3 v)
def E2 : ℝ := S * R * s3 v w + R ^ 2 / 2 * q2 v w
def E3 : ℝ := S ^ 2 * R * (s3 v w + s5 v w) + S * R ^ 2 / 2 * q2 v w + S * R ^ 2 * q4 v w +
  R ^ 3 / 3 * q3 v w
def QQ : ℝ := ∑ i, v i ^ 2 * (R * w i) ^ 2
def TT : ℝ := ∑ i, (R * w i) ^ 4

variable {v w}

lemma v_sq_le (hv : UnitV v) (i : Fin n) : v i ^ 2 ≤ 1 := by
  have h : ∑ i, v i ^ 2 = 1 := hv
  rw [← h]
  exact Finset.single_le_sum (f := fun i => v i ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

lemma p4_nonneg : 0 ≤ p4 v := Finset.sum_nonneg fun i _ => by positivity
lemma p6_nonneg : 0 ≤ p6 v := Finset.sum_nonneg fun i _ => by positivity

lemma p4_le (hv : UnitV v) : p4 v ≤ 1 := by
  have h : ∑ i, v i ^ 2 = 1 := hv
  rw [← h]
  refine Finset.sum_le_sum fun i _ => ?_
  nlinarith [v_sq_le hv i, sq_nonneg (v i)]

lemma p6_le (hv : UnitV v) : p6 v ≤ p4 v := by
  refine Finset.sum_le_sum fun i _ => ?_
  nlinarith [v_sq_le hv i, sq_nonneg (v i), sq_nonneg (v i ^ 2)]

lemma kk2_bd (hv : UnitV v) : 1 / 2 ≤ kk2 v ∧ kk2 v ≤ 1 := by
  have := p4_nonneg (v := v); have := p4_le hv
  unfold kk2; constructor <;> linarith

lemma kk3_bd (hv : UnitV v) : 1 / 6 ≤ kk3 v ∧ kk3 v ≤ 1 := by
  have := p4_nonneg (v := v); have := p4_le hv; have := p6_le hv
  have := p6_nonneg (v := v)
  unfold kk3; constructor <;> linarith

lemma c_facts (k : ℝ) (hk : 0 < k) :
    0 < 1 / Real.sqrt k ∧ (1 / Real.sqrt k) ^ 2 * k = 1 := by
  have hs := Real.sqrt_pos.mpr hk
  refine ⟨by positivity, ?_⟩
  rw [div_pow, one_pow, Real.sq_sqrt hk.le]
  field_simp

lemma c2_facts (hv : UnitV v) : 0 < c2 v ∧ c2 v ^ 2 * kk2 v = 1 :=
  c_facts _ (by have := (kk2_bd hv).1; linarith)

lemma c3_facts (hv : UnitV v) : 0 < c3 v ∧ c3 v ^ 2 * kk3 v = 1 :=
  c_facts _ (by have := (kk3_bd hv).1; linarith)

lemma dot_x (hv : UnitV v) (hvw : ∑ i, v i * w i = 0) :
    ∑ i, (S • v + R • w) i * v i = S := by
  have h : ∑ i, v i ^ 2 = 1 := hv
  have e : ∀ i, (S • v + R • w) i * v i = S * v i ^ 2 + R * (v i * w i) := by
    intro i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, h, hvw]; ring

lemma kvv2 (hv : UnitV v) : kJ 3 2 v v = kk2 v := by
  have h : ∑ i, v i ^ 2 = 1 := hv
  have h' : ∑ i, v i * v i = 1 := by simpa [sq] using h
  have e : ∑ i, (v i * v i) ^ 2 = p4 v := Finset.sum_congr rfl fun i _ => by ring
  rw [((closedForms n).1 v v).2.2.1, h', e]; unfold kk2; ring

lemma kvv3 (hv : UnitV v) : kJ 3 3 v v = kk3 v := by
  have h : ∑ i, v i ^ 2 = 1 := hv
  have h' : ∑ i, v i * v i = 1 := by simpa [sq] using h
  have e : ∑ i, (v i * v i) ^ 2 = p4 v := Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, (v i * v i) ^ 3 = p6 v := Finset.sum_congr rfl fun i _ => by ring
  rw [((closedForms n).1 v v).2.2.2, h', e, e3]; unfold kk3; ring

lemma P2x : ∑ i, ((S • v + R • w) i * v i) ^ 2 =
    S ^ 2 * p4 v + 2 * S * R * s3 v w + R ^ 2 * q2 v w := by
  simp only [p4, s3, q2, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma P3x : ∑ i, ((S • v + R • w) i * v i) ^ 3 =
    S ^ 3 * p6 v + 3 * S ^ 2 * R * s5 v w + 3 * S * R ^ 2 * q4 v w + R ^ 3 * q3 v w := by
  simp only [p6, s5, q4, q3, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma kx2 (hv : UnitV v) (hvw : ∑ i, v i * w i = 0) :
    kJ 3 2 (S • v + R • w) v = S ^ 2 * kk2 v + E2 v w S R := by
  rw [((closedForms n).1 _ v).2.2.1, dot_x S R hv hvw, P2x]; unfold kk2 E2; ring

lemma kx3 (hv : UnitV v) (hvw : ∑ i, v i * w i = 0) :
    kJ 3 3 (S • v + R • w) v = S ^ 3 * kk3 v + E3 v w S R := by
  rw [((closedForms n).1 _ v).2.2.2, dot_x S R hv hvw, P2x, P3x]; unfold kk3 E3; ring

lemma b1x (hv : UnitV v) (hvw : ∑ i, v i * w i = 0) : bF v 1 (S • v + R • w) = S := by
  have h : ∑ i, v i ^ 2 = 1 := hv
  have h' : ∑ i, v i * v i = 1 := by simpa [sq] using h
  unfold bF
  rw [((closedForms n).1 _ v).2.1, ((closedForms n).1 v v).2.1, dot_x S R hv hvw, h']; simp

lemma b2x (hv : UnitV v) (hvw : ∑ i, v i * w i = 0) :
    bF v 2 (S • v + R • w) = S ^ 2 * (kk2 v * c2 v) + c2 v * E2 v w S R := by
  unfold bF; rw [kx2 S R hv hvw, kvv2 hv]; unfold c2; ring

lemma b3x (hv : UnitV v) (hvw : ∑ i, v i * w i = 0) :
    bF v 3 (S • v + R • w) = S ^ 3 * (kk3 v * c3 v) + c3 v * E3 v w S R := by
  unfold bF; rw [kx3 S R hv hvw, kvv3 hv]; unfold c3; ring

def U2 (v : Fin n → ℝ) (S : ℝ) : Fin n → ℝ := fun i => c2 v * S * v i ^ 3
def U3 (v : Fin n → ℝ) (S : ℝ) : Fin n → ℝ := fun i => c3 v * S ^ 2 * (v i ^ 3 + v i ^ 5)
def UK (v : Fin n → ℝ) (S R : ℝ) : Fin n → ℝ := fun i => 2 * S ^ 3 * R ^ 2 * v i ^ 3
def XL (u w : Fin n → ℝ) (R : ℝ) : ℝ := R * ∑ i, u i * w i

def rho (s a y : ℝ) : ℝ := (5 * s ^ 2 - s ^ 4) * a ^ 2 * y ^ 2 + 3 * s ^ 4 * a ^ 4 * y ^ 2 +
  4 * s * a * y ^ 3 + 6 * s ^ 3 * a ^ 3 * y ^ 3 + y ^ 4 + 5 * s ^ 2 * a ^ 2 * y ^ 4 +
  2 * s * a * y ^ 5 + y ^ 6 / 3

lemma rho_bd (s a y : ℝ) (hs : s ^ 2 ≤ 1) (ha : a ^ 2 ≤ 1) (hy : y ^ 2 ≤ 1) :
    |rho s a y| ≤ 22 * (a ^ 2 * y ^ 2) + 13 / 3 * y ^ 4 := by
  have hay : 0 ≤ a ^ 2 * y ^ 2 := by positivity
  have hy4 : 0 ≤ y ^ 4 := by positivity
  have hs4 : s ^ 4 ≤ 1 := by nlinarith [sq_nonneg s]
  have ha4 : a ^ 4 ≤ a ^ 2 := by nlinarith [sq_nonneg a]
  have hy4' : y ^ 4 ≤ y ^ 2 := by nlinarith [sq_nonneg y]
  have hy6 : y ^ 6 ≤ y ^ 4 := by nlinarith [sq_nonneg y, sq_nonneg (y ^ 2)]
  have hP : |s * a * y| ≤ (a ^ 2 + y ^ 2) / 2 := by
    rw [abs_mul, abs_mul]
    have h1 : |s| ≤ 1 := by
      rw [← abs_one]; exact sq_le_sq.mp (by simpa using hs)
    have h2 : |a| * |y| ≤ (a ^ 2 + y ^ 2) / 2 := by
      nlinarith [sq_nonneg (|a| - |y|), sq_abs a, sq_abs y]
    have h3 : 0 ≤ |a| * |y| := by positivity
    calc |s| * |a| * |y| = |s| * (|a| * |y|) := by ring
      _ ≤ 1 * (|a| * |y|) := mul_le_mul_of_nonneg_right h1 h3
      _ ≤ _ := by linarith
  have hP1 : |s * a * y| ≤ 1 := by linarith
  have t1 : |(5 * s ^ 2 - s ^ 4) * a ^ 2 * y ^ 2| ≤ 5 * (a ^ 2 * y ^ 2) := by
    have h0 : 0 ≤ 5 * s ^ 2 - s ^ 4 := by nlinarith [sq_nonneg s]
    have h5 : 5 * s ^ 2 - s ^ 4 ≤ 5 := by nlinarith [sq_nonneg s, sq_nonneg (s ^ 2)]
    rw [mul_assoc, abs_mul, abs_of_nonneg h0, abs_of_nonneg hay]
    exact mul_le_mul_of_nonneg_right h5 hay
  have t2 : |3 * s ^ 4 * a ^ 4 * y ^ 2| ≤ 3 * (a ^ 2 * y ^ 2) := by
    have h0 : 0 ≤ 3 * s ^ 4 * a ^ 4 * y ^ 2 := by positivity
    rw [abs_of_nonneg h0]
    have : s ^ 4 * (a ^ 4 * y ^ 2) ≤ 1 * (a ^ 2 * y ^ 2) :=
      mul_le_mul hs4 (mul_le_mul_of_nonneg_right ha4 (sq_nonneg y)) (by positivity) (by norm_num)
    nlinarith
  have t3 : |4 * s * a * y ^ 3| ≤ 2 * (a ^ 2 * y ^ 2) + 2 * y ^ 4 := by
    have e : 4 * s * a * y ^ 3 = 4 * (s * a * y) * y ^ 2 := by ring
    rw [e, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg y), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    nlinarith [mul_le_mul_of_nonneg_right hP (sq_nonneg y)]
  have t4 : |6 * s ^ 3 * a ^ 3 * y ^ 3| ≤ 6 * (a ^ 2 * y ^ 2) := by
    have e : 6 * s ^ 3 * a ^ 3 * y ^ 3 = 6 * (s ^ 2 * (s * a * y)) * (a ^ 2 * y ^ 2) := by ring
    rw [e, abs_mul, abs_mul, abs_mul, abs_of_nonneg hay, abs_of_nonneg (sq_nonneg s),
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6)]
    have : s ^ 2 * |s * a * y| ≤ 1 * 1 := mul_le_mul hs hP1 (abs_nonneg _) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right this hay]
  have t6 : |5 * s ^ 2 * a ^ 2 * y ^ 4| ≤ 5 * (a ^ 2 * y ^ 2) := by
    have h0 : 0 ≤ 5 * s ^ 2 * a ^ 2 * y ^ 4 := by positivity
    rw [abs_of_nonneg h0]
    have : s ^ 2 * (a ^ 2 * y ^ 4) ≤ 1 * (a ^ 2 * y ^ 2) :=
      mul_le_mul hs (mul_le_mul_of_nonneg_left hy4' (sq_nonneg a)) (by positivity) (by norm_num)
    nlinarith
  have t7 : |2 * s * a * y ^ 5| ≤ a ^ 2 * y ^ 2 + y ^ 4 := by
    have e : 2 * s * a * y ^ 5 = 2 * (s * a * y) * y ^ 4 := by ring
    rw [e, abs_mul, abs_mul, abs_of_nonneg hy4, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have h1 := mul_le_mul_of_nonneg_right hP hy4
    have h2 : a ^ 2 * y ^ 4 ≤ a ^ 2 * y ^ 2 := mul_le_mul_of_nonneg_left hy4' (sq_nonneg a)
    have h3 : y ^ 2 * y ^ 4 ≤ 1 * y ^ 4 := mul_le_mul_of_nonneg_right hy hy4
    nlinarith
  have t5 : |y ^ 4| ≤ y ^ 4 := by rw [abs_of_nonneg hy4]
  have t8 : |y ^ 6 / 3| ≤ y ^ 4 / 3 := by
    rw [abs_of_nonneg (by positivity)]; linarith
  unfold rho
  have := abs_add_le ((5 * s ^ 2 - s ^ 4) * a ^ 2 * y ^ 2 + 3 * s ^ 4 * a ^ 4 * y ^ 2 +
    4 * s * a * y ^ 3 + 6 * s ^ 3 * a ^ 3 * y ^ 3 + y ^ 4 + 5 * s ^ 2 * a ^ 2 * y ^ 4 +
    2 * s * a * y ^ 5) (y ^ 6 / 3)
  have := abs_add_le ((5 * s ^ 2 - s ^ 4) * a ^ 2 * y ^ 2 + 3 * s ^ 4 * a ^ 4 * y ^ 2 +
    4 * s * a * y ^ 3 + 6 * s ^ 3 * a ^ 3 * y ^ 3 + y ^ 4 + 5 * s ^ 2 * a ^ 2 * y ^ 4)
    (2 * s * a * y ^ 5)
  have := abs_add_le ((5 * s ^ 2 - s ^ 4) * a ^ 2 * y ^ 2 + 3 * s ^ 4 * a ^ 4 * y ^ 2 +
    4 * s * a * y ^ 3 + 6 * s ^ 3 * a ^ 3 * y ^ 3 + y ^ 4) (5 * s ^ 2 * a ^ 2 * y ^ 4)
  have := abs_add_le ((5 * s ^ 2 - s ^ 4) * a ^ 2 * y ^ 2 + 3 * s ^ 4 * a ^ 4 * y ^ 2 +
    4 * s * a * y ^ 3 + 6 * s ^ 3 * a ^ 3 * y ^ 3) (y ^ 4)
  have := abs_add_le ((5 * s ^ 2 - s ^ 4) * a ^ 2 * y ^ 2 + 3 * s ^ 4 * a ^ 4 * y ^ 2 +
    4 * s * a * y ^ 3) (6 * s ^ 3 * a ^ 3 * y ^ 3)
  have := abs_add_le ((5 * s ^ 2 - s ^ 4) * a ^ 2 * y ^ 2 + 3 * s ^ 4 * a ^ 4 * y ^ 2)
    (4 * s * a * y ^ 3)
  have := abs_add_le ((5 * s ^ 2 - s ^ 4) * a ^ 2 * y ^ 2) (3 * s ^ 4 * a ^ 4 * y ^ 2)
  linarith

lemma w_sq_le (hw : ∑ i, w i ^ 2 = 1) (i : Fin n) : w i ^ 2 ≤ 1 := v_sq_le hw i

lemma Rw_sq_le (hw : ∑ i, w i ^ 2 = 1) (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (i : Fin n) :
    (R * w i) ^ 2 ≤ 1 := by
  have := w_sq_le hw i
  have h1 : R ^ 2 ≤ 1 := by nlinarith
  rw [mul_pow]; nlinarith [sq_nonneg (w i), sq_nonneg R]

lemma QQ_nonneg : 0 ≤ QQ v w R := Finset.sum_nonneg fun i _ => by positivity
lemma TT_nonneg : 0 ≤ TT w R := Finset.sum_nonneg fun i _ => by positivity

lemma sum_abs_le_QQ (f : Fin n → ℝ) (h : ∀ i, |f i| ≤ v i ^ 2 * (R * w i) ^ 2) :
    |∑ i, f i| ≤ QQ v w R :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => h i)

lemma c2_le (hv : UnitV v) : c2 v ≤ 283 / 200 := by
  obtain ⟨h0, h1⟩ := c2_facts hv
  have := (kk2_bd hv).1
  nlinarith

lemma c3_le (hv : UnitV v) : c3 v ≤ 49 / 20 := by
  obtain ⟨h0, h1⟩ := c3_facts hv
  have := (kk3_bd hv).1
  nlinarith

/-- The pointwise bound of the anchor features. -/
lemma b_pt (hv : UnitV v) (hw : ∑ i, w i ^ 2 = 1) (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (hS : S ^ 2 ≤ 1) :
    |c2 v * E2 v w S R| + |c3 v * E3 v w S R| ≤
      |XL (U2 v S) w R| + |XL (U3 v S) w R| + 26 / 5 * QQ v w R := by
  obtain ⟨h20, h21⟩ := c2_facts hv
  obtain ⟨h30, h31⟩ := c3_facts hv
  have hc2 := c2_le hv
  have hc3 := c3_le hv
  have hQ := QQ_nonneg (v := v) (w := w) (R := R)
  have hvi := v_sq_le hv
  have hyi := Rw_sq_le R hw hR0 hR1
  have hSa : |S| ≤ 1 := by rw [← abs_one]; exact sq_le_sq.mp (by simpa using hS)
  have e2 : c2 v * E2 v w S R = XL (U2 v S) w R + c2 v / 2 * QQ v w R := by
    simp only [E2, XL, U2, QQ, s3, q2, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : c3 v * E3 v w S R = XL (U3 v S) w R + c3 v * (S / 2 * QQ v w R +
      S * (∑ i, v i ^ 4 * (R * w i) ^ 2) + 1 / 3 * ∑ i, v i ^ 3 * (R * w i) ^ 3) := by
    simp only [E3, XL, U3, QQ, s3, s5, q2, q4, q3, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have a1 : |∑ i, v i ^ 4 * (R * w i) ^ 2| ≤ QQ v w R := by
    refine sum_abs_le_QQ R _ fun i => ?_
    rw [abs_of_nonneg (by positivity)]
    have : v i ^ 4 ≤ v i ^ 2 := by nlinarith [hvi i, sq_nonneg (v i)]
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have a2 : |∑ i, v i ^ 3 * (R * w i) ^ 3| ≤ QQ v w R := by
    refine sum_abs_le_QQ R _ fun i => ?_
    have e : v i ^ 3 * (R * w i) ^ 3 = (v i * (R * w i)) * (v i ^ 2 * (R * w i) ^ 2) := by ring
    rw [e, abs_mul, abs_of_nonneg (a := v i ^ 2 * (R * w i) ^ 2) (by positivity)]
    have h1 : |v i * (R * w i)| ≤ 1 := by
      rw [← abs_one]; apply sq_le_sq.mp
      rw [mul_pow, one_pow]
      have := hvi i; have := hyi i
      nlinarith [sq_nonneg (v i), sq_nonneg (R * w i)]
    nlinarith [mul_le_mul_of_nonneg_right h1 (show 0 ≤ v i ^ 2 * (R * w i) ^ 2 by positivity)]
  have b3 : |S / 2 * QQ v w R + S * (∑ i, v i ^ 4 * (R * w i) ^ 2) +
      1 / 3 * ∑ i, v i ^ 3 * (R * w i) ^ 3| ≤ 11 / 6 * QQ v w R := by
    have h1 : |S / 2 * QQ v w R| ≤ 1 / 2 * QQ v w R := by
      rw [abs_mul, abs_of_nonneg hQ, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      nlinarith
    have h2 : |S * (∑ i, v i ^ 4 * (R * w i) ^ 2)| ≤ QQ v w R := by
      rw [abs_mul]
      calc |S| * |∑ i, v i ^ 4 * (R * w i) ^ 2| ≤ 1 * QQ v w R :=
            mul_le_mul hSa a1 (abs_nonneg _) (by norm_num)
        _ = _ := by ring
    have h3 : |1 / 3 * ∑ i, v i ^ 3 * (R * w i) ^ 3| ≤ 1 / 3 * QQ v w R := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 3)]; linarith
    have := abs_add_le (S / 2 * QQ v w R + S * (∑ i, v i ^ 4 * (R * w i) ^ 2))
      (1 / 3 * ∑ i, v i ^ 3 * (R * w i) ^ 3)
    have := abs_add_le (S / 2 * QQ v w R) (S * (∑ i, v i ^ 4 * (R * w i) ^ 2))
    linarith
  rw [e2, e3]
  have g2 := abs_add_le (XL (U2 v S) w R) (c2 v / 2 * QQ v w R)
  have g3 := abs_add_le (XL (U3 v S) w R) (c3 v * (S / 2 * QQ v w R +
      S * (∑ i, v i ^ 4 * (R * w i) ^ 2) + 1 / 3 * ∑ i, v i ^ 3 * (R * w i) ^ 3))
  rw [abs_mul, abs_of_pos h30] at g3
  rw [abs_of_nonneg (by positivity : 0 ≤ c2 v / 2 * QQ v w R)] at g2
  have k3 := mul_le_mul_of_nonneg_left b3 h30.le
  nlinarith [mul_le_mul_of_nonneg_right hc2 hQ, mul_le_mul_of_nonneg_right hc3 hQ]

def kbar (v : Fin n → ℝ) (S : ℝ) : ℝ := 5 / 3 + S ^ 4 * p4 v + S ^ 6 * p6 v / 3 - S ^ 2 -
  (S ^ 2 * (kk2 v * c2 v)) ^ 2 - (S ^ 3 * (kk3 v * c3 v)) ^ 2

lemma x_sq (hv : UnitV v) (hvw : ∑ i, v i * w i = 0) (hw : ∑ i, w i ^ 2 = 1)
    (hSR : S ^ 2 + R ^ 2 = 1) : ∑ i, (S • v + R • w) i ^ 2 = 1 := by
  have h : ∑ i, v i ^ 2 = 1 := hv
  have e : ∀ i, (S • v + R • w) i ^ 2 = S ^ 2 * v i ^ 2 + 2 * S * R * (v i * w i) +
      R ^ 2 * w i ^ 2 := by
    intro i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, h, hvw, hw]; linarith

lemma x46 : ∑ i, (S • v + R • w) i ^ 4 + (∑ i, (S • v + R • w) i ^ 6) / 3 =
    S ^ 4 * p4 v + S ^ 6 * p6 v / 3 + 2 * S ^ 2 * E2 v w S R + 2 * S ^ 3 * E3 v w S R +
      2 * S ^ 3 * R * (1 - S ^ 2) * s3 v w + ∑ i, rho S (v i) (R * w i) := by
  simp only [p4, p6, E2, E3, s3, s5, q2, q4, q3, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rho]; ring

/-- The pointwise bound of the residual kernel. -/
lemma tau_pt (hv : UnitV v) (hvw : ∑ i, v i * w i = 0) (hw : ∑ i, w i ^ 2 = 1)
    (hSR : S ^ 2 + R ^ 2 = 1) (hR0 : 0 ≤ R) :
    |tauR 3 v (S • v + R • w) - kbar v S| ≤
      |XL (UK v S R) w R| + 22 * QQ v w R + 13 / 3 * TT w R +
        (|c2 v * E2 v w S R| + |c3 v * E3 v w S R|) ^ 2 := by
  obtain ⟨h20, h21⟩ := c2_facts hv
  obtain ⟨h30, h31⟩ := c3_facts hv
  have hS : S ^ 2 ≤ 1 := by nlinarith [sq_nonneg R]
  have hR1 : R ≤ 1 := by nlinarith [sq_nonneg S]
  have eL : XL (UK v S R) w R = 2 * S ^ 3 * R * (1 - S ^ 2) * s3 v w := by
    have : 1 - S ^ 2 = R ^ 2 := by linarith
    rw [this]
    simp only [XL, UK, s3, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have eT : tauR 3 v (S • v + R • w) - kbar v S =
      XL (UK v S R) w R + ∑ i, rho S (v i) (R * w i) -
        ((c2 v * E2 v w S R) ^ 2 + (c3 v * E3 v w S R) ^ 2) := by
    rw [(closedForms n).2 v hv _ (x_sq S R hv hvw hw hSR), b1x S R hv hvw, b2x S R hv hvw,
      b3x S R hv hvw, eL]
    have := x46 (v := v) (w := w) S R
    unfold kbar
    linear_combination this + (-2 * S ^ 2 * E2 v w S R) * h21 +
      (-2 * S ^ 3 * E3 v w S R) * h31
  have hrho : |∑ i, rho S (v i) (R * w i)| ≤ 22 * QQ v w R + 13 / 3 * TT w R := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simp only [QQ, TT, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ =>
      rho_bd S (v i) (R * w i) hS (v_sq_le hv i) (Rw_sq_le R hw hR0 hR1 i)
  have hsq : (c2 v * E2 v w S R) ^ 2 + (c3 v * E3 v w S R) ^ 2 ≤
      (|c2 v * E2 v w S R| + |c3 v * E3 v w S R|) ^ 2 := by
    nlinarith [abs_nonneg (c2 v * E2 v w S R), abs_nonneg (c3 v * E3 v w S R),
      sq_abs (c2 v * E2 v w S R), sq_abs (c3 v * E3 v w S R)]
  have hsq0 : 0 ≤ (c2 v * E2 v w S R) ^ 2 + (c3 v * E3 v w S R) ^ 2 := by positivity
  rw [eT]
  have g1 := abs_sub (XL (UK v S R) w R + ∑ i, rho S (v i) (R * w i))
    ((c2 v * E2 v w S R) ^ 2 + (c3 v * E3 v w S R) ^ 2)
  have g2 := abs_add_le (XL (UK v S R) w R) (∑ i, rho S (v i) (R * w i))
  rw [abs_of_nonneg hsq0] at g1
  linarith

end pt
section int
variable {m : ℕ} (v : Fin (m + 1) → ℝ)

/-- `‖F(w)‖_{L^k} ≤ A` over the slice direction `w = perpDir v g`. -/
def LB (k : ℕ) (F : (Fin (m + 1) → ℝ) → ℝ) (A : ℝ) : Prop :=
  ∫ g, F (perpDir v g) ^ k ∂stdGauss (Fin (m + 1)) ≤ A ^ k

variable {v}

lemma int_c {F : (Fin (m + 1) → ℝ) → ℝ} (hF : Continuous F) :
    Integrable (fun g => F (perpDir v g)) (stdGauss (Fin (m + 1))) :=
  BstLean.Part56.integrable_cont_perpDir56 v F hF

lemma LB_add {k : ℕ} (hk : 1 ≤ k) {F G : (Fin (m + 1) → ℝ) → ℝ} (hF : Continuous F)
    (hG : Continuous G) (hF0 : ∀ w, 0 ≤ F w) (hG0 : ∀ w, 0 ≤ G w) {A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (h1 : LB v k F A) (h2 : LB v k G B) :
    LB v k (fun w => F w + G w) (A + B) :=
  (mink2 k hk (fun g => F (perpDir v g)) (fun g => G (perpDir v g)) (fun _ => hF0 _)
    (fun _ => hG0 _)
    (hF.measurable.comp (BstLean.Part56.measurable_perpDir56 v)).aestronglyMeasurable
    (hG.measurable.comp (BstLean.Part56.measurable_perpDir56 v)).aestronglyMeasurable
    (int_c (F := fun w => F w ^ k) (hF.pow k)) (int_c (F := fun w => G w ^ k) (hG.pow k))
    A B hA hB h1 h2).2

lemma LB_mono {k : ℕ} {F G : (Fin (m + 1) → ℝ) → ℝ} (hF : Continuous F) (hG : Continuous G)
    (hG0 : ∀ w, 0 ≤ G w) (hm : 1 ≤ m) (hv : UnitV v)
    (hle : ∀ w, ∑ i, w i ^ 2 = 1 → ∑ i, v i * w i = 0 → G w ≤ F w) {A : ℝ}
    (h : LB v k F A) : LB v k G A := by
  refine le_trans (integral_mono_ae (int_c (F := fun w => G w ^ k) (hG.pow k))
    (int_c (F := fun w => F w ^ k) (hF.pow k)) ?_) h
  filter_upwards [BstLean.Part89.perp_unit hm v hv] with g hg
  exact pow_le_pow_left₀ (hG0 _) (hle _ hg (BstLean.Part56.perpDir_orth56 v g hv)) k

lemma LB_smul {k : ℕ} {F : (Fin (m + 1) → ℝ) → ℝ} {A : ℝ} (c : ℝ) (hc : 0 ≤ c)
    (h : LB v k F A) : LB v k (fun w => c * F w) (c * A) := by
  unfold LB at *
  simp only [mul_pow]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left h (pow_nonneg hc k)

lemma LB_weaken {k : ℕ} {F : (Fin (m + 1) → ℝ) → ℝ} {A B : ℝ} (h : LB v k F A) (hA : 0 ≤ A)
    (hAB : A ≤ B) : LB v k F B := le_trans h (pow_le_pow_left₀ hA hAB k)

lemma lin_atom (hm : 1 ≤ m) (hv : UnitV v) (a r : ℝ) (u : Fin (m + 1) → ℝ) (p : ℕ)
    (hp : 1 ≤ p) :
    ∫ g, XL u (perpDir v g) (axialR a r) ^ (2 * p) ∂stdGauss (Fin (m + 1)) ≤
      ((2 * p - 1).doubleFactorial : ℝ) * axialR a r ^ (2 * p) * nsq u ^ p / (m : ℝ) ^ p := by
  have h := sliceLin_moment m hm v hv a r u p hp
  have e : ∀ g : Fin (m + 1) → ℝ, (∑ i, u i * (polarPoint v (perpDir v g) a r i -
        (∑ l, v l * polarPoint v (perpDir v g) a r l) * v i)) =
      XL u (perpDir v g) (axialR a r) := fun g =>
    lin_slice v hv _ (BstLean.Part56.perpDir_orth56 v g hv) a r u
  simp only [e] at h
  exact h

lemma nsq_nonneg' (u : Fin (m + 1) → ℝ) : 0 ≤ nsq u := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma LB_lin (hm : 1 ≤ m) (hv : UnitV v) (a r : ℝ) (u : Fin (m + 1) → ℝ) (p k : ℕ)
    (hp : 1 ≤ p) (hk : k = 2 * p) (q N rm : ℝ) (hrm : 0 < rm) (hrm2 : rm ^ 2 = m)
    (hqq : ((2 * p - 1).doubleFactorial : ℝ) ≤ q ^ k) (hu : nsq u ≤ N ^ 2) :
    LB v k (fun w => |XL u w (axialR a r)|) (q * axialR a r * N / rm) := by
  subst hk
  unfold LB
  have e : ∀ g : Fin (m + 1) → ℝ, |XL u (perpDir v g) (axialR a r)| ^ (2 * p) =
      XL u (perpDir v g) (axialR a r) ^ (2 * p) := fun g => Even.pow_abs (even_two_mul p) _
  simp only [e]
  refine (lin_atom hm hv a r u p hp).trans ?_
  have h1 : nsq u ^ p ≤ N ^ (2 * p) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (nsq_nonneg' u) hu p
  have hR : 0 ≤ axialR a r ^ (2 * p) := by rw [pow_mul]; positivity
  have hm0 : (0 : ℝ) < (m : ℝ) ^ p := by rw [← hrm2]; positivity
  rw [div_pow, mul_pow, mul_pow, pow_mul rm, hrm2]
  apply div_le_div_of_nonneg_right _ hm0.le
  have hd : (0 : ℝ) ≤ ((2 * p - 1).doubleFactorial : ℝ) := by positivity
  calc ((2 * p - 1).doubleFactorial : ℝ) * axialR a r ^ (2 * p) * nsq u ^ p
      ≤ q ^ (2 * p) * axialR a r ^ (2 * p) * N ^ (2 * p) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hqq hR) h1 (pow_nonneg (nsq_nonneg' u) p)
          (mul_nonneg (hd.trans hqq) hR)
    _ = _ := by ring

lemma XL_single (i : Fin (m + 1)) (w : Fin (m + 1) → ℝ) (R : ℝ) :
    XL (Pi.single i 1) w R = R * w i := by
  simp [XL, Pi.single_apply]

lemma nsq_single (i : Fin (m + 1)) : nsq (Pi.single i (1 : ℝ)) = 1 := by
  simp [nsq, Pi.single_apply]

/-- `E (R w_i)^{2p} ≤ (2p−1)!! R^{2p}/m^p`. -/
lemma coord_atom (hm : 1 ≤ m) (hv : UnitV v) (a r : ℝ) (i : Fin (m + 1)) (p : ℕ)
    (hp : 1 ≤ p) :
    ∫ g, (axialR a r * perpDir v g i) ^ (2 * p) ∂stdGauss (Fin (m + 1)) ≤
      ((2 * p - 1).doubleFactorial : ℝ) * axialR a r ^ (2 * p) / (m : ℝ) ^ p := by
  have h := lin_atom hm hv a r (Pi.single i 1) p hp
  simp only [XL_single, nsq_single, one_pow, mul_one] at h
  exact h

lemma LB_Q (hm : 1 ≤ m) (hv : UnitV v) (a r : ℝ) (p : ℕ) (hp : 1 ≤ p) (h : ℝ)
    (hh : ((2 * p - 1).doubleFactorial : ℝ) ≤ h ^ p) :
    LB v p (fun w => QQ v w (axialR a r)) (h * axialR a r ^ 2 / m) := by
  unfold LB
  have hv1 : ∑ i, v i ^ 2 = 1 := hv
  have hpt : ∀ g : Fin (m + 1) → ℝ, QQ v (perpDir v g) (axialR a r) ^ p ≤
      ∑ i, v i ^ 2 * (axialR a r * perpDir v g i) ^ (2 * p) := by
    intro g
    have := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun i => v i ^ 2)
      (fun i => (axialR a r * perpDir v g i) ^ 2) (fun i _ => sq_nonneg _) hv1
      (fun i _ => sq_nonneg _) p
    simp only [← pow_mul] at this
    exact this
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))), Integrable (fun g : Fin (m + 1) → ℝ =>
      v i ^ 2 * (axialR a r * perpDir v g i) ^ (2 * p)) (stdGauss (Fin (m + 1))) := by
    intro i _
    exact int_c (F := fun w => v i ^ 2 * (axialR a r * w i) ^ (2 * p)) (by fun_prop)
  have hQc : Continuous fun w : Fin (m + 1) → ℝ => QQ v w (axialR a r) ^ p := by
    unfold QQ; fun_prop
  refine (integral_mono (int_c hQc) (integrable_finsetSum _ hi) hpt).trans ?_
  rw [integral_finsetSum _ hi]
  simp only [integral_const_mul]
  have hm0 : (0 : ℝ) < (m : ℝ) ^ p := by positivity
  calc ∑ i, v i ^ 2 * ∫ g, (axialR a r * perpDir v g i) ^ (2 * p) ∂stdGauss (Fin (m + 1))
      ≤ ∑ i, v i ^ 2 * (((2 * p - 1).doubleFactorial : ℝ) * axialR a r ^ (2 * p) /
          (m : ℝ) ^ p) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (coord_atom hm hv a r i p hp) (sq_nonneg _)
    _ = ((2 * p - 1).doubleFactorial : ℝ) * axialR a r ^ (2 * p) / (m : ℝ) ^ p := by
        rw [← Finset.sum_mul, hv1, one_mul]
    _ ≤ (h * axialR a r ^ 2 / m) ^ p := by
        rw [div_pow, mul_pow, ← pow_mul]
        apply div_le_div_of_nonneg_right _ hm0.le
        exact mul_le_mul_of_nonneg_right hh (by rw [pow_mul]; positivity)

lemma LB_T (hm : 945 ≤ m) (hv : UnitV v) (a r : ℝ) (hR0 : 0 ≤ axialR a r)
    (hR1 : axialR a r ≤ 1) :
    LB v 4 (fun w => axialR a r * TT w (axialR a r)) (111 / 20 / m) := by
  unfold LB
  have hm1 : 1 ≤ m := by omega
  have hmR : (945 : ℝ) ≤ m := by exact_mod_cast hm
  have hpt : ∀ g : Fin (m + 1) → ℝ, ∑ i, perpDir v g i ^ 2 = 1 →
      (axialR a r * TT (perpDir v g) (axialR a r)) ^ 4 ≤
        ∑ i, (axialR a r * perpDir v g i) ^ (2 * 5) := by
    intro g hg
    have hJ := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun i => perpDir v g i ^ 2)
      (fun i => perpDir v g i ^ 2) (fun i _ => sq_nonneg _) hg (fun i _ => sq_nonneg _) 4
    have e1 : axialR a r * TT (perpDir v g) (axialR a r) =
        axialR a r ^ 5 * ∑ i, perpDir v g i ^ 2 * perpDir v g i ^ 2 := by
      simp only [TT, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, (axialR a r * perpDir v g i) ^ (2 * 5) =
        axialR a r ^ 10 * ∑ i, perpDir v g i ^ 2 * (perpDir v g i ^ 2) ^ 4 := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h0 : 0 ≤ ∑ i, perpDir v g i ^ 2 * (perpDir v g i ^ 2) ^ 4 :=
      Finset.sum_nonneg fun i _ => by positivity
    have hR10 : axialR a r ^ 10 ≤ 1 := pow_le_one₀ hR0 hR1
    have hR10' : 0 ≤ axialR a r ^ 10 := by positivity
    rw [e1, e2, mul_pow]
    have e3 : (axialR a r ^ 5) ^ 4 = axialR a r ^ 10 * axialR a r ^ 10 := by ring
    rw [e3]
    calc axialR a r ^ 10 * axialR a r ^ 10 *
          (∑ i, perpDir v g i ^ 2 * perpDir v g i ^ 2) ^ 4
        ≤ axialR a r ^ 10 * 1 * ∑ i, perpDir v g i ^ 2 * (perpDir v g i ^ 2) ^ 4 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hR10 hR10') hJ (by positivity) (by positivity)
      _ = _ := by ring
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))), Integrable (fun g : Fin (m + 1) → ℝ =>
      (axialR a r * perpDir v g i) ^ (2 * 5)) (stdGauss (Fin (m + 1))) := by
    intro i _
    exact int_c (F := fun w => (axialR a r * w i) ^ (2 * 5)) (by fun_prop)
  have hTc : Continuous fun w : Fin (m + 1) → ℝ => (axialR a r * TT w (axialR a r)) ^ 4 := by
    unfold TT; fun_prop
  have hae : (fun g : Fin (m + 1) → ℝ => (axialR a r * TT (perpDir v g) (axialR a r)) ^ 4)
      ≤ᵐ[stdGauss (Fin (m + 1))] fun g => ∑ i, (axialR a r * perpDir v g i) ^ (2 * 5) := by
    filter_upwards [BstLean.Part89.perp_unit hm1 v hv] with g hg
    exact hpt g hg
  refine (integral_mono_ae (int_c hTc) (integrable_finsetSum _ hi) hae).trans ?_
  rw [integral_finsetSum _ hi]
  have hm0 : (0 : ℝ) < m := by linarith
  have hd : ((2 * 5 - 1).doubleFactorial : ℝ) = 945 := by
    norm_num [Nat.doubleFactorial]
  calc ∑ i, ∫ g, (axialR a r * perpDir v g i) ^ (2 * 5) ∂stdGauss (Fin (m + 1))
      ≤ ∑ _i : Fin (m + 1), (945 : ℝ) / (m : ℝ) ^ 5 := by
        refine Finset.sum_le_sum fun i _ => (coord_atom hm1 hv a r i 5 (by norm_num)).trans ?_
        rw [hd]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : axialR a r ^ (2 * 5) ≤ 1 := pow_le_one₀ hR0 hR1
        nlinarith
    _ = ((m : ℝ) + 1) * 945 / (m : ℝ) ^ 5 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
    _ ≤ (111 / 20 / m) ^ 4 := by
        rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 : ((m : ℝ) + 1) * 945 ≤ 946 * m := by linarith
        have h2 : (0 : ℝ) ≤ (m : ℝ) ^ 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h1 h2]

/-- The two anchor features: `FB w = |b₂ − β₂| + |b₃ − β₃|` as a function of the direction. -/
def FB (v w : Fin (m + 1) → ℝ) (S R : ℝ) : ℝ := |c2 v * E2 v w S R| + |c3 v * E3 v w S R|

lemma FB_cont (S R : ℝ) : Continuous fun w : Fin (m + 1) → ℝ => FB v w S R := by
  unfold FB E2 E3 s3 s5 q2 q4 q3; fun_prop

lemma nsq_U2 (hv : UnitV v) (S : ℝ) (hS : S ^ 2 ≤ 1) : nsq (U2 v S) ≤ 1 ^ 2 := by
  obtain ⟨h0, h1⟩ := c2_facts hv
  have e : nsq (U2 v S) = c2 v ^ 2 * S ^ 2 * p6 v := by
    simp only [nsq, U2, p6, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h6 := p6_le hv; have h4 := p4_le hv; have h60 := p6_nonneg (v := v)
  have hk : p6 v ≤ kk2 v := by unfold kk2; linarith
  have hc : 0 ≤ c2 v ^ 2 := sq_nonneg _
  have : c2 v ^ 2 * p6 v ≤ 1 := by nlinarith
  rw [e]
  have h3 : 0 ≤ c2 v ^ 2 * p6 v := by positivity
  nlinarith [sq_nonneg S]

lemma nsq_U3 (hv : UnitV v) (S : ℝ) (hS : S ^ 2 ≤ 1) : nsq (U3 v S) ≤ 2 ^ 2 := by
  obtain ⟨h0, h1⟩ := c3_facts hv
  have hvi := v_sq_le hv
  have e : nsq (U3 v S) = c3 v ^ 2 * (S ^ 2) ^ 2 * ∑ i, (v i ^ 3 + v i ^ 5) ^ 2 := by
    simp only [nsq, U3, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hs : ∑ i, (v i ^ 3 + v i ^ 5) ^ 2 ≤ 4 * p6 v := by
    unfold p6; rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have e' : (v i ^ 3 + v i ^ 5) ^ 2 = v i ^ 6 * (1 + v i ^ 2) ^ 2 := by ring
    have h6 : 0 ≤ v i ^ 6 := by positivity
    have : (1 + v i ^ 2) ^ 2 ≤ 4 := by nlinarith [hvi i, sq_nonneg (v i)]
    rw [e']; nlinarith
  have hs0 : 0 ≤ ∑ i, (v i ^ 3 + v i ^ 5) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h6 := p6_le hv; have h4 := p4_le hv; have h60 := p6_nonneg (v := v)
  have hk : p6 v ≤ kk3 v := by unfold kk3; linarith
  have hc : 0 ≤ c3 v ^ 2 := sq_nonneg _
  have h3 : c3 v ^ 2 * (∑ i, (v i ^ 3 + v i ^ 5) ^ 2) ≤ 4 := by nlinarith
  have h30 : 0 ≤ c3 v ^ 2 * (∑ i, (v i ^ 3 + v i ^ 5) ^ 2) := by positivity
  have hS2 : (S ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg S]
  rw [e]
  nlinarith [sq_nonneg (S ^ 2)]

lemma nsq_UK (hv : UnitV v) (S R : ℝ) : nsq (UK v S R) ≤ (2 * R ^ 2 * |S ^ 3|) ^ 2 := by
  have e : nsq (UK v S R) = 4 * (R ^ 2) ^ 2 * (S ^ 3) ^ 2 * p6 v := by
    simp only [nsq, UK, p6, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h6 := p6_le hv; have h4 := p4_le hv
  rw [e, mul_pow, mul_pow, sq_abs]
  have : 0 ≤ 4 * (R ^ 2) ^ 2 * (S ^ 3) ^ 2 := by positivity
  nlinarith

/-- The `L^k` bound of the anchor features, `k = 2p`. -/
lemma LB_FB (hm : 1000000 ≤ m) (hv : UnitV v) (a r : ℝ) (ha : a ≠ 0) (hr : 0 ≤ r)
    (p k : ℕ) (hp : 1 ≤ p) (hk : k = 2 * p) (q h C rm : ℝ) (hrm : 1000 ≤ rm)
    (hrm2 : rm ^ 2 = m) (hq0 : 0 ≤ q) (hh0 : 0 ≤ h)
    (hq : ((2 * p - 1).doubleFactorial : ℝ) ≤ q ^ k)
    (hh : ((2 * k - 1).doubleFactorial : ℝ) ≤ h ^ k)
    (hC : 3 * q + 26 / 5 * h / 1000 ≤ C) :
    LB v k (fun w => FB v w (axialS a r) (axialR a r)) (C * axialR a r / rm) := by
  have hm1 : 1 ≤ m := by omega
  have hk1 : 1 ≤ k := by omega
  have hSR := BstLean.Part89.axial_sq_eq a r ha
  have hR0 : 0 ≤ axialR a r := by unfold axialR; exact div_nonneg hr (Real.sqrt_nonneg _)
  have hR1 : axialR a r ≤ 1 := by nlinarith [sq_nonneg (axialS a r)]
  have hS : axialS a r ^ 2 ≤ 1 := by nlinarith [sq_nonneg (axialR a r)]
  have hrm0 : 0 < rm := by linarith
  have l2 := LB_lin hm1 hv a r (U2 v (axialS a r)) p k hp hk q 1 rm hrm0 hrm2 hq
    (nsq_U2 hv _ hS)
  have l3 := LB_lin hm1 hv a r (U3 v (axialS a r)) p k hp hk q 2 rm hrm0 hrm2 hq
    (nsq_U3 hv _ hS)
  have lQ := LB_smul (26 / 5) (by norm_num) (LB_Q hm1 hv a r k hk1 h hh)
  have c2c : Continuous fun w : Fin (m + 1) → ℝ => |XL (U2 v (axialS a r)) w (axialR a r)| := by
    unfold XL; fun_prop
  have c3c : Continuous fun w : Fin (m + 1) → ℝ => |XL (U3 v (axialS a r)) w (axialR a r)| := by
    unfold XL; fun_prop
  have cQ : Continuous fun w : Fin (m + 1) → ℝ => 26 / 5 * QQ v w (axialR a r) := by
    unfold QQ; fun_prop
  have A1 : 0 ≤ q * axialR a r * 1 / rm := by positivity
  have A2 : 0 ≤ q * axialR a r * 2 / rm := by positivity
  have A3 : 0 ≤ 26 / 5 * (h * axialR a r ^ 2 / m) := by positivity
  have s1 := LB_add hk1 c2c c3c (fun _ => abs_nonneg _) (fun _ => abs_nonneg _) A1 A2 l2 l3
  have s2 := LB_add hk1 (c2c.add c3c) cQ (fun _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
    (fun _ => mul_nonneg (by norm_num) (QQ_nonneg _)) (add_nonneg A1 A2) A3 s1 lQ
  have s3 := LB_mono (c2c.add c3c |>.add cQ) (FB_cont (axialS a r) (axialR a r))
    (fun _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hm1 hv
    (fun w hw _ => b_pt (axialS a r) (axialR a r) hv hw hR0 hR1 hS) s2
  refine LB_weaken s3 (add_nonneg (add_nonneg A1 A2) A3) ?_
  -- arithmetic
  have hmr : (m : ℝ) = rm * rm := by rw [← hrm2]; ring
  have e : q * axialR a r * 1 / rm + q * axialR a r * 2 / rm +
      26 / 5 * (h * axialR a r ^ 2 / m) =
      (3 * q + 26 / 5 * h * (axialR a r / rm)) * axialR a r / rm := by
    rw [hmr]; field_simp; ring
  rw [e]
  apply div_le_div_of_nonneg_right _ hrm0.le
  apply mul_le_mul_of_nonneg_right _ hR0
  have : axialR a r / rm ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ hrm0 (by norm_num)]; nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this (show 0 ≤ 26 / 5 * h by positivity)]

/-- The dominating function of `R |τ − k̄|`. -/
def GK (v w : Fin (m + 1) → ℝ) (S R : ℝ) : ℝ :=
  R * |XL (UK v S R) w R| + 22 * R * QQ v w R + 13 / 3 * (R * TT w R) + R * FB v w S R ^ 2

lemma GK_cont (S R : ℝ) : Continuous fun w : Fin (m + 1) → ℝ => GK v w S R := by
  unfold GK FB E2 E3 s3 s5 q2 q4 q3 XL QQ TT; fun_prop

/-- `R⁴ |S|³ ≤ 0.0963` on `S² + R² = 1`. -/
lemma SR_bd (S R : ℝ) (hSR : S ^ 2 + R ^ 2 = 1) : R ^ 4 * |S ^ 3| ≤ 963 / 10000 := by
  have h0 : 0 ≤ R ^ 4 * |S ^ 3| := by positivity
  have hx0 : 0 ≤ R ^ 2 := sq_nonneg R
  have hy0 : 0 ≤ S ^ 2 := sq_nonneg S
  have h1 : (R ^ 2) ^ 2 * S ^ 2 ≤ 4 / 27 := by
    have : S ^ 2 = 1 - R ^ 2 := by linarith
    rw [this]
    nlinarith [mul_nonneg (sq_nonneg (R ^ 2 - 2 / 3)) (show 0 ≤ R ^ 2 + 1 / 3 by linarith)]
  have h2 : R ^ 2 * S ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (R ^ 2 - S ^ 2)]
  have h3 : 0 ≤ R ^ 2 * S ^ 2 := by positivity
  have h4 : (R ^ 4 * |S ^ 3|) ^ 2 ≤ 1 / 108 := by
    have e : (R ^ 4 * |S ^ 3|) ^ 2 = ((R ^ 2) ^ 2 * S ^ 2) * ((R ^ 2 * S ^ 2) * (R ^ 2 * S ^ 2)) := by
      rw [mul_pow, sq_abs]; ring
    rw [e]
    have h5 : (R ^ 2 * S ^ 2) * (R ^ 2 * S ^ 2) ≤ 1 / 4 * (1 / 4) := mul_le_mul h2 h2 h3 (by norm_num)
    calc (R ^ 2) ^ 2 * S ^ 2 * (R ^ 2 * S ^ 2 * (R ^ 2 * S ^ 2))
        ≤ 4 / 27 * (1 / 4 * (1 / 4)) := mul_le_mul h1 h5 (by positivity) (by norm_num)
      _ = 1 / 108 := by norm_num
  by_contra hc
  rw [not_le] at hc
  nlinarith

/-- The `L⁴` bound of `R |τ − k̄|`. -/
lemma LB_K (hm : 1000000 ≤ m) (hv : UnitV v) (a r : ℝ) (ha : a ≠ 0) (hr : 0 ≤ r)
    (rm : ℝ) (hrm : 1000 ≤ rm) (hrm2 : rm ^ 2 = m)
    (hB8 : LB v 8 (fun w => FB v w (axialS a r) (axialR a r)) (27 / 5 * axialR a r / rm)) :
    LB v 4 (fun w => GK v w (axialS a r) (axialR a r)) (19 / 50 / rm) := by
  have hm1 : 1 ≤ m := by omega
  have hSR := BstLean.Part89.axial_sq_eq a r ha
  have hR0 : 0 ≤ axialR a r := by unfold axialR; exact div_nonneg hr (Real.sqrt_nonneg _)
  have hR1 : axialR a r ≤ 1 := by nlinarith [sq_nonneg (axialS a r)]
  have hrm0 : 0 < rm := by linarith
  have hmr : (m : ℝ) = rm * rm := by rw [← hrm2]; ring
  have P1 := LB_smul (axialR a r) hR0 (LB_lin hm1 hv a r (UK v (axialS a r) (axialR a r)) 2 4
    (by norm_num) (by norm_num) (13161 / 10000) (2 * axialR a r ^ 2 * |axialS a r ^ 3|) rm hrm0
    hrm2 (by norm_num [Nat.doubleFactorial]) (nsq_UK hv _ _))
  have P2 := LB_smul (22 * axialR a r) (by positivity) (LB_Q hm1 hv a r 4 (by norm_num)
    (3202 / 1000) (by norm_num [Nat.doubleFactorial]))
  have P3 := LB_smul (13 / 3) (by norm_num) (LB_T (by omega) hv a r hR0 hR1)
  have P4 : LB v 4 (fun w => axialR a r * FB v w (axialS a r) (axialR a r) ^ 2)
      (axialR a r * (27 / 5 * axialR a r / rm) ^ 2) := by
    unfold LB at hB8 ⊢
    simp only [mul_pow, ← pow_mul]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hB8 (by positivity)
  have c1 : Continuous fun w : Fin (m + 1) → ℝ =>
      axialR a r * |XL (UK v (axialS a r) (axialR a r)) w (axialR a r)| := by
    unfold XL; fun_prop
  have c2' : Continuous fun w : Fin (m + 1) → ℝ => 22 * axialR a r * QQ v w (axialR a r) := by
    unfold QQ; fun_prop
  have c3' : Continuous fun w : Fin (m + 1) → ℝ => 13 / 3 * (axialR a r * TT w (axialR a r)) := by
    unfold TT; fun_prop
  have c4 : Continuous fun w : Fin (m + 1) → ℝ =>
      axialR a r * FB v w (axialS a r) (axialR a r) ^ 2 :=
    continuous_const.mul ((FB_cont _ _).pow 2)
  have n1 : ∀ w : Fin (m + 1) → ℝ,
      0 ≤ axialR a r * |XL (UK v (axialS a r) (axialR a r)) w (axialR a r)| :=
    fun _ => mul_nonneg hR0 (abs_nonneg _)
  have n2 : ∀ w : Fin (m + 1) → ℝ, 0 ≤ 22 * axialR a r * QQ v w (axialR a r) :=
    fun _ => mul_nonneg (by positivity) (QQ_nonneg _)
  have n3 : ∀ w : Fin (m + 1) → ℝ, 0 ≤ 13 / 3 * (axialR a r * TT w (axialR a r)) :=
    fun _ => mul_nonneg (by norm_num) (mul_nonneg hR0 (TT_nonneg _))
  have n4 : ∀ w : Fin (m + 1) → ℝ, 0 ≤ axialR a r * FB v w (axialS a r) (axialR a r) ^ 2 :=
    fun _ => mul_nonneg hR0 (sq_nonneg _)
  have A1 : 0 ≤ axialR a r * (13161 / 10000 * axialR a r *
      (2 * axialR a r ^ 2 * |axialS a r ^ 3|) / rm) := by positivity
  have A2 : 0 ≤ 22 * axialR a r * (3202 / 1000 * axialR a r ^ 2 / m) := by positivity
  have A3 : (0 : ℝ) ≤ 13 / 3 * (111 / 20 / m) := by positivity
  have A4 : 0 ≤ axialR a r * (27 / 5 * axialR a r / rm) ^ 2 := by positivity
  have s1 := LB_add (by norm_num) c1 c2' n1 n2 A1 A2 P1 P2
  have s2 := LB_add (by norm_num) (c1.add c2') c3' (fun w => add_nonneg (n1 w) (n2 w)) n3
    (add_nonneg A1 A2) A3 s1 P3
  have s3 := LB_add (by norm_num) ((c1.add c2').add c3')  c4
    (fun w => add_nonneg (add_nonneg (n1 w) (n2 w)) (n3 w)) n4
    (add_nonneg (add_nonneg A1 A2) A3) A4 s2 P4
  refine LB_weaken s3 (add_nonneg (add_nonneg (add_nonneg A1 A2) A3) A4) ?_
  have hSRb := SR_bd _ _ hSR
  set im : ℝ := 1 / rm with him
  have him0 : 0 < im := by positivity
  have him1 : im ≤ 1 / 1000 := by
    rw [him, div_le_div_iff₀ hrm0 (by norm_num)]; linarith
  have hR3 : axialR a r ^ 3 ≤ 1 := pow_le_one₀ hR0 hR1
  have hR30 : 0 ≤ axialR a r ^ 3 := by positivity
  have e : axialR a r * (13161 / 10000 * axialR a r *
        (2 * axialR a r ^ 2 * |axialS a r ^ 3|) / rm) +
      22 * axialR a r * (3202 / 1000 * axialR a r ^ 2 / m) + 13 / 3 * (111 / 20 / m) +
      axialR a r * (27 / 5 * axialR a r / rm) ^ 2 =
      (13161 / 5000 * (axialR a r ^ 4 * |axialS a r ^ 3|) +
        (22 * 3202 / 1000 * axialR a r ^ 3 + 13 / 3 * (111 / 20) +
          (27 / 5) ^ 2 * axialR a r ^ 3) * im) * im := by
    rw [hmr, him]; field_simp; ring
  have e' : (19 : ℝ) / 50 / rm = 19 / 50 * im := by rw [him]; ring
  rw [e, e']
  apply mul_le_mul_of_nonneg_right _ him0.le
  have hb : (22 * 3202 / 1000 * axialR a r ^ 3 + 13 / 3 * (111 / 20) +
      (27 / 5) ^ 2 * axialR a r ^ 3) ≤ 124 := by nlinarith
  have hb0 : 0 ≤ (22 * 3202 / 1000 * axialR a r ^ 3 + 13 / 3 * (111 / 20) +
      (27 / 5) ^ 2 * axialR a r ^ 3) := by positivity
  nlinarith [mul_le_mul hb him1 him0.le (by norm_num : (0:ℝ) ≤ 124)]

end int
end MomAux

open MomAux

/-- **Slice moments of the anchor features and of the residual kernel**, `m ≥ 10⁶`. -/
theorem sliceMom (m : ℕ) (hm : 1000000 ≤ m) : SliceMom m (397 / 100) (27 / 5) (19 / 50) := by
  intro v hv a r ha hr
  have hm1 : 1 ≤ m := by omega
  have hmR : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hSR := BstLean.Part89.axial_sq_eq a r ha
  have hR0 : 0 ≤ axialR a r := by unfold axialR; exact div_nonneg hr (Real.sqrt_nonneg _)
  have hR1 : axialR a r ≤ 1 := by nlinarith [sq_nonneg (axialS a r)]
  have hS : axialS a r ^ 2 ≤ 1 := by nlinarith [sq_nonneg (axialR a r)]
  obtain ⟨h20, h21⟩ := c2_facts hv
  obtain ⟨h30, h31⟩ := c3_facts hv
  -- the square root of `m`
  set rm : ℝ := Real.sqrt m with hrmd
  have hrm2 : rm ^ 2 = m := Real.sq_sqrt (by positivity)
  have hrm : 1000 ≤ rm := by
    rw [hrmd]; apply Real.le_sqrt_of_sq_le; norm_num; linarith
  have hrm0 : 0 < rm := by linarith
  have hmr : (m : ℝ) = rm * rm := by rw [← hrm2]; ring
  -- the two moment bounds of the anchor features
  have hB4 := LB_FB hm hv a r ha hr 2 4 (by norm_num) (by norm_num) (13161 / 10000)
    (3202 / 1000) (397 / 100) rm hrm hrm2 (by norm_num) (by norm_num)
    (by norm_num [Nat.doubleFactorial]) (by norm_num [Nat.doubleFactorial]) (by norm_num)
  have hB8 := LB_FB hm hv a r ha hr 4 8 (by norm_num) (by norm_num) (17892 / 10000)
    (6143 / 1000) (27 / 5) rm hrm hrm2 (by norm_num) (by norm_num)
    (by norm_num [Nat.doubleFactorial]) (by norm_num [Nat.doubleFactorial]) (by norm_num)
  have eB : ∀ g : Fin (m + 1) → ℝ,
      |bF v 2 (polarPoint v (perpDir v g) a r) - axialS a r ^ 2 * (kk2 v * c2 v)| +
        |bF v 3 (polarPoint v (perpDir v g) a r) - axialS a r ^ 3 * (kk3 v * c3 v)| =
      FB v (perpDir v g) (axialS a r) (axialR a r) := by
    intro g
    have hvw := BstLean.Part56.perpDir_orth56 v g hv
    have e : polarPoint v (perpDir v g) a r = axialS a r • v + axialR a r • perpDir v g := rfl
    rw [e, b2x _ _ hv hvw, b3x _ _ hv hvw, add_sub_cancel_left, add_sub_cancel_left]
    rfl
  have hk2 := kk2_bd hv
  have hk3 := kk3_bd hv
  have t2 : 0 ≤ kk2 v * c2 v ∧ kk2 v * c2 v ≤ 1 := by
    have h0 : 0 ≤ kk2 v * c2 v := mul_nonneg (by linarith [hk2.1]) h20.le
    have : (kk2 v * c2 v) ^ 2 ≤ 1 := by
      have : (kk2 v * c2 v) ^ 2 = kk2 v * (c2 v ^ 2 * kk2 v) := by ring
      rw [this, h21]; linarith [hk2.2]
    exact ⟨h0, by nlinarith⟩
  have t3 : 0 ≤ kk3 v * c3 v ∧ kk3 v * c3 v ≤ 1 := by
    have h0 : 0 ≤ kk3 v * c3 v := mul_nonneg (by linarith [hk3.1]) h30.le
    have : (kk3 v * c3 v) ^ 2 ≤ 1 := by
      have : (kk3 v * c3 v) ^ 2 = kk3 v * (c3 v ^ 2 * kk3 v) := by ring
      rw [this, h31]; linarith [hk3.2]
    exact ⟨h0, by nlinarith⟩
  have hSa : |axialS a r| ≤ 1 := by rw [← abs_one]; exact sq_le_sq.mp (by simpa using hS)
  refine ⟨axialS a r ^ 2 * (kk2 v * c2 v), axialS a r ^ 3 * (kk3 v * c3 v),
    kbar v (axialS a r), ?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_mul, abs_pow, abs_of_nonneg t2.1]
    have : |axialS a r| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) hSa
    nlinarith [t2.1, t2.2, sq_nonneg |axialS a r|]
  · rw [abs_mul, abs_pow, abs_of_nonneg t3.1]
    have : |axialS a r| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hSa
    have : 0 ≤ |axialS a r| ^ 3 := by positivity
    nlinarith [t3.1, t3.2]
  · simp only [eB]
    refine le_trans hB4 (le_of_eq ?_)
    rw [div_pow, hmr]; ring
  · simp only [eB]
    refine le_trans hB8 (le_of_eq ?_)
    rw [div_pow, hmr]; ring
  · have hK := LB_K hm hv a r ha hr rm hrm hrm2 hB8
    rw [← integral_const_mul]
    have hae : (fun g : Fin (m + 1) → ℝ => axialR a r ^ 4 *
        (tauR 3 v (polarPoint v (perpDir v g) a r) - kbar v (axialS a r)) ^ 4)
        ≤ᵐ[stdGauss (Fin (m + 1))]
        fun g => GK v (perpDir v g) (axialS a r) (axialR a r) ^ 4 := by
      filter_upwards [BstLean.Part89.perp_unit hm1 v hv] with g hg
      have hvw := BstLean.Part56.perpDir_orth56 v g hv
      have e : polarPoint v (perpDir v g) a r = axialS a r • v + axialR a r • perpDir v g := rfl
      have ht := tau_pt (axialS a r) (axialR a r) hv hvw hg hSR hR0
      rw [← e] at ht
      have h1 := mul_le_mul_of_nonneg_left ht hR0
      have e4 : axialR a r ^ 4 *
          (tauR 3 v (polarPoint v (perpDir v g) a r) - kbar v (axialS a r)) ^ 4 =
          (axialR a r * |tauR 3 v (polarPoint v (perpDir v g) a r) - kbar v (axialS a r)|) ^ 4 := by
        rw [mul_pow, Even.pow_abs (by decide)]
      rw [e4]
      refine pow_le_pow_left₀ (mul_nonneg hR0 (abs_nonneg _)) (h1.trans (le_of_eq ?_)) 4
      unfold GK FB; ring
    refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => by positivity)
      (int_c (F := fun w => GK v w (axialS a r) (axialR a r) ^ 4) ((GK_cont _ _).pow 4)) hae) ?_
    refine le_trans hK (le_of_eq ?_)
    rw [div_pow, hmr]; ring

end

end BstLean.Part90

#print axioms BstLean.Part90.sliceMom
