import BstLean.Part81UM
import BstLean.Part81UP
import BstLean.Part81UW
import BstLean.Part81KerGen
import BstLean.Part81KD

/-!
# Part 81 (UX): the feature operator bound and the moment form of the sphere constants,
uniform in the map degree
-/

namespace BstLean.Part81.UX

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part53 (hS53)
open BstLean.Part81 BstLean.Part81.UM BstLean.Part81.KD

variable {n : ℕ}

/-- `S(x) = Σ_{k ≤ m} h_k(x²)`. -/
noncomputable def Sx (m : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), hS53 (fun l => x l ^ 2) k

lemma Sx_ge (m : ℕ) (x : Fin n → ℝ) : 1 ≤ Sx m x := by
  unfold Sx
  rw [Finset.sum_range_succ', hSZero53]
  have : 0 ≤ ∑ k ∈ Finset.range m, hS53 (fun l => x l ^ 2) (k + 1) :=
    Finset.sum_nonneg fun k _ => UP.hS_nonneg _ (fun i => sq_nonneg _) _
  linarith

lemma Sx_le (m : ℕ) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    Sx m x ≤ 2719 / 1000 * Gq (m / 2) (∑ i, x i ^ 4) := by
  have h := hS_sum_le n m (fun i => x i ^ 2) (fun i => sq_nonneg _) hx
  rw [q4_eq] at h
  exact h

/-- `G_M(q) ≤ 1 + Σ_{k<M} P_{k+2}` on the sphere. -/
lemma Gq_le_P (M : ℕ) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    Gq M (∑ i, x i ^ 4) ≤ 1 + ∑ k ∈ Finset.range M, P (k + 2) x := by
  unfold Gq
  rw [Finset.sum_range_succ', pow_zero, add_comm]
  have : ∑ k ∈ Finset.range M, (∑ i, x i ^ 4) ^ (k + 1) ≤ ∑ k ∈ Finset.range M, P (k + 2) x :=
    Finset.sum_le_sum fun k _ => qpow_le_P x hx (k + 1)
  linarith

lemma sumG2 (n : ℕ) (hn : 1000 ≤ n) (M : ℕ) :
    ∑ k ∈ Finset.range M, muS n (k + 2) ≤ 3 / (n : ℝ) + 16 / (n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have h1 : ∑ k ∈ Finset.range M, muS n (k + 2) ≤ ∑ k ∈ Finset.range (M + 1), muS n (k + 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      (fun k _ _ => (muS_pos' n hn1 _).le)
  rw [Finset.sum_range_succ'] at h1
  have h2 := sum1_range n hn M
  have h3 := muS_two_le n hn1
  simp only [zero_add] at h1
  have e : ∑ k ∈ Finset.range M, muS n (k + 1 + 2) = ∑ k ∈ Finset.range M, muS n (k + 3) := rfl
  rw [e] at h1
  linarith

lemma int_fourth (hn : 1 ≤ n) (i : Fin n) :
    ∫ x, x i ^ 4 ∂uniformSphere n ≤ 3 / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by positivity
  have h := int_pow_even hn i 2
  have h2 := muS_eq hn 2
  have h3 := muS_two_le n hn
  have e : ∫ x, x i ^ 4 ∂uniformSphere n = muS n 2 / n := by
    have : (2 * 2 : ℕ) = 4 := rfl
    rw [this] at h h2
    rw [h, h2]; field_simp
  rw [e, div_le_iff₀ hn0]
  have : 3 / (n : ℝ) ^ 2 * n = 3 / n := by field_simp
  rw [this]; exact h3

lemma coord_le_one (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) (j : Fin n) : x j ^ 2 ≤ 1 := by
  rw [← hx]
  exact Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)

lemma P_nonneg (j : ℕ) (x : Fin n → ℝ) : 0 ≤ P j x := by
  unfold P
  exact Finset.sum_nonneg fun k _ => by rw [pow_mul]; positivity

/-- Light row. -/
lemma rowL (n : ℕ) (hn : 1000 ≤ n) (τ : ℝ) (hτ : 0 < τ) (m : ℕ) (i : Fin n) :
    ∫ x, x i ^ 2 * (1 + τ * (Sx m x - 1)) ∂uniformSphere n ≤
      ((1 - τ) + τ * (2719 / 1000) * (1 + 3 / (n : ℝ) + 16 / (n : ℝ) ^ 2)) / n := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by positivity
  have c1 : Continuous (fun x : Fin n → ℝ => x i ^ 2 * P 1 x) := by
    have := P_cont (n := n) 1; fun_prop
  have c2 : Continuous (fun x : Fin n → ℝ => x i ^ 2 * Gq (m / 2) (∑ k, x k ^ 4)) := by
    unfold Gq; fun_prop
  have i1 := BstLean.Part78.sph_int hn1 c1
  have i2 := BstLean.Part78.sph_int hn1 c2
  have hg : Integrable (fun x : Fin n → ℝ => (1 - τ) * (x i ^ 2 * P 1 x)
      + τ * (2719 / 1000) * (x i ^ 2 * Gq (m / 2) (∑ k, x k ^ 4))) (uniformSphere n) :=
    (i1.const_mul _).add (i2.const_mul _)
  have h : ∫ x, x i ^ 2 * (1 + τ * (Sx m x - 1)) ∂uniformSphere n ≤
      ∫ x, ((1 - τ) * (x i ^ 2 * P 1 x)
        + τ * (2719 / 1000) * (x i ^ 2 * Gq (m / 2) (∑ k, x k ^ 4))) ∂uniformSphere n := by
    apply integral_mono_of_nonneg _ hg
    · filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
      have hS := Sx_le m x hx
      have hP : P 1 x = 1 := by unfold P; simpa using hx
      rw [hP]
      have h0 : 0 ≤ x i ^ 2 := sq_nonneg _
      have : 1 + τ * (Sx m x - 1) ≤ (1 - τ) + τ * (2719 / 1000) * Gq (m / 2) (∑ k, x k ^ 4) := by
        nlinarith
      have := mul_le_mul_of_nonneg_left this h0
      linarith
    · filter_upwards with x
      have := Sx_ge m x
      have : 0 ≤ τ * (Sx m x - 1) := mul_nonneg hτ.le (by linarith)
      exact mul_nonneg (sq_nonneg _) (by linarith)
  rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul] at h
  have a1 : ∫ x, x i ^ 2 * P 1 x ∂uniformSphere n = 1 / n := by
    have := int_sq_powsum n hn1 i 1
    unfold P; rw [this, muS_one n hn1]
  have a2 := int_sq_Gq n hn i (m / 2)
  rw [a1] at h
  refine h.trans ?_
  have : τ * (2719 / 1000) * ∫ x, x i ^ 2 * Gq (m / 2) (∑ k, x k ^ 4) ∂uniformSphere n
      ≤ τ * (2719 / 1000) * ((1 + 3 / (n : ℝ) + 16 / (n : ℝ) ^ 2) / n) :=
    mul_le_mul_of_nonneg_left a2 (by positivity)
  have e : ((1 - τ) + τ * (2719 / 1000) * (1 + 3 / (n : ℝ) + 16 / (n : ℝ) ^ 2)) / n
      = (1 - τ) * (1 / n) + τ * (2719 / 1000) * ((1 + 3 / (n : ℝ) + 16 / (n : ℝ) ^ 2) / n) := by
    ring
  rw [e]; linarith

/-- Heavy row. -/
lemma rowH (n : ℕ) (hn : 1000 ≤ n) (τ : ℝ) (hτ : 0 < τ) (m : ℕ) (i j : Fin n) :
    ∫ x, x i ^ 2 * x j ^ 2 * (1 / τ + (Sx m x - 1)) ∂uniformSphere n ≤
      (1 / τ + 1719 / 1000) * (3 / (n : ℝ) ^ 2)
        + 2719 / 1000 * ((3 / (n : ℝ) + 16 / (n : ℝ) ^ 2) / n) := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by positivity
  have hτi : 0 < 1 / τ := by positivity
  have hPc := fun j => P_cont (n := n) j
  have c1 : Continuous (fun x : Fin n → ℝ => x i ^ 4) := by fun_prop
  have c2 : Continuous (fun x : Fin n → ℝ => x j ^ 4) := by fun_prop
  have c3 : Continuous (fun x : Fin n → ℝ =>
      ∑ s ∈ Finset.range (m / 2), 1 * (x i ^ 2 * P (s + 2) x)) := by fun_prop
  have i1 := BstLean.Part78.sph_int hn1 c1
  have i2 := BstLean.Part78.sph_int hn1 c2
  have i3 := BstLean.Part78.sph_int hn1 c3
  set A : ℝ := (1 / τ + 1719 / 1000) / 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hg : Integrable (fun x : Fin n → ℝ => A * x i ^ 4 + A * x j ^ 4
      + 2719 / 1000 * ∑ s ∈ Finset.range (m / 2), 1 * (x i ^ 2 * P (s + 2) x))
      (uniformSphere n) := ((i1.const_mul _).add (i2.const_mul _)).add (i3.const_mul _)
  have h : ∫ x, x i ^ 2 * x j ^ 2 * (1 / τ + (Sx m x - 1)) ∂uniformSphere n ≤
      ∫ x, (A * x i ^ 4 + A * x j ^ 4
      + 2719 / 1000 * ∑ s ∈ Finset.range (m / 2), 1 * (x i ^ 2 * P (s + 2) x))
        ∂uniformSphere n := by
    apply integral_mono_of_nonneg _ hg
    · filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
      have hS := Sx_le m x hx
      have hG := Gq_le_P (m / 2) x hx
      set T := ∑ k ∈ Finset.range (m / 2), P (k + 2) x with hT
      have hT0 : 0 ≤ T := Finset.sum_nonneg fun k _ => P_nonneg _ x
      have e : ∑ s ∈ Finset.range (m / 2), 1 * (x i ^ 2 * P (s + 2) x) = x i ^ 2 * T := by
        rw [hT, Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring
      rw [e]
      have hi0 : 0 ≤ x i ^ 2 := sq_nonneg _
      have hj0 : 0 ≤ x j ^ 2 := sq_nonneg _
      have hj1 := coord_le_one x hx j
      have hb : 1 / τ + (Sx m x - 1) ≤ 2 * A + 2719 / 1000 * T := by
        rw [hA]; linarith
      have hij : x i ^ 2 * x j ^ 2 ≤ (x i ^ 4 + x j ^ 4) / 2 := by
        nlinarith [sq_nonneg (x i ^ 2 - x j ^ 2)]
      have hij0 : 0 ≤ x i ^ 2 * x j ^ 2 := mul_nonneg hi0 hj0
      have hij1 : x i ^ 2 * x j ^ 2 ≤ x i ^ 2 := by nlinarith
      calc x i ^ 2 * x j ^ 2 * (1 / τ + (Sx m x - 1))
          ≤ x i ^ 2 * x j ^ 2 * (2 * A + 2719 / 1000 * T) := mul_le_mul_of_nonneg_left hb hij0
        _ = (x i ^ 2 * x j ^ 2) * (2 * A) + 2719 / 1000 * ((x i ^ 2 * x j ^ 2) * T) := by ring
        _ ≤ ((x i ^ 4 + x j ^ 4) / 2) * (2 * A) + 2719 / 1000 * (x i ^ 2 * T) := by
            have h1 := mul_le_mul_of_nonneg_right hij (by positivity : 0 ≤ 2 * A)
            have h2 := mul_le_mul_of_nonneg_right hij1 hT0
            linarith
        _ = _ := by ring
    · filter_upwards with x
      have := Sx_ge m x
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by linarith)
  have i12 : Integrable (fun x : Fin n → ℝ => A * x i ^ 4 + A * x j ^ 4) (uniformSphere n) :=
    (i1.const_mul _).add (i2.const_mul _)
  rw [integral_add i12 (i3.const_mul _),
    integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, int_lin_sq hn1] at h
  simp only [one_mul] at h
  have b1 := int_fourth hn1 i
  have b2 := int_fourth hn1 j
  have b3 := sumG2 n hn (m / 2)
  have b3' : (∑ s ∈ Finset.range (m / 2), muS n (s + 2)) / n
      ≤ (3 / (n : ℝ) + 16 / (n : ℝ) ^ 2) / n := by gcongr
  refine h.trans ?_
  have e : (1 / τ + 1719 / 1000) * (3 / (n : ℝ) ^ 2) = A * (3 / (n : ℝ) ^ 2) + A * (3 / (n : ℝ) ^ 2) := by
    rw [hA]; ring
  rw [e]
  have := mul_le_mul_of_nonneg_left b1 hA0
  have := mul_le_mul_of_nonneg_left b2 hA0
  linarith

/-- The diagonal defect and its majorant. -/
noncomputable def gq (d : ℕ) (x : Fin n → ℝ) : ℝ :=
  ((∑ i, x i ^ 4) + ∑ i, x i ^ 6) * Gq (d / 2) (∑ i, x i ^ 4)

lemma gq_cont (d : ℕ) : Continuous (gq (n := n) d) := by unfold gq Gq; fun_prop

lemma delta_bounds (d : ℕ) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    0 ≤ kap d x x - eD d ∧ kap d x x - eD d ≤ 2719 / 2000 * gq d x := by
  refine ⟨sub_nonneg.mpr (kap_diag_lower n d x hx), ?_⟩
  have := kap_delta_le n d x hx
  unfold gq; linarith

lemma delta_cont (d : ℕ) : Continuous (fun x : Fin n → ℝ => kap d x x - eD d) :=
  (cont_kap_diag (n := n) (d := d)).sub continuous_const

lemma int_delta_pow (hn : 1 ≤ n) (d k : ℕ) :
    ∫ x, (kap d x x - eD d) ^ k ∂uniformSphere n ≤
      (2719 / 2000) ^ k * ∫ x, gq d x ^ k ∂uniformSphere n := by
  rw [← integral_const_mul]
  apply int_le hn (f := fun x : Fin n → ℝ => (kap d x x - eD d) ^ k)
    (g := fun x => (2719 / 2000) ^ k * gq d x ^ k)
    ((delta_cont d).pow k) (continuous_const.mul ((gq_cont d).pow k))
  intro x hx
  obtain ⟨h0, h1⟩ := delta_bounds d x hx
  show (kap d x x - eD d) ^ k ≤ (2719 / 2000) ^ k * gq d x ^ k
  rw [← mul_pow]
  exact pow_le_pow_left₀ h0 h1 k

end BstLean.Part81.UX

namespace BstLean.Part81

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part81.UX BstLean.Part81.KD

/-- **Feature operator bound, uniform in the map degree.** -/
theorem featOpU (n d : ℕ) (hn : 5000 ≤ n) : FeatOp n d (101 / 100) := by
  have hn1 : 1 ≤ n := by omega
  have hnk : 1000 ≤ n := by omega
  have hnR : (5000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ht : 1 / (n : ℝ) ≤ 1 / 5000 := one_div_le_one_div_of_le (by norm_num) hnR
  have ht0 : 0 < 1 / (n : ℝ) := by positivity
  have e1 : (3 : ℝ) / n = 3 * (1 / n) := by ring
  have e2 : (16 : ℝ) / (n : ℝ) ^ 2 = 16 * (1 / n) ^ 2 := by ring
  have e3 : (3 : ℝ) / (n : ℝ) ^ 2 = 3 * (1 / n) ^ 2 := by ring
  apply featOp_of_rowW n d hn1 (1 / 400) (101 / 100) (by norm_num) (by norm_num)
  · intro i
    have h := rowL n hnk (1 / 400) (by norm_num) (d / 2) i
    refine h.trans ?_
    rw [div_le_div_iff_of_pos_right hn0, e1, e2]
    set t : ℝ := 1 / (n : ℝ)
    nlinarith
  · intro i j
    have h := rowH n hnk (1 / 400) (by norm_num) (d / 2) i j
    refine h.trans ?_
    have e4 : (101 / 100 : ℝ) / n = 101 / 100 * (1 / n) := by ring
    have e5 : (3 / (n : ℝ) + 16 / (n : ℝ) ^ 2) / n = 3 * (1 / n) ^ 2 + 16 * (1 / n) ^ 3 := by
      field_simp
    rw [e3, e4, e5]
    set t : ℝ := 1 / (n : ℝ)
    have t2 : t ^ 2 ≤ 1 / 5000 * t := by nlinarith
    have t3 : t ^ 3 ≤ 1 / 5000 * t ^ 2 := by nlinarith [sq_nonneg t]
    norm_num
    nlinarith

/-- **Sphere constants, moment form, uniform in the map degree.** -/
theorem sphMU (n d : ℕ) (hd : 1 ≤ d) (hn : 5000 ≤ n) (CF : ℝ) (hCF0 : 0 ≤ CF) (hCF1 : CF ≤ 2)
    (hF : FeatOp n d CF) :
    SphM n d CF (CF * (eD d + (4093 / 1000) / (n : ℝ))) (4093 / 1000) 119 2212 := by
  have hn1 : 1 ≤ n := by omega
  have hnk : 1000 ≤ n := by omega
  have hnR : (5000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have := BstLean.Part29.uniformSphere_isProbability n hn1
  have ht : 1 / (n : ℝ) ≤ 1 / 5000 := one_div_le_one_div_of_le (by norm_num) hnR
  have ht0 : 0 < 1 / (n : ℝ) := by positivity
  obtain ⟨hm0, hs0, _, hK⟩ := kerGen n d hn1
  obtain ⟨hm1, hs1⟩ := hK CF hCF0 hF
  -- item 1
  have hint : Integrable (fun x : Fin n → ℝ => kap d x x) (uniformSphere n) :=
    BstLean.Part78.sph_int hn1 cont_kap_diag
  have h1 : tG n d - eD d ≤ (4093 / 1000) / (n : ℝ) := by
    have hd1 := int_delta_pow hn1 d 1
    simp only [pow_one] at hd1
    rw [integral_sub hint (integrable_const _)] at hd1
    simp only [integral_const, probReal_univ, one_smul] at hd1
    have hq := int_qG1 n hnk (d / 2)
    have hq' : ∫ x, gq d x ∂uniformSphere n ≤ 3 / (n : ℝ) + 48 / (n : ℝ) ^ 2 := hq
    have e1 : (3 : ℝ) / n + 48 / (n : ℝ) ^ 2 = 3 * (1 / n) + 48 * (1 / n) ^ 2 := by ring
    have e2 : (4093 / 1000 : ℝ) / n = 4093 / 1000 * (1 / n) := by ring
    rw [e1] at hq'
    rw [e2]
    unfold tG
    set t : ℝ := 1 / (n : ℝ)
    nlinarith
  have h2 : ∫ x, (kap d x x - eD d) ^ 2 ∂uniformSphere n ≤ 119 / (n : ℝ) ^ 2 := by
    have hd2 := int_delta_pow hn1 d 2
    have hq : ∫ x, gq d x ^ 2 ∂uniformSphere n ≤ 64 / (n : ℝ) ^ 2 := int_qG2 n hnk (d / 2)
    have e : (119 : ℝ) / (n : ℝ) ^ 2 = 119 / 64 * (64 / (n : ℝ) ^ 2) := by ring
    have p : (0 : ℝ) ≤ 64 / (n : ℝ) ^ 2 := by positivity
    rw [e]; nlinarith
  have h3 : ∫ x, (kap d x x - eD d) ^ 3 ∂uniformSphere n ≤ 2212 / (n : ℝ) ^ 3 := by
    have hd3 := int_delta_pow hn1 d 3
    have hq : ∫ x, gq d x ^ 3 ∂uniformSphere n ≤ 880 / (n : ℝ) ^ 3 := int_qG3 n hnk (d / 2)
    have e : (2212 : ℝ) / (n : ℝ) ^ 3 = 2212 / 880 * (880 / (n : ℝ) ^ 3) := by ring
    have p : (0 : ℝ) ≤ 880 / (n : ℝ) ^ 3 := by positivity
    rw [e]; nlinarith
  have hs2 : ss2 n d ≤ CF * (eD d + (4093 / 1000) / (n : ℝ)) / (n : ℝ) := by
    refine hs1.trans ?_
    have : CF / (n : ℝ) * tG n d ≤ CF / (n : ℝ) * (eD d + (4093 / 1000) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    refine this.trans (le_of_eq ?_)
    ring
  have hm1' : mm1 n d ≤ 1 := by
    refine hm1.trans ?_
    rw [div_le_one hn0]; linarith
  refine ⟨h1, h2, h3, hm0, hm1, hs0, hs2, fun x hx => ?_⟩
  have hk := kap_diag_lower n d x hx
  have he := one_le_eD d hd
  have hk1 : 1 ≤ kap d x x := he.trans hk
  refine ⟨hk, inner_kap_nonneg n d hn1 x, ?_⟩
  have hsq := k1_sq_le n d hn1 x
  have : (∫ y, kap d x y ∂uniformSphere n) ^ 2 ≤ kap d x x ^ 2 := by
    refine hsq.trans ?_
    nlinarith
  exact (abs_le_of_sq_le_sq' this (by linarith)).2

theorem eD_two : eD 2 = 3 / 2 := by
  rw [eD_eq]; norm_num [Finset.sum_range_succ, Nat.factorial]

theorem eD_four_le (d : ℕ) (hd : 4 ≤ d) : 41 / 24 ≤ eD d := by
  refine le_trans (le_of_eq ?_) (eD_mono hd)
  rw [eD_eq]; norm_num [Finset.sum_range_succ, Nat.factorial]

end BstLean.Part81

#print axioms BstLean.Part81.featOpU
#print axioms BstLean.Part81.sphMU
#print axioms BstLean.Part81.eD_two
#print axioms BstLean.Part81.eD_four_le
