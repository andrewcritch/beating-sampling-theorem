import BstLean.Part172SRow

/-!
# Part 172 (file `SBnd`): the deterministic bounds of `ς²` on a latitude

No proof is left open; no `native_decide` or `axiom` is used.

With `u = û`, `z_i = a_i·u` and `|p_i|² = |a_i|² − z_i²` (`a_i` the rows of `A₁`), for every
latitude `0 ≤ s ≤ 1` (`s² ≤ 1`):
* **`sg_vsig2_lower`**: `ς²(s) ≥ t_A(1 − s²)/(4(n − 1))·Σ_{z_i ≥ 0} |p_i|²`;
* **`sg_vsig2_upper`**: `ς²(s) ≤ t_A(1 − s²)/(n − 1)·Σ_i |p_i|²`.
-/

namespace BstLean.Part172

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq relu)
open BstLean.Part157 (Ret)
open BstLean.Part161 (hhMat uHat consV xLat)
open BstLean.Part53 (unitF53 measurable_unitF)
open BstLean.Part169 (A1 a1Bar e1Bar vsig2)

variable {n : ℕ}

lemma sg_sum_split (hn : 1 ≤ n) (F : Fin n → ℝ) :
    ∑ k, F k = F ⟨0, by omega⟩ + ∑ j : Fin (n - 1), F ⟨j + 1, by omega⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Fin.sum_univ_succ]
  rfl

lemma sg_consV_succ (z : ℝ) (g : Fin (n - 1) → ℝ) (j : Fin (n - 1)) (h : (j : ℕ) + 1 < n) :
    consV z g ⟨j + 1, h⟩ = g j := by
  simp [consV]

lemma sg_hh_sq (u : Fin n → ℝ) : hhMat u * hhMat u = 1 := by
  have h := BstLean.Part161.hh_mul_transpose u
  have e : (hhMat u).transpose = hhMat u := by
    ext i j; simp [Matrix.transpose_apply, BstLean.Part161.hh_symm]
  rwa [e] at h

/-- `z(a) = a·u`. -/
noncomputable def sg_z (u a : Fin n → ℝ) : ℝ := ∑ j, a j * u j

/-- `p(a)`: the last `n − 1` coordinates of `H a`. -/
noncomputable def sg_p (hn : 1 ≤ n) (u a : Fin n → ℝ) : Fin (n - 1) → ℝ :=
  fun j => (hhMat u *ᵥ a) ⟨j + 1, by omega⟩

lemma sg_Ha0 (hn : 1 ≤ n) {u : Fin n → ℝ} (hu : normSq u = 1) (a : Fin n → ℝ) :
    (hhMat u *ᵥ a) ⟨0, by omega⟩ = sg_z u a := by
  have h := BstLean.Part161.hh_dot u (hhMat u *ᵥ a) (BstLean.Part130.e0 n)
  rw [Matrix.mulVec_mulVec, sg_hh_sq, Matrix.one_mulVec, BstLean.Part161.hh_e0 hn hu] at h
  rw [← BstLean.Part161.e0_dot hn (hhMat u *ᵥ a), sg_z, h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma sg_normSq_p (hn : 1 ≤ n) {u : Fin n → ℝ} (hu : normSq u = 1) (a : Fin n → ℝ) :
    normSq (sg_p hn u a) = normSq a - sg_z u a ^ 2 := by
  have h := BstLean.Part161.hh_normSq u a
  unfold normSq at h
  rw [sg_sum_split hn, sg_Ha0 hn hu] at h
  unfold normSq sg_p
  linarith

lemma sg_row_form (hn : 1 ≤ n) {m : ℕ} {u : Fin n → ℝ} (hu : normSq u = 1)
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (s : ℝ) (w : Fin (n - 1) → ℝ) :
    (A *ᵥ (hhMat u *ᵥ consV s (√(1 - s ^ 2) • w))) i =
      s * sg_z u (A i) + √(1 - s ^ 2) * ∑ k, sg_p hn u (A i) k * w k := by
  set y := consV (n := n) s (√(1 - s ^ 2) • w)
  have e1 : (A *ᵥ (hhMat u *ᵥ y)) i = ∑ k, (hhMat u *ᵥ A i) k * y k := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [BstLean.Part161.hh_symm u j k]; ring
  rw [e1, sg_sum_split hn, sg_Ha0 hn hu]
  have e2 : y ⟨0, by omega⟩ = s := BstLean.Part161.consV_zero hn _ _
  rw [e2, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [y, sg_consV_succ, sg_p, Pi.smul_apply, smul_eq_mul]
    ring

lemma sg_var_nonneg {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ v, |f v| ≤ C) :
    0 ≤ ∫ v, f v ^ 2 ∂stdGauss (Fin d) - (∫ v, f v ∂stdGauss (Fin d)) ^ 2 := by
  have h := sg_var_eq hf hC (∫ v, f v ∂stdGauss (Fin d))
  have h0 : 0 ≤ ∫ v, (f v - ∫ v, f v ∂stdGauss (Fin d)) ^ 2 ∂stdGauss (Fin d) :=
    integral_nonneg fun v => sq_nonneg _
  rw [sub_self, zero_pow two_ne_zero, add_zero] at h
  linarith

/-- The row variance at the latitude `s`, as the variance of `ReLU(μ + σY)`. -/
lemma sg_row_var_eq (hn : 1 ≤ n) (c : Ret n) (hc : c.1.2 ≠ 0) (s : ℝ) (i : Fin (BstLean.Part130.mA n)) :
    e1Bar c s i - a1Bar c s i ^ 2 =
      ∫ v, relu (s * sg_z (uHat c) (A1 c i) + √(1 - s ^ 2) *
          sg_Y (sg_p hn (uHat c) (A1 c i)) v) ^ 2 ∂stdGauss (Fin (n - 1)) -
        (∫ v, relu (s * sg_z (uHat c) (A1 c i) + √(1 - s ^ 2) *
          sg_Y (sg_p hn (uHat c) (A1 c i)) v) ∂stdGauss (Fin (n - 1))) ^ 2 := by
  have hu := BstLean.Part161.normSq_uHat hc
  have e : ∀ v, (A1 c).mulVec (xLat c s (unitF53 v)) i = s * sg_z (uHat c) (A1 c i) +
      √(1 - s ^ 2) * sg_Y (sg_p hn (uHat c) (A1 c i)) v := fun v =>
    sg_row_form hn hu (A1 c) i s (unitF53 v)
  unfold e1Bar a1Bar
  simp_rw [e]

/-- **Lower bound of `ς²`** (for `0 ≤ s`, `s² ≤ 1`). -/
theorem sg_vsig2_lower (hn : 2 ≤ n) (c : Ret n) (hc : c.1.2 ≠ 0) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ^ 2 ≤ 1) :
    2 / (BstLean.Part130.mA n : ℝ) * ((1 - s ^ 2) / (4 * ((n - 1 : ℕ) : ℝ))) *
        ∑ i, (if 0 ≤ sg_z (uHat c) (A1 c i) then
          normSq (A1 c i) - sg_z (uHat c) (A1 c i) ^ 2 else 0) ≤ vsig2 c s := by
  have hn1 : 1 ≤ n := by omega
  have hd : 1 ≤ n - 1 := by omega
  have hu := BstLean.Part161.normSq_uHat hc
  have hdR : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hd
  have hσ : (0 : ℝ) ≤ √(1 - s ^ 2) := Real.sqrt_nonneg _
  have hσ2 : √(1 - s ^ 2) ^ 2 = 1 - s ^ 2 := Real.sq_sqrt (by linarith)
  have hrow : ∀ i, (if 0 ≤ sg_z (uHat c) (A1 c i) then
      (1 - s ^ 2) / (4 * ((n - 1 : ℕ) : ℝ)) * (normSq (A1 c i) - sg_z (uHat c) (A1 c i) ^ 2)
      else 0) ≤ e1Bar c s i - a1Bar c s i ^ 2 := by
    intro i
    rw [sg_row_var_eq hn1 c hc s i]
    split_ifs with hz
    · have := sg_row_var_lower hd (sg_p hn1 (uHat c) (A1 c i)) (mul_nonneg hs0 hz) hσ
      rw [sg_normSq_p hn1 hu, hσ2] at this
      calc _ = (1 - s ^ 2) * (normSq (A1 c i) - sg_z (uHat c) (A1 c i) ^ 2) /
            (4 * ((n - 1 : ℕ) : ℝ)) := by ring
        _ ≤ _ := this
    · obtain ⟨hfm, hfC⟩ := sg_row_int (sg_p hn1 (uHat c) (A1 c i))
        (s * sg_z (uHat c) (A1 c i)) (√(1 - s ^ 2))
      exact sg_var_nonneg hfm hfC
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hrow i
  have e : ∑ i, (if 0 ≤ sg_z (uHat c) (A1 c i) then
      (1 - s ^ 2) / (4 * ((n - 1 : ℕ) : ℝ)) * (normSq (A1 c i) - sg_z (uHat c) (A1 c i) ^ 2)
      else 0) = (1 - s ^ 2) / (4 * ((n - 1 : ℕ) : ℝ)) * ∑ i, (if 0 ≤ sg_z (uHat c) (A1 c i) then
          normSq (A1 c i) - sg_z (uHat c) (A1 c i) ^ 2 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  rw [e] at hsum
  have e2 : ∑ i, (e1Bar c s i - a1Bar c s i ^ 2) = ∑ i, e1Bar c s i - normSq (a1Bar c s) := by
    rw [Finset.sum_sub_distrib]; rfl
  rw [e2] at hsum
  unfold vsig2
  have ht : (0 : ℝ) ≤ 2 / (BstLean.Part130.mA n : ℝ) := by positivity
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left hsum ht).trans (le_max_right _ _)

/-- **Upper bound of `ς²`** (for `s² ≤ 1`). -/
theorem sg_vsig2_upper (hn : 2 ≤ n) (c : Ret n) (hc : c.1.2 ≠ 0) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ 2 / (BstLean.Part130.mA n : ℝ) * ((1 - s ^ 2) / ((n - 1 : ℕ) : ℝ)) *
        ∑ i, (normSq (A1 c i) - sg_z (uHat c) (A1 c i) ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hd : 1 ≤ n - 1 := by omega
  have hu := BstLean.Part161.normSq_uHat hc
  have hdR : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hd
  have hσ : (0 : ℝ) ≤ √(1 - s ^ 2) := Real.sqrt_nonneg _
  have hσ2 : √(1 - s ^ 2) ^ 2 = 1 - s ^ 2 := Real.sq_sqrt (by linarith)
  have hrow : ∀ i, e1Bar c s i - a1Bar c s i ^ 2 ≤
      (1 - s ^ 2) / ((n - 1 : ℕ) : ℝ) * (normSq (A1 c i) - sg_z (uHat c) (A1 c i) ^ 2) := by
    intro i
    rw [sg_row_var_eq hn1 c hc s i]
    have := sg_row_var_upper hd (sg_p hn1 (uHat c) (A1 c i)) (s * sg_z (uHat c) (A1 c i)) hσ
    rw [sg_normSq_p hn1 hu, hσ2] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hrow i
  rw [← Finset.mul_sum] at hsum
  have e2 : ∑ i, (e1Bar c s i - a1Bar c s i ^ 2) = ∑ i, e1Bar c s i - normSq (a1Bar c s) := by
    rw [Finset.sum_sub_distrib]; rfl
  rw [e2] at hsum
  have hnn : 0 ≤ ∑ i, (normSq (A1 c i) - sg_z (uHat c) (A1 c i) ^ 2) := by
    refine Finset.sum_nonneg fun i _ => ?_
    rw [← sg_normSq_p hn1 hu]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold vsig2
  have ht : (0 : ℝ) ≤ 2 / (BstLean.Part130.mA n : ℝ) := by positivity
  have h1 : (0 : ℝ) ≤ 1 - s ^ 2 := by linarith
  rw [mul_assoc]
  refine max_le (by positivity) (mul_le_mul_of_nonneg_left hsum ht)

end BstLean.Part172
