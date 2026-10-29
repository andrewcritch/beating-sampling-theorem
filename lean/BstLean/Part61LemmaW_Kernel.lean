import BstLean.Part61LemmaW_Symmetric
import BstLean.Part56MomProg_Basic
import BstLean.Part56PropD_Assemble

/-! The block kernel is a complete homogeneous polynomial at `xᵢvᵢ`.
Its signed Lipschitz bound reduces the mean-direction error to a weighted residual.
-/

namespace BstLean.Part61.W
open BstLean.Part56 BstLean.Part58.Kappa BstLean.Part41
open MeasureTheory
set_option maxHeartbeats 1000000
variable {n d : ℕ}

lemma kJ_hval (j : ℕ) (hj : j ≤ d) (x v : Fin n → ℝ) :
    kJ d j x v = hval j (fun i => x i * v i) := by
  classical
  let b : Fin (d+1) := ⟨j, by omega⟩
  unfold kJ
  rw [Fintype.sum_sigma, Finset.sum_eq_single b]
  · simp only [phiB, b, ite_true]
    rw [hval_eq]
    apply Finset.sum_congr rfl
    intro s hs
    exact Multiset.prod_map_mul.symm
  · intro c hc hcb
    have hcj : (c : ℕ) ≠ j := by intro he; apply hcb; apply Fin.ext; exact he
    simp only [phiB, hcj, ite_false, zero_mul, Finset.sum_const_zero]
  · simp

lemma kJ_factorial_lower (j : ℕ) (hj : j ≤ d) (v : Fin n → ℝ) (hv : UnitV v) :
    1 ≤ (j.factorial : ℝ) * kJ d j v v := by
  rw [kJ_hval j hj]
  simpa only [← pow_two] using hval_lower j (fun i => v i ^ 2)
    (fun i => sq_nonneg _) hv

def residual (v x : Fin n → ℝ) : ℝ := ∑ i, (v i * (x i - sx61 v x * v i)) ^ 2

lemma residual_nonneg (v x : Fin n → ℝ) : 0 ≤ residual v x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma abs_sum_product_le (v x : Fin n → ℝ) (hv : UnitV v) (hx : UnitV x) :
    ∑ i, |x i * v i| ≤ 1 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |x i|) (fun i => |v i|)
  have hv' : ∑ i, v i ^ 2 = 1 := hv
  have hx' : ∑ i, x i ^ 2 = 1 := hx
  simp only [← abs_mul, sq_abs, hv', hx', one_mul] at h
  have hh : 0 ≤ ∑ i, |x i * v i| := Finset.sum_nonneg fun i hi => abs_nonneg _
  nlinarith

lemma sx_abs_le (v x : Fin n → ℝ) (hv : UnitV v) (hx : UnitV x) : |sx61 v x| ≤ 1 := by
  unfold sx61
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by
    simpa only [mul_comm] using abs_sum_product_le v x hv hx)

lemma kernel_error_sq_le (j : ℕ) (hj : j ≤ d) (v x : Fin n → ℝ)
    (hv : UnitV v) (hx : UnitV x) :
    (kJ d j x v - sx61 v x ^ j * kJ d j v v) ^ 2 ≤ (j : ℝ) ^ 2 * residual v x := by
  have hv' : ∑ i, v i ^ 2 = 1 := hv
  have hz : (∑ i, |sx61 v x * (v i * v i)|) ≤ 1 := by
    simp only [← pow_two, abs_mul, abs_pow, sq_abs, ← Finset.mul_sum, hv', mul_one]
    exact sx_abs_le v x hv hx
  have he : (∑ i, x i * v i) = ∑ i, sx61 v x * (v i * v i) := by
    simp only [← pow_two, ← Finset.mul_sum, hv', mul_one]
    unfold sx61
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hh := hval_sub_sq_bound j (fun i => x i * v i)
    (fun i => sx61 v x * (v i * v i)) (abs_sum_product_le v x hv hx) hz he
  rw [← kJ_hval j hj x v] at hh
  have hs : hval j (fun i => sx61 v x * (v i * v i)) = sx61 v x ^ j * kJ d j v v := by
    rw [kJ_hval j hj]
    exact hval_smul j (fun i => v i * v i) (sx61 v x)
  rw [hs] at hh
  convert hh using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma block_error_le (j : ℕ) (hj : j ≤ d) (v x : Fin n → ℝ)
    (hv : UnitV v) (hx : UnitV x) :
    (betaJ d j v x - sx61 v x ^ j) ^ 2 * kJ d j v v ≤
      ((j.factorial : ℝ) * (j : ℝ) ^ 2) * residual v x := by
  have hk := BstLean.Part56.MomProg.kJ_pos v hv j hj
  have hl := kJ_factorial_lower j hj v hv
  have he := kernel_error_sq_le j hj v x hv hx
  have hR := residual_nonneg v x
  have hr : 0 ≤ (j : ℝ)^2 * residual v x := mul_nonneg (sq_nonneg _) hR
  have hm := mul_le_mul_of_nonneg_left hl hr
  have h : (kJ d j x v - sx61 v x ^ j * kJ d j v v)^2 ≤
      (((j.factorial : ℝ) * (j : ℝ)^2) * residual v x) * kJ d j v v := by
    calc
      _ ≤ (j : ℝ)^2 * residual v x := he
      _ ≤ ((j : ℝ)^2 * residual v x) * ((j.factorial : ℝ) * kJ d j v v) := by
        simpa only [mul_one] using hm
      _ = _ := by ring
  have heq : (betaJ d j v x - sx61 v x ^ j)^2 * kJ d j v v =
      (kJ d j x v - sx61 v x ^ j * kJ d j v v)^2 / kJ d j v v := by
    unfold betaJ
    field_simp [hk.ne']
  rw [heq]
  exact (div_le_iff₀ hk).mpr h

def degreeConstant (d : ℕ) : ℝ := ∑ j ∈ Finset.range (d+1), (j.factorial : ℝ) * (j : ℝ)^2

lemma degreeConstant_nonneg (d : ℕ) : 0 ≤ degreeConstant d := by unfold degreeConstant; positivity

lemma sum_error_le (d : ℕ) (v x : Fin n → ℝ) (hv : UnitV v) (hx : UnitV x) :
    (∑ j ∈ Finset.range (d+1), (betaJ d j v x - sx61 v x^j)^2 * kJ d j v v) ≤
      degreeConstant d * residual v x := by
  unfold degreeConstant
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun j hj => block_error_le j (by simpa using Finset.mem_range.mp hj) v x hv hx

lemma continuous_residual (v : Fin n → ℝ) : Continuous (residual v) := by
  unfold residual sx61
  fun_prop

end BstLean.Part61.W
