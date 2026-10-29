import BstLean.Part130Mean

/-!
# Part 130: the entries of a Gaussian matrix, and the widths of the Focus

* `gaussMat_eq_pi`: `gaussMat m k v` is the image, under the map from entries to matrices, of the
  product measure of `N(0, v)` over the index pairs `(i, j)`: the entries are independent Gaussians
  with mean `0` and variance `v`.
* `mF_le_iff`, `mW_le_iff`: `⌈n^{3/2}⌉` is the least natural number `j` with `n³ ≤ j²`;
  `⌈n^{7/2}⌉` is the least `j` with `n⁷ ≤ j²`.
* `one_le_mA`, `one_le_mF`, `one_le_mW`: the widths of the Focus are positive for `n ≥ 1`.
* `Bn_mean_zero_focus`, `phiN_second_moment_focus`: the identities at the widths of the Focus.
-/

namespace BstLean.Part130

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)

variable {m k : ℕ}

/-- **The entries of a Gaussian matrix are independent `N(0, v)`** (`v ≥ 0`): `gaussMat m k v` is
the image of the product measure `⨂_{(i,j)} N(0, v)` under `ξ ↦ (ξ(i, j))_{i,j}`. -/
theorem gaussMat_eq_pi {v : ℝ} (hv : 0 ≤ v) :
    gaussMat m k v =
      (Measure.pi fun _ : Fin m × Fin k => gaussianReal 0 v.toNNReal).map unflat := by
  have h1 : ∀ _ : Fin m × Fin k, (gaussianReal 0 1).map (Real.sqrt v * ·) = gaussianReal 0 v.toNNReal := by
    intro _
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt hv, Real.coe_toNNReal _ hv]
  have h2 := Measure.pi_map_pi (μ := fun _ : Fin m × Fin k => gaussianReal 0 1)
    (f := fun _ => (Real.sqrt v * ·)) (hμ := fun i => by rw [h1 i]; infer_instance)
    (fun _ => (measurable_const_mul _).aemeasurable)
  have h3 : (fun _ : Fin m × Fin k => (gaussianReal 0 1).map (Real.sqrt v * ·)) =
      fun _ => gaussianReal 0 v.toNNReal := funext h1
  rw [h3] at h2
  have hm : Measurable (fun (x : Fin m × Fin k → ℝ) i => Real.sqrt v * x i) :=
    measurable_pi_iff.mpr fun p => (measurable_const_mul _).comp (measurable_pi_apply p)
  rw [← h2, Measure.map_map measurable_unflat hm]
  rfl

/-! ## The widths -/

lemma ceil_rpow_half_le_iff (n j e : ℕ) :
    ⌈(n : ℝ) ^ ((e : ℝ) / 2)⌉₊ ≤ j ↔ n ^ e ≤ j ^ 2 := by
  rw [Nat.ceil_le]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have ha : 0 ≤ (n : ℝ) ^ ((e : ℝ) / 2) := Real.rpow_nonneg hn _
  have hsq : ((n : ℝ) ^ ((e : ℝ) / 2)) ^ 2 = (n : ℝ) ^ e := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
    norm_num
  constructor
  · intro h
    have : ((n : ℝ) ^ ((e : ℝ) / 2)) ^ 2 ≤ (j : ℝ) ^ 2 := pow_le_pow_left₀ ha h 2
    rw [hsq] at this
    exact_mod_cast this
  · intro h
    have h' : (n : ℝ) ^ e ≤ (j : ℝ) ^ 2 := by exact_mod_cast h
    rw [← hsq] at h'
    exact (pow_le_pow_iff_left₀ ha hj two_ne_zero).mp h'

/-- `m_F = ⌈n^{3/2}⌉` is the least natural number `j` with `n³ ≤ j²`. -/
theorem mF_le_iff (n j : ℕ) : mF n ≤ j ↔ n ^ 3 ≤ j ^ 2 := by
  have := ceil_rpow_half_le_iff n j 3
  simpa [mF] using this

/-- `m_W = ⌈n^{7/2}⌉` is the least natural number `j` with `n⁷ ≤ j²`. -/
theorem mW_le_iff (n j : ℕ) : mW n ≤ j ↔ n ^ 7 ≤ j ^ 2 := by
  have := ceil_rpow_half_le_iff n j 7
  simpa [mW] using this

theorem one_le_mA {n : ℕ} (hn : 1 ≤ n) : 1 ≤ mA n := Nat.one_le_pow _ _ hn

theorem one_le_mF {n : ℕ} (hn : 1 ≤ n) : 1 ≤ mF n := by
  by_contra h
  have h0 : mF n ≤ 0 := by omega
  rw [mF_le_iff] at h0
  have : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ hn
  omega

theorem one_le_mW {n : ℕ} (hn : 1 ≤ n) : 1 ≤ mW n := by
  by_contra h
  have h0 : mW n ≤ 0 := by omega
  rw [mW_le_iff] at h0
  have : 1 ≤ n ^ 7 := Nat.one_le_pow _ _ hn
  omega

/-! ## The identities at the widths of the Focus -/

/-- **Zero mean at the widths of the Focus**: for `r, n ≥ 1` and every fixed `(W, A)`,
`E_F B(W, A, F) = 0`. -/
theorem Bn_mean_zero_focus {r n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n)
    (W : MlpParam (r * n) (mW n) n) (A : MlpParam n (mA n) n) :
    ∫ F, Bn W A F ∂mlpGauss n (mF n) 1 = 0 :=
  Bn_mean_zero hn (Nat.mul_pos hr hn) (one_le_mF hn) W A

/-- **The mean of the second moment at the widths of the Focus**: for `r, n ≥ 1` and every fixed
`W`, `E_A E_F E_u F(A(x))² = 4/n`. -/
theorem phiN_second_moment_focus {r n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n)
    (W : MlpParam (r * n) (mW n) n) :
    ∫ A, ∫ F, ∫ x, phiN A F x ^ 2 ∂muWn W ∂mlpGauss n (mF n) 1 ∂mlpGauss n (mA n) n = 4 / n :=
  phiN_second_moment hn (Nat.mul_pos hr hn) (one_le_mA hn) (one_le_mF hn) W

end BstLean.Part130

open BstLean.Part130 in
#print axioms gaussMat_eq_pi
open BstLean.Part130 in
#print axioms mF_le_iff
open BstLean.Part130 in
#print axioms mW_le_iff
open BstLean.Part130 in
#print axioms Bn_mean_zero_focus
open BstLean.Part130 in
#print axioms phiN_second_moment_focus
