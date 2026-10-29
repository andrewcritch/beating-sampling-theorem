import BstLean.Part218Homogeneous
import BstLean.Part218AngularMoments
import BstLean.Part218Distance
import BstLean.Part218ScaledTrace

/-! The actual first-layer covariance has the linear and angular decomposition in P10e. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part105 BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part137 BstLean.Part141 BstLean.Part205 BstLean.Part214

noncomputable def rowCos {N : ℕ} (x y : Fin N → ℝ) : ℝ := dotp x y / (nrm x * nrm y)
noncomputable def angularOffset (N : ℕ) : ℝ := 1 / (2 * π * N) - cN N ^ 2

lemma rowCos_symm {N : ℕ} (x y : Fin N → ℝ) : rowCos x y = rowCos y x := by
  unfold rowCos dotp
  simp only [mul_comm]

lemma angularOffset_nonpos {N : ℕ} (hN : 2 ≤ N) : angularOffset N ≤ 0 :=
  sub_nonpos.mpr (BstLean.Part159.cN_sq_window hN).1

lemma rowCos_abs_le {N : ℕ} (x y : Fin N → ℝ) : |rowCos x y| ≤ 1 := by
  have hp : 0 ≤ nrm x * nrm y := mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  unfold rowCos
  rw [abs_div, abs_of_nonneg hp]
  rcases hp.eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · exact (div_le_one h0).mpr (abs_dotp_le_nrm x y)

lemma rowCos_mul {N : ℕ} (x y : Fin N → ℝ) : nrm x * nrm y * rowCos x y = dotp x y := by
  by_cases h0 : nrm x * nrm y = 0
  · have hd : dotp x y = 0 := abs_eq_zero.mp (le_antisymm
      (by simpa only [h0] using abs_dotp_le_nrm x y) (abs_nonneg _))
    rw [h0, zero_mul, hd]
  · unfold rowCos
    exact mul_div_cancel₀ (dotp x y) h0

noncomputable def firstCovEntry {N m : ℕ} (M : Matrix (Fin m) (Fin N) ℝ) (i j : Fin m) : ℝ :=
  ∫ u, centeredFirst M i u * centeredFirst M j u ∂uniformSphere N

noncomputable def firstLinearEntry {N m : ℕ} (M : Matrix (Fin m) (Fin N) ℝ) (i j : Fin m) : ℝ :=
  dotp (rowOf i M) (rowOf j M) / (4 * N)

noncomputable def firstRemainderEntry {N m : ℕ} (M : Matrix (Fin m) (Fin N) ℝ) (i j : Fin m) : ℝ :=
  firstCovEntry M i j - firstLinearEntry M i j

theorem firstCovEntry_formula {N m : ℕ} (hN : 1 ≤ N)
    (M : Matrix (Fin m) (Fin N) ℝ) (i j : Fin m) :
    firstCovEntry M i j = kernelPhi (rowOf i M) (rowOf j M) / (2 * N) -
      cN N ^ 2 * nrm (rowOf i M) * nrm (rowOf j M) := by
  have := uniformSphere_isProbability N hN
  have ci : Continuous (fun u => reluV (M.mulVec u) i) :=
    (continuous_apply i).comp (continuous_h1_u M)
  have cj : Continuous (fun u => reluV (M.mulVec u) j) :=
    (continuous_apply j).comp (continuous_h1_u M)
  have h := (centered_product_integral (sphere_cont_integrable hN ci) (sphere_cont_integrable hN cj)
    (sphere_cont_integrable hN (ci.mul cj)) (h1bar M i) (h1bar M j)).2
  change firstCovEntry M i j =
    (∫ u, reluV (M.mulVec u) i * reluV (M.mulVec u) j ∂uniformSphere N) -
      h1bar M j * h1bar M i - h1bar M i * h1bar M j + h1bar M i * h1bar M j at h
  have hp : (∫ u, reluV (M.mulVec u) i * reluV (M.mulVec u) j ∂uniformSphere N) =
      kernelPhi (rowOf i M) (rowOf j M) / (2 * N) := by
    convert sphere_relu_pair hN (rowOf i M) (rowOf j M) using 1
    apply integral_congr_ae
    filter_upwards [] with u
    unfold reluV Matrix.mulVec dotProduct dotp rowOf
    simp only [mul_comm]
  rw [h, hp, h1bar_eq hN, h1bar_eq hN]
  ring

/-- The formula also holds when either row is zero. -/
theorem firstRemainderEntry_formula {N m : ℕ} (hN : 1 ≤ N)
    (M : Matrix (Fin m) (Fin N) ℝ) (i j : Fin m) :
    firstRemainderEntry M i j = nrm (rowOf i M) * nrm (rowOf j M) *
      angularK N (angularOffset N) (rowCos (rowOf i M) (rowOf j M)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  unfold firstRemainderEntry firstLinearEntry
  rw [firstCovEntry_formula hN]
  have hd := rowCos_mul (rowOf i M) (rowOf j M)
  change nrm (rowOf i M) * nrm (rowOf j M) *
      BstLean.Part130.kappa (rowCos (rowOf i M) (rowOf j M)) / (2 * N) -
      cN N ^ 2 * nrm (rowOf i M) * nrm (rowOf j M) -
      dotp (rowOf i M) (rowOf j M) / (4 * N) = _
  rw [← hd]
  unfold angularK angularG angularOffset
  field_simp
  ring

/-- The linear covariance term has the exact Wishart normalization used by the paper. -/
theorem firstLinear_frob {N m : ℕ} (hN : 1 ≤ N) (M : Matrix (Fin m) (Fin N) ℝ) :
    (∑ i, ∑ j, firstLinearEntry M i j ^ 2) = paperTrace N m M / (4 * (N : ℝ) ^ 4) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  unfold paperTrace
  rw [wishartTrace_entries]
  have he : ∀ i j : Fin m,
      firstLinearEntry M i j ^ 2 = dotp (M j) (M i) ^ 2 / (16 * (N : ℝ) ^ 2) := by
    intro i j
    unfold firstLinearEntry rowOf dotp
    have hs : (∑ k, M i k * M j k) = ∑ k, M j k * M i k := by
      apply Finset.sum_congr rfl; intro k _; ring
    rw [hs]
    ring
  simp_rw [he, ← Finset.sum_div]
  field_simp
  ring

end BstLean.Part218
#print axioms BstLean.Part218.firstCovEntry_formula
#print axioms BstLean.Part218.firstRemainderEntry_formula
#print axioms BstLean.Part218.firstLinear_frob
