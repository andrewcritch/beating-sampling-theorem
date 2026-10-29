import BstLean.Part59Radial_Moments
import BstLean.Part62HyperK

/-!
# Part 63: explicit radial moment constants

`λ = ‖Z‖/√𝒟`, `X = λ²`, `Z` standard Gaussian in `ℝ^𝒟`.

* `centered_moment_eq63`: `E(X − 1)^m = Σ_{j ≤ m} (−1)^{m−j} C(m,j) ρ_j(𝒟)/𝒟^j`, with
  `ρ_j(𝒟) = Π_{i<j}(𝒟 + 2i)` (exact Gaussian norm moments, `Part41.p1_gauss_norm_moment`).
* `centered_exact63`: the exact bounds `E(X − 1)^{2r} ≤ m_r/𝒟^r` for `r = 1, 2, 3, 4`, with
  `m = 2, 60, 6040, 1190672` (omN0-p59 §2.4). For example `E(X−1)⁴ = (12𝒟² + 48𝒟)/𝒟⁴`.
* `dbl63`, `poly_even_moment63`: the doubling route of `Part59.polynomial_even_moment_bound59x` with
  the explicit fourth-moment constant `Part62.Kexp` in place of `Part48Hyper.fourth_moment`.
* `CR63 r`: `m_r` for `r ≤ 4` and `1 + dbl63 2 2 (2r)` for `r ≥ 5` (every value explicit).
* `radial_moment63`: `E(λ − 1)^{2r} ≤ CR63 r/𝒟^r` for every `r`, `n ≥ 1`.

Do not use `native_decide` or `axiom`.
-/

namespace BstLean.Part63

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD rhoD)
open BstLean.Part53 (sg)
open BstLean.Part53.T2Aux
open BstLean.Part59

private lemma radialPoly_eval63 (n d : ℕ) (s : ℝ) (Z : CoefIdxD n d → ℝ) :
    MvPolynomial.eval Z (radialPoly n d s) = ∑ α, (s • Z) α ^ 2 := by
  classical
  simp [radialPoly, Pi.smul_apply, smul_eq_mul]

private lemma gpow_int63 {ι : Type*} [Fintype ι] (P : MvPolynomial ι ℝ) (r : ℕ) :
    Integrable (fun z => (MvPolynomial.eval z P) ^ r) (stdGauss ι) := by
  simpa only [map_pow] using BstLean.Part48.gauss_poly_integrable (P ^ r)

private lemma radialPoly_moment63 (n d : ℕ) (s : ℝ) (r : ℕ) :
    ∫ Z, (MvPolynomial.eval Z (radialPoly n d s)) ^ r ∂stdGauss (CoefIdxD n d) =
      s ^ (2 * r) * rhoD (Fintype.card (CoefIdxD n d)) r := by
  classical
  have hs (Z : CoefIdxD n d → ℝ) :
      Real.sqrt (∑ α, Z α ^ 2) ^ (2 * r) = (∑ α, Z α ^ 2) ^ r := by
    rw [pow_mul, Real.sq_sqrt (Finset.sum_nonneg fun α hα => sq_nonneg _)]
  have hm := BstLean.Part41.p1_gauss_norm_moment (ι := CoefIdxD n d) r
  simp_rw [hs] at hm
  have he (Z : CoefIdxD n d → ℝ) :
      (MvPolynomial.eval Z (radialPoly n d s)) ^ r =
        s ^ (2 * r) * (∑ α, Z α ^ 2) ^ r := by
    rw [radialPoly_eval63]
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, pow_mul]
  simp_rw [he]
  rw [integral_const_mul, hm]

private lemma sg_sq63 (n d : ℕ) (hn : 1 ≤ n) : (sg n d) ^ 2 = 1 / DD n d := by
  have hD := BstLean.Part36.DD_pos (d := d) hn
  rw [BstLean.Part53.sg, div_pow, one_pow, Real.sq_sqrt hD.le]

/-- `E X^j = ρ_j(𝒟)/𝒟^j`. -/
lemma radial_moment_eq63 (n d : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    ∫ Z, (MvPolynomial.eval Z (radialPoly n d (sg n d))) ^ j ∂stdGauss (CoefIdxD n d) =
      rhoD (DD n d) j / DD n d ^ j := by
  rw [radialPoly_moment63, pow_mul, sg_sq63 n d hn]
  change (1 / DD n d) ^ j * rhoD (DD n d) j = _
  rw [one_div_pow]; ring

/-- `E(X − 1)^m = Σ_{j ≤ m} (−1)^{m−j} C(m,j) ρ_j(𝒟)/𝒟^j`. -/
lemma centered_moment_eq63 (n d : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    ∫ Z, (MvPolynomial.eval Z (radialPoly n d (sg n d)) - 1) ^ m ∂stdGauss (CoefIdxD n d) =
      ∑ j ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ (m - j) * (m.choose j : ℝ) * (rhoD (DD n d) j / DD n d ^ j) := by
  have he (Z : CoefIdxD n d → ℝ) :
      (MvPolynomial.eval Z (radialPoly n d (sg n d)) - 1) ^ m =
        ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ (m - j) * (m.choose j : ℝ) *
          (MvPolynomial.eval Z (radialPoly n d (sg n d))) ^ j := by
    rw [sub_eq_add_neg, add_pow]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ => (gpow_int63 _ j).const_mul _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, radial_moment_eq63 n d hn j]

private lemma DD_ge_one63 (n d : ℕ) (hn : 1 ≤ n) : 1 ≤ DD n d := by
  rw [BstLean.Part36.DD_eq]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : (1 : ℝ) ≤ ((n + d).choose d : ℝ) := by
    exact_mod_cast (Nat.choose_pos (show d ≤ n + d by omega))
  nlinarith

/-- The exact constants `m_r = E(g² − 1)^{2r}`: `2, 60, 6040, 1190672`. -/
def mR63 : ℕ → ℝ
  | 1 => 2
  | 2 => 60
  | 3 => 6040
  | 4 => 1190672
  | _ => 0

/-- **Exact radial moments**, `r = 1, 2, 3, 4`: `E(X − 1)^{2r} ≤ m_r/𝒟^r`. -/
theorem centered_exact63 (n d : ℕ) (hn : 1 ≤ n) (r : ℕ) (hr1 : 1 ≤ r) (hr4 : r ≤ 4) :
    ∫ Z, (MvPolynomial.eval Z (radialPoly n d (sg n d)) - 1) ^ (2 * r) ∂stdGauss (CoefIdxD n d) ≤
      mR63 r / DD n d ^ r := by
  rw [centered_moment_eq63 n d hn]
  have hD1 := DD_ge_one63 n d hn
  have hD : 0 < DD n d := by linarith
  set D := DD n d with hDdef
  have h1 : 0 ≤ D - 1 := by linarith
  have hD2 : 0 ≤ D * (D - 1) := mul_nonneg hD.le h1
  have hD3 : 0 ≤ D ^ 2 * (D - 1) := mul_nonneg (by positivity) h1
  have hD4 : 0 ≤ D ^ 3 * (D - 1) := mul_nonneg (by positivity) h1
  have hD5 : 0 ≤ D * (D - 1) * (D - 1) := mul_nonneg hD2 h1
  have hD6 : 0 ≤ D ^ 2 * (D - 1) * (D - 1) := mul_nonneg hD3 h1
  interval_cases r
  · have hP : (0 : ℝ) ≤ 2 * D ^ 1 - (2 * D) := by nlinarith
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, rhoD, Finset.prod_range_succ,
      Finset.prod_range_zero, mR63]
    rw [← sub_nonneg]
    convert div_nonneg hP (pow_pos hD (2 * 1)).le using 1
    field_simp
    norm_num [Nat.choose]
    ring
  · have hP : (0 : ℝ) ≤ 60 * D ^ 2 - (12 * D ^ 2 + 48 * D) := by nlinarith
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, rhoD, Finset.prod_range_succ,
      Finset.prod_range_zero, mR63]
    rw [← sub_nonneg]
    convert div_nonneg hP (pow_pos hD (2 * 2)).le using 1
    field_simp
    norm_num [Nat.choose]
    ring
  · have hP : (0 : ℝ) ≤ 6040 * D ^ 3 - (120 * D ^ 3 + 2080 * D ^ 2 + 3840 * D) := by nlinarith
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, rhoD, Finset.prod_range_succ,
      Finset.prod_range_zero, mR63]
    rw [← sub_nonneg]
    convert div_nonneg hP (pow_pos hD (2 * 3)).le using 1
    field_simp
    norm_num [Nat.choose]
    ring
  · have hP : (0 : ℝ) ≤ 1190672 * D ^ 4 - (1680 * D ^ 4 + 76160 * D ^ 3 + 467712 * D ^ 2 + 645120 * D) := by nlinarith
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, rhoD, Finset.prod_range_succ,
      Finset.prod_range_zero, mR63]
    rw [← sub_nonneg]
    convert div_nonneg hP (pow_pos hD (2 * 4)).le using 1
    field_simp
    norm_num [Nat.choose]
    ring

/-- The doubling constants with the explicit fourth moment: `dbl 0 = B`,
`dbl (j+1) = Kexp(2^j h)·dbl(j)²`. -/
noncomputable def dbl63 (h : ℕ) (B : ℝ) : ℕ → ℝ
  | 0 => B
  | j + 1 => BstLean.Part62.Kexp (2 ^ j * h) * dbl63 h B j ^ 2

lemma dbl63_nonneg (h : ℕ) (B : ℝ) (hB : 0 ≤ B) (j : ℕ) : 0 ≤ dbl63 h B j := by
  induction j with
  | zero => exact hB
  | succ j ih =>
    simp only [dbl63]
    exact mul_nonneg (BstLean.Part62.Kexp_pos _).le (sq_nonneg _)

/-- Copy of `Part59.doubling_moment59x` with the explicit constant `dbl63`. -/
lemma doubling63 (h j : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∀ (ι : Type) [Fintype ι] (P : MvPolynomial ι ℝ),
      P.totalDegree ≤ h → (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ≤ B →
      (∫ z, (MvPolynomial.eval z P) ^ (2 ^ (j + 1)) ∂stdGauss ι) ≤ dbl63 h B j := by
  induction j with
  | zero => exact fun _ _ _ _ hb => by simpa [dbl63] using hb
  | succ j ih =>
    intro ι _ P hP hPb
    have hC := dbl63_nonneg h B hB j
    have hK := BstLean.Part62.Kexp_pos (2 ^ j * h)
    have hfour := BstLean.Part62.fourth_moment_explicit (2 ^ j * h)
    have hd : (P ^ (2 ^ j)).totalDegree ≤ 2 ^ j * h :=
      (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hP)
    have hf := hfour ι (P ^ (2 ^ j)) hd
    have hi := ih ι P hP hPb
    have hnn : 0 ≤ ∫ z, (MvPolynomial.eval z P) ^ (2 ^ (j + 1)) ∂stdGauss ι := by
      apply integral_nonneg
      intro z
      change 0 ≤ (MvPolynomial.eval z P) ^ (2 ^ (j + 1))
      rw [pow_succ, pow_mul]
      exact sq_nonneg _
    have he2 : 2 ^ j * 2 = 2 ^ (j + 1) := by simp [pow_succ]
    have he4 : 2 ^ j * 4 = 2 ^ (j + 1 + 1) := by simp [pow_succ]; omega
    simp only [map_pow, ← pow_mul, he2, he4] at hf
    simp only [dbl63]
    exact hf.trans (mul_le_mul_of_nonneg_left (by nlinarith :
      (∫ z, (MvPolynomial.eval z P) ^ (2 ^ (j + 1)) ∂stdGauss ι) ^ 2 ≤ dbl63 h B j ^ 2) hK.le)

private lemma even_power_le63 (x : ℝ) (r j : ℕ) (hr : 2 * r ≤ 2 ^ (j + 1)) :
    x ^ (2 * r) ≤ 1 + x ^ (2 ^ (j + 1)) := by
  have he : x ^ (2 ^ (j + 1)) = |x| ^ (2 ^ (j + 1)) := by
    rw [pow_succ, mul_comm, pow_mul, pow_mul, sq_abs]
  have her : x ^ (2 * r) = |x| ^ (2 * r) := by
    rw [pow_mul, pow_mul, sq_abs]
  rw [her, he]
  by_cases hx : |x| ≤ 1
  · have hl : |x| ^ (2 * r) ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
    exact hl.trans (le_add_of_nonneg_right (pow_nonneg (abs_nonneg _) _))
  · exact (pow_le_pow_right₀ (le_of_not_ge hx) hr).trans
      (le_add_of_nonneg_left (by norm_num))

/-- Copy of `Part59.polynomial_even_moment_bound59x` with the explicit constant `1 + dbl63 h B (2r)`. -/
lemma poly_even_moment63 (h r : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∀ (ι : Type) [Fintype ι] (P : MvPolynomial ι ℝ),
      P.totalDegree ≤ h → (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ≤ B →
      (∫ z, (MvPolynomial.eval z P) ^ (2 * r) ∂stdGauss ι) ≤ 1 + dbl63 h B (2 * r) := by
  intro ι _ P hP hPb
  have hi (a : ℕ) : Integrable (fun z => (MvPolynomial.eval z P) ^ a) (stdGauss ι) := by
    simpa only [map_pow] using BstLean.Part48.gauss_poly_integrable (P ^ a)
  have he : 2 * r ≤ 2 ^ (2 * r + 1) := by
    exact (Nat.le_succ _).trans (Nat.lt_two_pow_self).le
  calc
    _ ≤ ∫ z, (1 : ℝ) + (MvPolynomial.eval z P) ^ (2 ^ (2 * r + 1)) ∂stdGauss ι :=
      integral_mono (hi _) ((integrable_const 1).add (hi _))
        (fun z => even_power_le63 _ _ _ he)
    _ = 1 + ∫ z, (MvPolynomial.eval z P) ^ (2 ^ (2 * r + 1)) ∂stdGauss ι := by
      rw [integral_add (integrable_const 1) (hi _)]; simp
    _ ≤ 1 + dbl63 h B (2 * r) := add_le_add_right (doubling63 h (2 * r) B hB ι P hP hPb) _

private lemma radial_degree63 (n d : ℕ) :
    (radialPoly n d (sg n d)).totalDegree ≤ 2 := by
  classical
  unfold radialPoly
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a _
  apply (MvPolynomial.totalDegree_pow _ _).trans
  have hm := MvPolynomial.totalDegree_mul (MvPolynomial.C (sg n d)) (MvPolynomial.X a)
  simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add] at hm
  omega

/-- The general centered bound `E(X − 1)^{2r} ≤ (1 + dbl63 2 2 (2r))/𝒟^r` (copy of
`Part59.radial_centered_even_moment59x`, with `B = 2` from `centered_exact63` at `r = 1`). -/
lemma centered_general63 (r n d : ℕ) (hn : 1 ≤ n) :
    ∫ Z, (MvPolynomial.eval Z (radialPoly n d (sg n d)) - 1) ^ (2 * r) ∂stdGauss (CoefIdxD n d) ≤
      (1 + dbl63 2 2 (2 * r)) / DD n d ^ r := by
  let Q := radialPoly n d (sg n d) - 1
  let P := MvPolynomial.C (Real.sqrt (DD n d)) * Q
  have hD := BstLean.Part36.DD_pos (d := d) hn
  have hQ : Q.totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_sub_C_le _ 1).trans (radial_degree63 n d)
  have hP : P.totalDegree ≤ 2 := by
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa [P] using hQ)
  have hnorm : (∫ Z, (MvPolynomial.eval Z P) ^ 2 ∂stdGauss (CoefIdxD n d)) ≤ 2 := by
    simp only [P, map_mul, MvPolynomial.eval_C, mul_pow]
    rw [integral_const_mul, Real.sq_sqrt hD.le]
    have ht := centered_exact63 n d hn 1 le_rfl (by norm_num)
    simp only [mR63, pow_one, mul_one] at ht
    have ht' := (le_div_iff₀ hD).mp ht
    simpa [Q, mul_comm] using ht'
  have hbound := poly_even_moment63 2 r 2 (by norm_num) (CoefIdxD n d) P hP hnorm
  simp only [P, map_mul, MvPolynomial.eval_C, mul_pow] at hbound
  rw [integral_const_mul, pow_mul, Real.sq_sqrt hD.le] at hbound
  have he (Z : CoefIdxD n d → ℝ) :
      MvPolynomial.eval Z (radialPoly n d (sg n d)) - 1 = MvPolynomial.eval Z Q := by
    simp [Q]
  simp_rw [he]
  exact (le_div_iff₀ (pow_pos hD r)).mpr (by simpa [mul_comm] using hbound)

/-- **The radial moment constants**: exact `m_r` for `1 ≤ r ≤ 4`, the doubling bound otherwise. -/
noncomputable def CR63 (r : ℕ) : ℝ :=
  if 1 ≤ r ∧ r ≤ 4 then mR63 r else 1 + dbl63 2 2 (2 * r)

lemma CR63_nonneg (r : ℕ) : 0 ≤ CR63 r := by
  unfold CR63
  split_ifs with h
  · obtain ⟨h1, h4⟩ := h
    interval_cases r <;> norm_num [mR63]
  · have := dbl63_nonneg 2 2 (by norm_num) (2 * r); linarith

lemma centered63 (r n d : ℕ) (hn : 1 ≤ n) :
    ∫ Z, (MvPolynomial.eval Z (radialPoly n d (sg n d)) - 1) ^ (2 * r) ∂stdGauss (CoefIdxD n d) ≤
      CR63 r / DD n d ^ r := by
  unfold CR63
  split_ifs with h
  · exact centered_exact63 n d hn r h.1 h.2
  · exact centered_general63 r n d hn

/-- **Radial displacement moments with explicit constants**: `E(λ − 1)^{2r} ≤ CR63 r/𝒟^r`
(copy of `Part59.radial_displacement_even_moment59x`). -/
theorem radial_moment63 (r n d : ℕ) (hn : 1 ≤ n) :
    Integrable (fun Z => (lam59 n d Z - 1) ^ (2 * r)) (stdGauss (CoefIdxD n d)) ∧
      (∫ Z, (lam59 n d Z - 1) ^ (2 * r) ∂stdGauss (CoefIdxD n d)) ≤ CR63 r / DD n d ^ r := by
  have hbound := centered63 r n d hn
  have hi : Integrable (fun Z => (radialScale n d Z ^ 2 - 1) ^ (2 * r))
      (stdGauss (CoefIdxD n d)) := by
    have he (Z : CoefIdxD n d → ℝ) : radialScale n d Z ^ 2 - 1 =
        MvPolynomial.eval Z (radialPoly n d (sg n d) - 1) := by
      simp [radialScale_sq n d hn]
    simp_rw [he]
    exact gpow_int63 _ _
  have hbound' : (∫ Z, (radialScale n d Z ^ 2 - 1) ^ (2 * r) ∂stdGauss (CoefIdxD n d)) ≤
      CR63 r / DD n d ^ r := by
    simp_rw [radialScale_sq n d hn]; exact hbound
  have hdom (Z : CoefIdxD n d → ℝ) :
      (lam59 n d Z - 1) ^ (2 * r) ≤ (radialScale n d Z ^ 2 - 1) ^ (2 * r) := by
    have hl : 0 ≤ lam59 n d Z := radialScale_nonneg n d Z
    have hs : (lam59 n d Z - 1) ^ 2 ≤ (lam59 n d Z ^ 2 - 1) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (lam59 n d Z - 1))
        (add_nonneg (sq_nonneg (lam59 n d Z)) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hl))]
    change (lam59 n d Z - 1) ^ (2 * r) ≤ (lam59 n d Z ^ 2 - 1) ^ (2 * r)
    simpa only [pow_mul] using pow_le_pow_left₀ (sq_nonneg _) hs r
  have hc : Continuous (fun Z : CoefIdxD n d → ℝ => (lam59 n d Z - 1) ^ (2 * r)) :=
    ((radialScale_continuous n d).sub continuous_const).pow _
  have hir : Integrable (fun Z => (lam59 n d Z - 1) ^ (2 * r))
      (stdGauss (CoefIdxD n d)) := by
    apply hi.mono' hc.aestronglyMeasurable
    filter_upwards [] with Z
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hdom Z
    · rw [pow_mul]; positivity
  exact ⟨hir, (integral_mono hir hi hdom).trans hbound'⟩

end BstLean.Part63
