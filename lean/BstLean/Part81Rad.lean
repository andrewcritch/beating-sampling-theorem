import BstLean.Part81Defs
import BstLean.Part81Bridge
import BstLean.Part63RadMom

/-!
# Part 81, radius tail from the eighth moment

* `Rad.eighth`: `E (‖Z‖²/𝒟 − 1)⁸ ≤ 1700/𝒟⁴` for `𝒟 ≥ 4000`.
* `radTail8`: `P(|‖Z‖²/𝒟 − 1| > δ) ≤ 1700/(𝒟⁴ δ⁸)` for `𝒟 ≥ 4000`.
-/

namespace BstLean.Part81.Rad

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD rhoD)
open BstLean.Part78 (Good good_coord)

lemma hev (n d : ℕ) (hn : 1 ≤ n) (Z : CoefIdxD n d → ℝ) :
    MvPolynomial.eval Z (BstLean.Part53.T2Aux.radialPoly n d (BstLean.Part53.sg n d)) =
      (∑ α, Z α ^ 2) / DD n d := by
  have hD : 0 < DD n d := BstLean.Part36.DD_pos hn
  have hs : (BstLean.Part53.sg n d) ^ 2 = 1 / DD n d := by
    rw [BstLean.Part53.sg, div_pow, one_pow, Real.sq_sqrt hD.le]
  simp only [BstLean.Part53.T2Aux.radialPoly, map_sum, map_pow, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, mul_pow, hs]
  rw [← Finset.mul_sum]; ring

/-- `E (X − 1)⁸ ≤ 1700/𝒟⁴` for `𝒟 ≥ 4000`. -/
lemma eighth (n d : ℕ) (hn : 1 ≤ n) (hD4 : 4000 ≤ DD n d) :
    ∫ Z, ((∑ α, Z α ^ 2) / DD n d - 1) ^ 8 ∂stdGauss (CoefIdxD n d) ≤ 1700 / DD n d ^ 4 := by
  have h := BstLean.Part63.centered_moment_eq63 n d hn 8
  simp only [hev n d hn] at h
  rw [h]
  have hD : 0 < DD n d := by linarith
  set D := DD n d with hDdef
  have hP : (0 : ℝ) ≤ 1700 * D ^ 4 -
      (1680 * D ^ 4 + 76160 * D ^ 3 + 467712 * D ^ 2 + 645120 * D) := by
    have h1 : 0 ≤ D ^ 3 * (D - 4000) := mul_nonneg (by positivity) (by linarith)
    have h2 : 0 ≤ D ^ 2 * (D - 4000) := mul_nonneg (by positivity) (by linarith)
    have h3 : 0 ≤ D * (D - 4000) := mul_nonneg (by positivity) (by linarith)
    nlinarith
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, rhoD, Finset.prod_range_succ,
    Finset.prod_range_zero]
  rw [← sub_nonneg]
  convert div_nonneg hP (pow_pos hD 8).le using 1
  field_simp
  norm_num [Nat.choose]
  ring

end BstLean.Part81.Rad

namespace BstLean.Part81

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD)
open BstLean.Part78 (Good good_coord markov_gt)

/-- **Radius tail from the eighth moment**: `P(|‖Z‖²/𝒟 − 1| > δ) ≤ 1700/(𝒟⁴ δ⁸)`, `𝒟 ≥ 4000`. -/
theorem radTail8 (n d : ℕ) (hn : 1 ≤ n) (hD : 4000 ≤ BstLean.Part36.DD n d) (δ : ℝ) (hδ : 0 < δ) :
    stdGauss (CoefIdxD n d) {Z | δ ^ 2 < ((∑ α, Z α ^ 2) / BstLean.Part36.DD n d - 1) ^ 2} ≤
      ENNReal.ofReal (1700 / BstLean.Part36.DD n d ^ 4 / δ ^ 8) := by
  have hB := Rad.eighth n d hn hD
  have hgood : Good (stdGauss (CoefIdxD n d))
      (fun Z : CoefIdxD n d → ℝ => ((∑ α, Z α ^ 2) / BstLean.Part36.DD n d - 1) ^ 8) := by
    have h1 : Good (stdGauss (CoefIdxD n d)) (fun Z : CoefIdxD n d → ℝ => ∑ α, Z α ^ 2) :=
      Good.sum _ fun α _ => (good_coord α).pow 2
    have h2 := ((h1.mul_const (1 / BstLean.Part36.DD n d)).sub (Good.const 1)).pow 8
    have h3 : (fun Z : CoefIdxD n d → ℝ => ((∑ α, Z α ^ 2) / BstLean.Part36.DD n d - 1) ^ 8) =
        fun Z => ((∑ α, Z α ^ 2) * (1 / BstLean.Part36.DD n d) - 1) ^ 8 := by
      funext Z; ring
    rw [h3]; exact h2
  have hmk := markov_gt (μ := stdGauss (CoefIdxD n d))
    (f := fun Z : CoefIdxD n d → ℝ => ((∑ α, Z α ^ 2) / BstLean.Part36.DD n d - 1) ^ 8)
    (fun Z => by
      have : ((∑ α, Z α ^ 2) / BstLean.Part36.DD n d - 1) ^ 8 =
        (((∑ α, Z α ^ 2) / BstLean.Part36.DD n d - 1) ^ 4) ^ 2 := by ring
      rw [this]; exact sq_nonneg _)
    hgood.integrable (t := δ ^ 8) (by positivity) hB
  refine (measure_mono ?_).trans hmk
  intro Z hZ
  simp only [Set.mem_ofPred_eq] at hZ ⊢
  have h := pow_lt_pow_left₀ hZ (sq_nonneg δ) (by norm_num : (4 : ℕ) ≠ 0)
  calc δ ^ 8 = (δ ^ 2) ^ 4 := by ring
    _ < (((∑ α, Z α ^ 2) / BstLean.Part36.DD n d - 1) ^ 2) ^ 4 := h
    _ = _ := by ring

end BstLean.Part81

#print axioms BstLean.Part81.radTail8
