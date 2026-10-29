import BstLean.Part56MC_WickSpan
import BstLean.Part56MC_Spectral

namespace BstLean.Part56

open MeasureTheory
open BstLean.Part29 (stdGauss)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def mc56_wordLp (w : List ι) : Lp ℝ 2 (stdGauss ι) :=
  mc56_polynomialToLp (mc56_wickWord w)

private noncomputable def chaos (k : ℕ) : Submodule ℝ (Lp ℝ 2 (stdGauss ι)) :=
  Submodule.span ℝ {x | ∃ w : List ι, w.length = k ∧ mc56_wordLp w = x}

theorem mc56_polynomial_inner (p q : MvPolynomial ι ℝ) :
    inner ℝ (mc56_polynomialToLp p) (mc56_polynomialToLp q) =
      ∫ x, MvPolynomial.eval x p * MvPolynomial.eval x q ∂stdGauss ι := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(mc56_polynomial_memLp p).coeFn_toLp,
    (mc56_polynomial_memLp q).coeFn_toLp] with x hp hq
  change mc56_polynomialToLp q x * mc56_polynomialToLp p x = _
  change mc56_polynomialToLp p x = _ at hp
  change mc56_polynomialToLp q x = _ at hq
  rw [hp, hq]
  exact mul_comm _ _

private theorem chaos_orthogonal :
    OrthogonalFamily ℝ (fun k => chaos (ι := ι) k) (fun k => (chaos k).subtypeₗᵢ) := by
  intro k l hkl x y
  change inner ℝ (x : Lp ℝ 2 (stdGauss ι)) (y : Lp ℝ 2 (stdGauss ι)) = 0
  have hx := x.property
  have hy := y.property
  generalize hxv : (x : Lp ℝ 2 (stdGauss ι)) = xv at hx ⊢
  generalize hyv : (y : Lp ℝ 2 (stdGauss ι)) = yv at hy ⊢
  clear hxv hyv
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, hv, rfl⟩ := hy
      rw [mc56_wordLp, mc56_wordLp, mc56_polynomial_inner]
      exact mc56_wickWord_orthogonal w v (by simpa [hw, hv] using hkl)
    | zero => simp
    | add p q hp hq ihp ihq => simp only [inner_add_right, ihp, ihq, add_zero]
    | smul r p hp ih => simp only [inner_smul_right, ih, mul_zero]
  | zero => simp
  | add p q hp hq ihp ihq => simp only [inner_add_left, ihp, ihq, add_zero]
  | smul r p hp ih => simp only [inner_smul_left, ih, mul_zero]

private theorem chaos_dense : (⨆ k, chaos (ι := ι) k).topologicalClosure = ⊤ := by
  have hle : LinearMap.range (mc56_polynomialToLp (ι := ι)) ≤ ⨆ k, chaos k := by
    rintro _ ⟨p, rfl⟩
    have hp : p ∈ Submodule.span ℝ (Set.range (mc56_wickWord (ι := ι))) := by
      rw [mc56_wickWord_span]; trivial
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨w, rfl⟩ := hp
      exact (le_iSup (fun k => chaos k) w.length)
        (Submodule.subset_span ⟨w, rfl, rfl⟩)
    | zero => simp
    | add p q hp hq ihp ihq => simpa only [map_add] using (⨆ k, chaos k).add_mem ihp ihq
    | smul r p hp ih => simpa only [map_smul] using (⨆ k, chaos k).smul_mem r ih
  apply top_unique
  rw [← mc56_polynomials_dense (ι := ι)]
  exact Submodule.topologicalClosure_mono hle

theorem mc56_word_diagonal_bound (T : Lp ℝ 2 (stdGauss ι) →L[ℝ] Lp ℝ 2 (stdGauss ι))
    (eig : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (heigen : ∀ w : List ι, T (mc56_wordLp w) = eig w.length • mc56_wordLp w)
    (heig : ∀ k, |eig k| ≤ C) : ∀ F, ‖T F‖ ≤ C * ‖F‖ := by
  apply mc56_diagonal_bound T chaos eig C hC chaos_orthogonal chaos_dense _ heig
  intro k x
  have hx := x.property
  generalize hxv : (x : Lp ℝ 2 (stdGauss ι)) = xv at hx ⊢
  clear hxv
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨w, hw, rfl⟩ := hx; simpa only [hw] using heigen w
  | zero => simp
  | add p q hp hq ihp ihq => simp only [map_add, ihp, ihq, smul_add]
  | smul r p hp ih => rw [map_smul, ih, smul_comm]

end BstLean.Part56
