import BstLean.Part246DS
import BstLean.Part208Gram

/-! Part 244: the centred Gram tail of a Gaussian matrix, from the Davidson–Szarek lower tail
(Gordon) and the Gordon upper tail. This is the singular-value step of the sharp E block of
Lemma `t7:p04:ti`, with the paper's `h = √d + υ`. -/
namespace BstLean.Part246
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 (normSq normSq_nonneg gaussMat normSq_smul)
open BstLean.Part152 (opN opN_nonneg mulVec_le_opN opN_tail')
open BstLean.Part153 (nrm nrm_nonneg nrm_sq)

/-- **Gaussian centred Gram tail.** For an `N × d` matrix with independent `N(0, v)` entries and
`υ ≥ 0`, put `h = √d + υ + 2/√N`. Except with probability `2 e^{-υ²/2}`,
`|⟨Gp, Gq⟩ - v N ⟨p, q⟩| ≤ v (2 √N h + h²) |p| |q|` for all `p`, `q`. -/
theorem gaussian_gram_tail {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) {v υ : ℝ} (hv : 0 < v)
    (hυ : 0 ≤ υ) :
    (gaussMat N d v).real {G | ¬ ∀ p q : Fin d → ℝ,
      |(G *ᵥ p) ⬝ᵥ (G *ᵥ q) - v * N * (p ⬝ᵥ q)| ≤
        v * (2 * √(N : ℝ) * (√(d : ℝ) + υ) +
          (√(d : ℝ) + υ) ^ 2) * √(normSq p) * √(normSq q)} ≤
      2 * exp (-υ ^ 2 / 2) := by
  haveI : IsProbabilityMeasure (gaussMat N d v) := by unfold gaussMat; infer_instance
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set h := √(d : ℝ) + υ with hhd
  have hh : 0 ≤ h := by positivity
  set Lo := {G : Matrix (Fin N) (Fin d) ℝ | ∃ x : Fin d → ℝ, normSq x = 1 ∧
    nrm (G *ᵥ x) < √v * (√(N : ℝ) - √(d : ℝ) - √(2 * (υ ^ 2 / 2)))} with hLo
  set Hi := {G : Matrix (Fin N) (Fin d) ℝ | √v * (√(N : ℝ) + √(d : ℝ) + υ) ≤ opN G} with hHi
  have hsub : {G : Matrix (Fin N) (Fin d) ℝ | ¬ ∀ p q : Fin d → ℝ,
      |(G *ᵥ p) ⬝ᵥ (G *ᵥ q) - v * N * (p ⬝ᵥ q)| ≤
        v * (2 * √(N : ℝ) * h + h ^ 2) * √(normSq p) * √(normSq q)} ⊆ Lo ∪ Hi := by
    intro G hG
    by_contra hno
    simp only [Set.mem_union, not_or, hLo, hHi, Set.mem_setOf_eq, not_exists, not_and,
      not_lt, not_le] at hno
    obtain ⟨hlo, hhi⟩ := hno
    apply hG
    have hs2 : √(2 * (υ ^ 2 / 2)) = υ := by
      rw [show 2 * (υ ^ 2 / 2) = υ ^ 2 by ring, Real.sqrt_sq hυ]
    refine BstLean.Part208.gram_from_singular_bounds G hv.le hNR.le hh (fun z => ?_) (fun z => ?_)
    · by_cases hz : normSq z = 0
      · rw [hz, Real.sqrt_zero, mul_zero]; exact Real.sqrt_nonneg _
      · have hzp : 0 < √(normSq z) := Real.sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg z) (Ne.symm hz))
        set x := (√(normSq z))⁻¹ • z with hx
        have hx1 : normSq x = 1 := by
          rw [hx, normSq_smul, inv_pow, Real.sq_sqrt (normSq_nonneg z), inv_mul_cancel₀ hz]
        have h1 := hlo x hx1
        rw [hs2] at h1
        have hGx : nrm (G *ᵥ x) * √(normSq z) = √(normSq (G *ᵥ z)) := by
          have e : G *ᵥ z = √(normSq z) • (G *ᵥ x) := by
            rw [hx, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hzp.ne', one_smul]
          rw [e, normSq_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hzp.le]
          unfold nrm; ring
        rw [← hGx]
        refine mul_le_mul_of_nonneg_right ?_ hzp.le
        have hle : √v * max (√(N : ℝ) - h) 0 ≤ nrm (G *ᵥ x) := by
          rcases le_total (√(N : ℝ) - h) 0 with hc | hc
          · rw [max_eq_right hc, mul_zero]; exact nrm_nonneg _
          · rw [max_eq_left hc]
            have : √(N : ℝ) - h = √(N : ℝ) - √(d : ℝ) - υ := by rw [hhd]; ring
            rw [this]; exact h1
        exact hle
    · have h1 := mulVec_le_opN G z
      have h2 : opN G < √v * (√(N : ℝ) + √(d : ℝ) + υ) := hhi
      have h2N : 0 ≤ 2 / √(N : ℝ) := by positivity
      have h3 : √v * (√(N : ℝ) + √(d : ℝ) + υ) ≤ √v * (√(N : ℝ) + h) :=
        mul_le_mul_of_nonneg_left (by rw [hhd]; linarith) (Real.sqrt_nonneg v)
      have h4 : opN G * √(normSq z) ≤ √v * (√(N : ℝ) + h) * √(normSq z) :=
        mul_le_mul_of_nonneg_right (h2.le.trans h3) (Real.sqrt_nonneg _)
      exact h1.trans h4
  have hLoP : (gaussMat N d v).real Lo ≤ exp (-(υ ^ 2 / 2)) :=
    minStretch_tail_DS hN hd hv (by positivity)
  have hHiP : (gaussMat N d v).real Hi ≤ exp (-υ ^ 2 / 2) := opN_tail' hv hυ
  have e : exp (-(υ ^ 2 / 2)) = exp (-υ ^ 2 / 2) := by ring_nf
  rw [e] at hLoP
  calc _ ≤ (gaussMat N d v).real (Lo ∪ Hi) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (gaussMat N d v).real Lo + (gaussMat N d v).real Hi := measureReal_union_le _ _
    _ ≤ 2 * exp (-υ ^ 2 / 2) := by linarith

end BstLean.Part246
