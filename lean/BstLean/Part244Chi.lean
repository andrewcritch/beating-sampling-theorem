import BstLean.Part244Smin
import BstLean.Part107WickA

/-! Part 244: the Gaussian norm mean `a_N ≥ N/√(N+2)`, the explicit Davidson–Szarek mean bound,
and its lower tail with the Gaussian concentration of Part 208. -/
namespace BstLean.Part244
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg gaussMat)
open BstLean.Part152 (coord_sq)
open BstLean.Part153 (nrm nrm_nonneg)
open BstLean.Part208 (minStretch gaussian_minStretch_deviation)

/-- `r(r - t)²(r + 2t) ≥ 0` in the form used for the norm mean. -/
lemma poly_lower {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) :
    (3 * t ^ 2 * r ^ 2 - (r ^ 2) ^ 2) / (2 * t ^ 3) ≤ r := by
  rw [div_le_iff₀ (by positivity)]
  have h : 0 ≤ r * (r - t) ^ 2 * (r + 2 * t) := by positivity
  nlinarith [h]

/-- **The Gaussian norm mean.** `E|g_N| ≥ N/√(N+2)`. -/
theorem gaussNormMean_ge (N : ℕ) : (N : ℝ) / √((N : ℝ) + 2) ≤ gaussNormMean N := by
  classical
  set t := √((N : ℝ) + 2) with htd
  have ht : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have ht2 : t ^ 2 = (N : ℝ) + 2 := Real.sq_sqrt (by positivity)
  have i2 : Integrable (fun z : Fin N → ℝ => ∑ i, z i ^ 2) (stdGauss (Fin N)) :=
    integrable_finsetSum _ fun i _ => (coord_sq i).1
  have i4 : Integrable (fun z : Fin N → ℝ => (∑ i, z i ^ 2) ^ 2) (stdGauss (Fin N)) := by
    have e : (fun z : Fin N → ℝ => (∑ i, z i ^ 2) ^ 2) =
        fun z => ∑ i, ∑ j, z i * z i * z j * z j := by
      funext z
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      BstLean.Part107.int4 i i j j
  have iP : Integrable (fun z : Fin N → ℝ =>
      (3 * t ^ 2 * (∑ i, z i ^ 2) - (∑ i, z i ^ 2) ^ 2) / (2 * t ^ 3)) (stdGauss (Fin N)) :=
    ((i2.const_mul _).sub i4).div_const _
  have hpt : ∀ z : Fin N → ℝ,
      (3 * t ^ 2 * (∑ i, z i ^ 2) - (∑ i, z i ^ 2) ^ 2) / (2 * t ^ 3) ≤ nrm z := by
    intro z
    have h := poly_lower (nrm_nonneg z) ht
    rwa [BstLean.Part153.nrm_sq] at h
  have hm := integral_mono iP nrm_integrable hpt
  have e1 : ∫ z : Fin N → ℝ, (3 * t ^ 2 * (∑ i, z i ^ 2) - (∑ i, z i ^ 2) ^ 2) / (2 * t ^ 3)
      ∂stdGauss (Fin N) = (3 * t ^ 2 * N - N * (N + 2)) / (2 * t ^ 3) := by
    rw [integral_div, integral_sub (i2.const_mul _) i4, integral_const_mul,
      BstLean.Part107.normSq_mom1, BstLean.Part107.normSq_mom2, Fintype.card_fin]
  rw [e1] at hm
  unfold gaussNormMean
  refine le_trans (le_of_eq ?_) hm
  rw [ht2]
  have ht3 : t ^ 3 = ((N : ℝ) + 2) * t := by rw [pow_succ, ht2]
  rw [ht3]
  field_simp
  ring

/-- **Davidson–Szarek mean bound (explicit).** `E s_min ≥ √v (N/√(N+2) - √d)`. -/
theorem minStretch_mean_explicit {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) {v : ℝ} (hv : 0 ≤ v) :
    √v * ((N : ℝ) / √((N : ℝ) + 2) - √(d : ℝ)) ≤ ∫ M, minStretch M ∂gaussMat N d v :=
  le_trans (mul_le_mul_of_nonneg_left (by linarith [gaussNormMean_ge N]) (Real.sqrt_nonneg v))
    (minStretch_mean_ge hN hd hv)

/-- `N/√(N+2) ≥ √N - 2/√N`: the correction to the paper's `√N` is at most `2/√N`. -/
theorem sqrt_sub_le_mean_lower {N : ℕ} (hN : 1 ≤ N) :
    √(N : ℝ) - 2 / √(N : ℝ) ≤ (N : ℝ) / √((N : ℝ) + 2) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 0 < √(N : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : √(N : ℝ) ^ 2 = N := Real.sq_sqrt (by linarith)
  have ht : 0 < √((N : ℝ) + 2) := Real.sqrt_pos.mpr (by linarith)
  have ht2 : √((N : ℝ) + 2) ^ 2 = N + 2 := Real.sq_sqrt (by linarith)
  -- `√(N+2) ≤ √N + 1/√N`
  have hup : √((N : ℝ) + 2) ≤ √(N : ℝ) + 1 / √(N : ℝ) := by
    rw [Real.sqrt_le_left]
    · have : (√(N : ℝ) + 1 / √(N : ℝ)) ^ 2 = N + 2 + 1 / N := by
        field_simp; rw [hs2]; ring
      rw [this]
      have : (0 : ℝ) ≤ 1 / N := by positivity
      linarith
    · positivity
  rw [le_div_iff₀ ht]
  have h1 : (√(N : ℝ) - 2 / √(N : ℝ)) * √((N : ℝ) + 2) ≤
      (√(N : ℝ) - 2 / √(N : ℝ)) * (√(N : ℝ) + 1 / √(N : ℝ)) ∨
      √(N : ℝ) - 2 / √(N : ℝ) < 0 := by
    by_cases h : 0 ≤ √(N : ℝ) - 2 / √(N : ℝ)
    · exact Or.inl (mul_le_mul_of_nonneg_left hup h)
    · exact Or.inr (lt_of_not_ge h)
  rcases h1 with h1 | h1
  · have e : (√(N : ℝ) - 2 / √(N : ℝ)) * (√(N : ℝ) + 1 / √(N : ℝ)) = N - 1 - 2 / N := by
      field_simp; rw [hs2]; ring
    rw [e] at h1
    have : (0 : ℝ) ≤ 2 / N := by positivity
    linarith
  · have : (√(N : ℝ) - 2 / √(N : ℝ)) * √((N : ℝ) + 2) < 0 := mul_neg_of_neg_of_pos h1 ht
    linarith [(by positivity : (0 : ℝ) ≤ N)]

/-- **Davidson–Szarek lower tail (Gordon + Gaussian concentration).** For an `N × d` matrix with
independent `N(0, v)` entries, `s_min ≥ √v (N/√(N+2) - √d - √(2τ))` except with probability
`e^{-τ}`. -/
theorem minStretch_tail {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) {v τ : ℝ} (hv : 0 < v)
    (hτ : 0 ≤ τ) :
    (gaussMat N d v).real {G | ∃ x : Fin d → ℝ, normSq x = 1 ∧
      nrm (G *ᵥ x) < √v * ((N : ℝ) / √((N : ℝ) + 2) - √(d : ℝ) - √(2 * τ))} ≤ exp (-τ) := by
  haveI : IsProbabilityMeasure (gaussMat N d v) := by unfold gaussMat; infer_instance
  have hmean := minStretch_mean_explicit hN hd hv.le
  refine (measureReal_mono (s₂ := {G | ∃ x : Fin d → ℝ, normSq x = 1 ∧
    nrm (G *ᵥ x) < (∫ M, minStretch M ∂gaussMat N d v) - √v * √(2 * τ)})
      ?_ (measure_ne_top _ _)).trans (gaussian_minStretch_deviation hd hv hτ)
  rintro G ⟨x, hx, hbad⟩
  exact ⟨x, hx, hbad.trans_le (by nlinarith only [hmean])⟩

/-- The same tail with the paper's form `√v (√N - √d - υ)`, corrected by `2√v/√N`. -/
theorem minStretch_tail_paper {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) {v τ : ℝ} (hv : 0 < v)
    (hτ : 0 ≤ τ) :
    (gaussMat N d v).real {G | ∃ x : Fin d → ℝ, normSq x = 1 ∧
      nrm (G *ᵥ x) < √v * (√(N : ℝ) - 2 / √(N : ℝ) - √(d : ℝ) - √(2 * τ))} ≤ exp (-τ) := by
  haveI : IsProbabilityMeasure (gaussMat N d v) := by unfold gaussMat; infer_instance
  refine (measureReal_mono (fun G hG => ?_) (measure_ne_top _ _)).trans
    (minStretch_tail hN hd hv hτ)
  obtain ⟨x, hx, hbad⟩ := hG
  refine ⟨x, hx, hbad.trans_le ?_⟩
  have h := sqrt_sub_le_mean_lower hN
  exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg v)

end BstLean.Part244
