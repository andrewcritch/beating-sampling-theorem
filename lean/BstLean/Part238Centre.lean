import BstLean.Part238Network

/-! Part 238: the centre-projection lower bound `s₋` on the core input set, from the window
parameters alone. It discharges the latitude premise of the tangential gain. -/
namespace BstLean.Part238
open MeasureTheory Real Matrix Set
open BstLean.Part130 BstLean.Part182 BstLean.Part208
open BstLean.Part153 (nrm nrm_sq abs_dot_le_nrm)

/-- `s₋ = (a - τ t₀)² / (a² + 2 a τ t₀ + τ² (n + 2√(n z₀) + 2 z₀))`. -/
noncomputable def axialProjLower (n : ℕ) (a τ t0 z0 : ℝ) : ℝ :=
  (a - τ * t0) ^ 2 /
    (a ^ 2 + 2 * a * τ * t0 + τ ^ 2 * ((n : ℝ) + 2 * √((n : ℝ) * z0) + 2 * z0))

lemma dot_sphPt_sq {n : ℕ} (u y : Fin n → ℝ) (hy : normSq y ≠ 0) :
    (u ⬝ᵥ sphPt y) ^ 2 = (u ⬝ᵥ y) ^ 2 / normSq y := by
  have he : sphPt y = (1 / √(normSq y)) • y := by
    simp only [sphPt, hy, if_false]
    rfl
  rw [he, dotProduct_smul, smul_eq_mul, mul_pow, div_pow, one_pow,
    Real.sq_sqrt (normSq_nonneg _)]
  ring

lemma normSq_shift {n : ℕ} (u ξ : Fin n → ℝ) (a τ : ℝ) :
    normSq (a • u + τ • ξ) = a ^ 2 * normSq u + 2 * a * τ * (u ⬝ᵥ ξ) + τ ^ 2 * normSq ξ := by
  simp only [normSq, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The centre projection is bounded below on the core input set. -/
theorem centre_proj_lower {n : ℕ} {u : Fin n → ℝ} (hu : normSq u = 1) {a τ t0 z0 : ℝ}
    (ha : 0 < a) (hτ : 0 < τ) (hat : τ * t0 ≤ a) :
    ∀ ξ ∈ OmegaS (a • u) t0 z0,
      axialProjLower n a τ t0 z0 ≤ (u ⬝ᵥ sphPt (a • u + τ • ξ)) ^ 2 := by
  intro ξ hξ
  obtain ⟨hZ, -, hR⟩ := hξ
  rw [uC_smul_unit hu ha] at hZ
  set Z := u ⬝ᵥ ξ with hZd
  have hZlo := (abs_le.mp hZ).1
  have hZhi := (abs_le.mp hZ).2
  have hnum0 : 0 ≤ a - τ * t0 := by linarith
  have hlin : a - τ * t0 ≤ a + τ * Z := by nlinarith
  have hdot : u ⬝ᵥ (a • u + τ • ξ) = a + τ * Z := by
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, ms_dot_self, hu]
    simp [smul_eq_mul, hZd]
  have hN := normSq_shift u ξ a τ
  rw [hu, mul_one, ← hZd] at hN
  by_cases hy : normSq (a • u + τ • ξ) = 0
  · -- then `a + τ Z = 0`, so `a = τ t₀` and the bound is zero
    have hsq : (a + τ * Z) ^ 2 ≤ normSq (a • u + τ • ξ) := by
      have h := pow_le_pow_left₀ (abs_nonneg _) (abs_dot_le_nrm u (a • u + τ • ξ)) 2
      rw [sq_abs, mul_pow, nrm_sq, nrm_sq, hu, one_mul, hdot] at h
      exact h
    rw [hy] at hsq
    have h0 : a + τ * Z = 0 := by nlinarith [sq_nonneg (a + τ * Z)]
    have hnum : a - τ * t0 = 0 := by linarith
    unfold axialProjLower
    rw [hnum]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
    exact sq_nonneg _
  · rw [dot_sphPt_sq u _ hy, hdot]
    have hpos : 0 < normSq (a • u + τ • ξ) := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hy)
    have hD : normSq (a • u + τ • ξ) ≤
        a ^ 2 + 2 * a * τ * t0 + τ ^ 2 * ((n : ℝ) + 2 * √((n : ℝ) * z0) + 2 * z0) := by
      rw [hN]
      have h1 : 2 * a * τ * Z ≤ 2 * a * τ * t0 :=
        mul_le_mul_of_nonneg_left hZhi (by positivity)
      have h2 := mul_le_mul_of_nonneg_left hR (sq_nonneg τ)
      linarith
    unfold axialProjLower
    exact div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ hnum0 hlin 2) hpos hD

theorem axialProjLower_le_one (n : ℕ) {a τ t0 z0 : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (ht : 0 ≤ t0) (hz : 0 ≤ z0) (hat : τ * t0 ≤ a) : axialProjLower n a τ t0 z0 ≤ 1 := by
  unfold axialProjLower
  have hRp : 0 ≤ (n : ℝ) + 2 * √((n : ℝ) * z0) + 2 * z0 := by positivity
  have hτt : 0 ≤ τ * t0 := mul_nonneg hτ.le ht
  apply div_le_one_of_le₀ _ (by positivity)
  have h1 : τ * t0 * (τ * t0) ≤ τ * t0 * a := mul_le_mul_of_nonneg_left hat hτt
  have h2 := mul_nonneg (sq_nonneg τ) hRp
  nlinarith

/-- A nonzero centre is its norm times its unit direction. -/
lemma centre_decomp {n : ℕ} {c : Fin n → ℝ} (hc : c ≠ 0) :
    c = nrm c • uC c ∧ 0 < nrm c ∧ normSq (uC c) = 1 := by
  have hN : 0 < normSq c := by
    rcases (normSq_nonneg c).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hc
      funext i
      have hs : ∑ j, c j ^ 2 = 0 := h.symm
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j))).1 hs i
        (Finset.mem_univ i)
      simpa using this
  have hn : 0 < nrm c := Real.sqrt_pos.mpr hN
  refine ⟨?_, hn, ?_⟩
  · unfold uC
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  · unfold uC
    rw [normSq_smul, inv_pow, nrm_sq, inv_mul_cancel₀ hN.ne']

end BstLean.Part238
