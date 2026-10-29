import BstLean.Part167Conc

/-! The transverse Gaussian vector has an order-160 moment bound. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part148 (EuLip)
open BstLean.Part153 (nrm nrm_nonneg)
open BstLean.Part167
variable {n m : ℕ}

theorem transverse_moment160 (a : Fin n → ℝ) (B : Matrix (Fin n) (Fin m) ℝ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ z, nrm (B *ᵥ z) ≤ L * nrm z) :
    ∫⁻ γ, ENNReal.ofReal (nrm (a + B *ᵥ γ) ^ 160) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal ((√(normSq a + ∑ i, ∑ j, B i j ^ 2) +
        BstLean.Part152.gaussMomConst 80 * L) ^ 160) := by
  set f : (Fin m → ℝ) → ℝ := fun γ => nrm (a + B *ᵥ γ) with hf
  have hlip : EuLip f L := by
    intro x y
    have h1 : |f x - f y| ≤ nrm ((a + B *ᵥ x) - (a + B *ᵥ y)) := by
      have := BstLean.Part153.nrm_tri3 (a + B *ᵥ x) (a + B *ᵥ y)
      have := BstLean.Part153.nrm_tri3 (a + B *ᵥ y) (a + B *ᵥ x)
      have e : nrm ((a + B *ᵥ y) - (a + B *ᵥ x)) = nrm ((a + B *ᵥ x) - (a + B *ᵥ y)) := by
        unfold nrm normSq; congr 1; exact Finset.sum_congr rfl fun i _ => by
          simp only [Pi.sub_apply]; ring
      rw [abs_le]; constructor <;> linarith
    have e2 : (a + B *ᵥ x) - (a + B *ᵥ y) = B *ᵥ (x - y) := by
      rw [Matrix.mulVec_sub]; abel
    rw [e2] at h1
    refine h1.trans ((hL _).trans (le_of_eq ?_))
    rfl
  obtain ⟨hI2, hE2⟩ := sec_mom a B
  set V := normSq a + ∑ i, ∑ j, B i j ^ 2 with hV
  have hV0 : 0 ≤ V := add_nonneg (normSq_nonneg a)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hfi : Integrable f (stdGauss (Fin m)) :=
    (BstLean.Part151.lip_memLp hL0 hlip).integrable one_le_two
  set E := ∫ γ, f γ ∂stdGauss (Fin m) with hEdef
  -- `E f ≤ √V` (Jensen)
  have hEle : E ≤ √V := by
    have hE0 : 0 ≤ E := integral_nonneg fun γ => nrm_nonneg _
    have hsq : E ^ 2 ≤ V := by
      have hJ := (convexOn_pow 2).map_integral_le (μ := stdGauss (Fin m)) (f := f)
        (continuous_pow 2).continuousOn isClosed_Ici
        (Filter.Eventually.of_forall fun γ => Set.mem_Ici.mpr (nrm_nonneg _)) hfi
        (by
          have : (fun γ => f γ ^ 2) = fun γ => normSq (a + B *ᵥ γ) := by
            funext γ; simp only [hf, nrm]; rw [Real.sq_sqrt (normSq_nonneg _)]
          simp only [Function.comp_def]; rw [this]; exact hI2)
      try simp only [Function.comp_def] at hJ
      have : (fun γ => f γ ^ 2) = fun γ => normSq (a + B *ᵥ γ) := by
        funext γ; simp only [hf, nrm]; rw [Real.sq_sqrt (normSq_nonneg _)]
      rw [this, hE2] at hJ
      exact hJ
    exact Real.le_sqrt_of_sq_le hsq
  have hE0 : 0 ≤ E := integral_nonneg fun γ => nrm_nonneg _
  have hm : Measurable f := (hlip.continuous hL0).measurable
  obtain ⟨hYi, hYb⟩ := BstLean.Part152.gaussConc_moment hL0 hlip 80
  have hB0 : 0 ≤ BstLean.Part152.gaussMomConst 80 * L :=
    mul_nonneg (BstLean.Part152.gaussMomConst_nonneg _) hL0
  have hYpow : ∫ γ, max (f γ - E) 0 ^ 160 ∂stdGauss (Fin m) ≤
      (BstLean.Part152.gaussMomConst 80 * L) ^ 160 := by
    refine hYb.trans (le_of_eq ?_)
    rw [mul_pow, BstLean.Part152.gaussMomConst_pow (by norm_num : 1 ≤ (80 : ℕ))]
    ring
  obtain ⟨hI, hM⟩ := BstLean.Part152.moment_shift hm
    ((hm.sub_const E).max measurable_const) (fun γ => nrm_nonneg _)
    (fun γ => le_max_right _ _) hE0
    (fun γ => by have := le_max_left (f γ - E) 0; linarith)
    (by norm_num : 1 ≤ (80 : ℕ)) hB0 hYi hYpow
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (ae_of_all _ fun γ => pow_nonneg (nrm_nonneg _) _)]
  exact ENNReal.ofReal_le_ofReal (hM.trans
    (pow_le_pow_left₀ (add_nonneg hE0 hB0) (by linarith [hEle]) 160))
end BstLean.Part212
