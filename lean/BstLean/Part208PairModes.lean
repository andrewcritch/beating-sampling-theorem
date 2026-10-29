import BstLean.Part182MS

/-! Part 208: retain the tangent factors before integration. -/
namespace BstLean.Part208
open Real Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part182
open BstLean.Part153 (nrm nrm_nonneg nrm_sq abs_dot_le_nrm)
variable {m n : ℕ}

/-- The three TI blocks give four bilinear modes with their tangent components intact. -/
theorem pair_four_modes {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    (hc : (x ⬝ᵥ x') ^ 2 < 1) (J J' : Matrix (Fin m) (Fin n) ℝ) {KE KO KS : ℝ}
    (hE0 : 0 ≤ KE) (hO0 : 0 ≤ KO) (hS0 : 0 ≤ KS)
    (hE : opN (PEm x x' * (Jᵀ * J') * PEm x x') ≤ KE)
    (hO1 : nrm (PEm x x' *ᵥ ((Jᵀ * J') *ᵥ eTan x' x)) ≤ KO)
    (hO2 : nrm (PEm x x' *ᵥ ((J'ᵀ * J) *ᵥ eTan x x')) ≤ KO)
    (hS : |(J *ᵥ eTan x x') ⬝ᵥ (J' *ᵥ eTan x' x)| ≤ KS)
    {f f' : Fin n → ℝ} (hxf : x ⬝ᵥ f = 0) (hxf' : x' ⬝ᵥ f' = 0) :
    |(J *ᵥ f) ⬝ᵥ (J' *ᵥ f')| ≤
      KE * nrm f * nrm f' +
      KO * (|eTan x x' ⬝ᵥ f| * nrm f' + nrm f * |eTan x' x ⬝ᵥ f'|) +
      KS * |eTan x x' ⬝ᵥ f| * |eTan x' x ⬝ᵥ f'| := by
  have hc' : (x' ⬝ᵥ x) ^ 2 < 1 := by rw [dotProduct_comm]; exact hc
  have e1 := eTan_dot_x hx hx' hc
  have e2 := eTan_dot_self hx hx' hc
  have e1' := eTan_dot_x hx' hx hc'
  have e2' := eTan_dot_self hx' hx hc'
  have hf : f = PEm x x' *ᵥ f + (eTan x x' ⬝ᵥ f) • eTan x x' := by
    rw [PEm_mulVec, hxf]; simp
  have hf' : f' = PEm x x' *ᵥ f' + (eTan x' x ⬝ᵥ f') • eTan x' x := by
    rw [PEm_alt hx hx' hc, hxf']; simp
  have hPe' : eTan x' x ⬝ᵥ (PEm x x' *ᵥ f') = 0 := by
    rw [PEm_alt hx hx' hc]
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, e1', e2']; ring
  have hPe : eTan x x' ⬝ᵥ (PEm x x' *ᵥ f) = 0 := ms_PE_dot_e x x' f e1 e2
  have hN : normSq f = normSq (PEm x x' *ᵥ f) + (eTan x x' ⬝ᵥ f) ^ 2 := by
    rw [← ms_pyth _ _ _ hPe e2, ← hf]
  have hN' : normSq f' = normSq (PEm x x' *ᵥ f') + (eTan x' x ⬝ᵥ f') ^ 2 := by
    rw [← ms_pyth _ _ _ hPe' e2', ← hf']
  have hPα : PEm x x' *ᵥ (PEm x x' *ᵥ f) = PEm x x' *ᵥ f := PEm_idem hx hx' hc f
  have hPα' : PEm x x' *ᵥ (PEm x x' *ᵥ f') = PEm x x' *ᵥ f' := PEm_idem hx hx' hc f'
  generalize PEm x x' *ᵥ f = α at hf hN hPe hPα
  generalize PEm x x' *ᵥ f' = α' at hf' hN' hPe' hPα'
  have T1 : |(J *ᵥ α) ⬝ᵥ (J' *ᵥ α')| ≤ KE * (nrm α * nrm α') := by
    rw [ms_bil]
    have : α ⬝ᵥ (Jᵀ * J') *ᵥ α' = α ⬝ᵥ (PEm x x' * (Jᵀ * J') * PEm x x') *ᵥ α' := by
      rw [show (PEm x x' * (Jᵀ * J') * PEm x x') *ᵥ α' =
          PEm x x' *ᵥ ((Jᵀ * J') *ᵥ (PEm x x' *ᵥ α')) by rw [mulVec_mulVec, mulVec_mulVec],
        hPα', ← PEm_symm, hPα]
    rw [this]
    exact (ms_abs_bil_le_opN _ _ _).trans (mul_le_mul_of_nonneg_right hE (by unfold nrm; positivity))
  have T2 : |(J *ᵥ α) ⬝ᵥ (J' *ᵥ eTan x' x)| ≤ nrm α * KO := by
    rw [ms_bil, ← hPα, PEm_symm, hPα]
    exact (abs_dot_le_nrm _ _).trans (mul_le_mul_of_nonneg_left hO1 (by unfold nrm; positivity))
  have T3 : |(J *ᵥ eTan x x') ⬝ᵥ (J' *ᵥ α')| ≤ nrm α' * KO := by
    rw [dotProduct_comm, ms_bil, ← hPα', PEm_symm, hPα']
    exact (abs_dot_le_nrm _ _).trans (mul_le_mul_of_nonneg_left hO2 (by unfold nrm; positivity))
  have hexp : (J *ᵥ f) ⬝ᵥ (J' *ᵥ f') = (J *ᵥ α) ⬝ᵥ (J' *ᵥ α') + (eTan x' x ⬝ᵥ f') *
      ((J *ᵥ α) ⬝ᵥ (J' *ᵥ eTan x' x)) + (eTan x x' ⬝ᵥ f) * ((J *ᵥ eTan x x') ⬝ᵥ (J' *ᵥ α')) +
      (eTan x x' ⬝ᵥ f) * (eTan x' x ⬝ᵥ f') * ((J *ᵥ eTan x x') ⬝ᵥ (J' *ᵥ eTan x' x)) := by
    conv_lhs => rw [hf, hf']
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    ring
  have hA : nrm α ≤ nrm f := by
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (eTan x x' ⬝ᵥ f)]
  have hA' : nrm α' ≤ nrm f' := by
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (eTan x' x ⬝ᵥ f')]
  have T1' := T1.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul hA hA' (nrm_nonneg _) (nrm_nonneg _)) hE0)
  have T2' := T2.trans (mul_le_mul_of_nonneg_right hA hO0)
  have T3' := T3.trans (mul_le_mul_of_nonneg_right hA' hO0)
  have h2 := mul_le_mul_of_nonneg_left T2' (abs_nonneg (eTan x' x ⬝ᵥ f'))
  have h3 := mul_le_mul_of_nonneg_left T3' (abs_nonneg (eTan x x' ⬝ᵥ f))
  have h4 := mul_le_mul_of_nonneg_left hS
    (mul_nonneg (abs_nonneg (eTan x x' ⬝ᵥ f)) (abs_nonneg (eTan x' x ⬝ᵥ f')))
  rw [hexp]
  have htri := (abs_add_le
    ((J *ᵥ α) ⬝ᵥ (J' *ᵥ α') +
      (eTan x' x ⬝ᵥ f') * ((J *ᵥ α) ⬝ᵥ (J' *ᵥ eTan x' x)) +
      (eTan x x' ⬝ᵥ f) * ((J *ᵥ eTan x x') ⬝ᵥ (J' *ᵥ α')))
    ((eTan x x' ⬝ᵥ f) * (eTan x' x ⬝ᵥ f') *
      ((J *ᵥ eTan x x') ⬝ᵥ (J' *ᵥ eTan x' x)))).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  simp only [abs_mul] at htri
  nlinarith only [htri, T1', h2, h3, h4]

end BstLean.Part208

