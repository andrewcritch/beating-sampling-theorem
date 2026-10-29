import BstLean.Part89QDefs
import BstLean.Part89QCore

/-!
# Part 89: the pointwise bound of `Dq` at the anchors `U_j / r` by `Ỹ(U)`

No `sorry`, no `native_decide`, no `axiom`.
-/

namespace BstLean.Part89

open BstLean.Part86

/-- `Dq H (U/r) ≤ 16 |I| (101/100) Ỹ(U) · (λ₀² σ² ‖H‖_F²)` on the radius event
`ρ² ≥ (100/101) D_W`, with `r² = ‖U‖² + ρ²` and `σ = 𝒟^{-1/2}`. -/
theorem dq_bound {n : ℕ} {I : Type} [Fintype I] (H : Matrix (Fin n) (Fin n) ℝ)
    (U : I × Fin n → ℝ) (ρ DDr DWv : ℝ) (hDD : 0 < DDr) (hDW : 0 < DWv)
    (hρ : 100 / 101 * DWv ≤ ρ ^ 2) :
    Dq H (fun j i => U (j, i) / Real.sqrt (∑ a, U a ^ 2 + ρ ^ 2)) ≤
      (16 * (Fintype.card I : ℝ) * (101 / 100) * Ytil H U) *
        (lam0 DDr DWv U ρ ^ 2 * (1 / Real.sqrt DDr) ^ 2 * BstLean.Part78.frobH H) := by
  have hρ2 : 0 < ρ ^ 2 := lt_of_lt_of_le (by positivity) hρ
  have hS : 0 ≤ ∑ a, U a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hR : 0 < ∑ a, U a ^ 2 + ρ ^ 2 := by linarith
  set R : ℝ := ∑ a, U a ^ 2 + ρ ^ 2 with hRdef
  have hr : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hr2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  set N : ℝ := ∑ j : I, BstLean.Part78.nsq (fun i => ∑ l, H i l * U (j, l)) with hN
  have hNnn : 0 ≤ N := by
    rw [hN]
    refine Finset.sum_nonneg fun j _ => ?_
    unfold BstLean.Part78.nsq
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hc : (0 : ℝ) ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
  -- the left side
  have hL : Dq H (fun j i => U (j, i) / Real.sqrt R) = 16 * (Fintype.card I : ℝ) * (N / R) := by
    unfold Dq
    congr 1
    rw [hN, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold BstLean.Part78.nsq
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∑ l, H i l * (U (j, l) / Real.sqrt R) = (∑ l, H i l * U (j, l)) / Real.sqrt R := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun l _ => by ring
    show (∑ l, H i l * (U (j, l) / Real.sqrt R)) ^ 2 = (∑ l, H i l * U (j, l)) ^ 2 / R
    rw [this, div_pow, hr2]
  rw [hL]
  by_cases hF : BstLean.Part78.frobH H = 0
  · -- `H = 0`
    have hH : ∀ i l, H i l = 0 := by
      intro i l
      unfold BstLean.Part78.frobH at hF
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (H i j))).mp hF i (Finset.mem_univ i)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (H i j))).mp h1 l (Finset.mem_univ l)
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
    have hN0 : N = 0 := by
      rw [hN]
      unfold BstLean.Part78.nsq
      simp [hH]
    rw [hN0, hF]
    simp
  · have hFpos : 0 < BstLean.Part78.frobH H := lt_of_le_of_ne (frobH_nonneg H) (Ne.symm hF)
    have hsD : 0 < Real.sqrt DDr := Real.sqrt_pos.mpr hDD
    have hsW : 0 < Real.sqrt DWv := Real.sqrt_pos.mpr hDW
    have hlam : lam0 DDr DWv U ρ ^ 2 * (1 / Real.sqrt DDr) ^ 2 = ρ ^ 2 / (R * DWv) := by
      unfold lam0
      rw [← hRdef, div_pow, mul_pow, mul_pow, hr2, Real.sq_sqrt hDW.le, div_pow, one_pow,
        Real.sq_sqrt hDD.le]
      field_simp
    have hR' : (16 * (Fintype.card I : ℝ) * (101 / 100) * Ytil H U) *
        (lam0 DDr DWv U ρ ^ 2 * (1 / Real.sqrt DDr) ^ 2 * BstLean.Part78.frobH H) =
        16 * (Fintype.card I : ℝ) * (N / R) * ((101 / 100) * ρ ^ 2 / DWv) := by
      rw [hlam]
      unfold Ytil
      rw [← hN]
      field_simp
    rw [hR']
    have h1 : 1 ≤ (101 / 100) * ρ ^ 2 / DWv := by
      rw [le_div_iff₀ hDW]; linarith
    have hA : 0 ≤ 16 * (Fintype.card I : ℝ) * (N / R) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 hA]

end BstLean.Part89

#print axioms BstLean.Part89.dq_bound
