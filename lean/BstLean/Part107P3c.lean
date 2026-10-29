import BstLean.Part107P3b

/-!
# Part 107 (P3), file c: the bound of `|∇f|²` on `U`
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part105

variable {n : ℕ}

lemma sum_sq_partials {r : ℝ} (hr : |r| ≤ 1) {w : Fin n ⊕ Fin n → ℝ} (hw : w ∈ Uset r)
    {L : (Fin n ⊕ Fin n → ℝ) →L[ℝ] ℝ}
    (hL : ∀ v, L v =
      Pf r w * ((-(1 / (2 * Real.sqrt (Af w * Bf r w))) / Real.sqrt (Af w * Bf r w) ^ 2) *
        (Af w * dBv r w v + Bf r w * dAv w v)) + (Real.sqrt (Af w * Bf r w))⁻¹ * dPv r w v) :
    ∑ j, (L (Pi.single j 1)) ^ 2 =
      (1 - qf r w ^ 2) * (1 / Af w + 1 / Bf r w - 2 * r * Pf r w / (Af w * Bf r w)) := by
  have hD := mul_pos_of_mem hw
  have hA : 0 < Af w := lt_of_le_of_ne (Af_nonneg w) (Ne.symm hw.1)
  have hB : 0 < Bf r w := lt_of_le_of_ne (Bf_nonneg r w) (Ne.symm hw.2)
  have hδ : 0 < Real.sqrt (Af w * Bf r w) := Real.sqrt_pos.2 hD
  have hBδ : Bf r w = Real.sqrt (Af w * Bf r w) ^ 2 / Af w := by
    rw [Real.sq_sqrt hD.le]
    field_simp
  have h1 : ∀ k : Fin n, L (Pi.single (Sum.inl k) 1) = (Real.sqrt (Af w * Bf r w))⁻¹ *
      ((r - Pf r w / Af w) * gL w k + (1 - r * Pf r w / Bf r w) * gR r w k) := fun k => by
    rw [hL, dPv_inl, dAv_inl, dBv_inl]
    exact scal_inl hA hδ hBδ
  have h2 : ∀ k : Fin n, L (Pi.single (Sum.inr k) 1) = (Real.sqrt (Af w * Bf r w))⁻¹ *
      (sC r * (1 * gL w k + (-(Pf r w / Bf r w)) * gR r w k)) := fun k => by
    rw [hL, dPv_inr, dAv_inr, dBv_inr]
    exact scal_inr hA hδ hBδ
  have hinv : (Real.sqrt (Af w * Bf r w))⁻¹ ^ 2 = (Af w * Bf r w)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hD.le]
  have e1 : ∑ k : Fin n, (L (Pi.single (Sum.inl k) 1)) ^ 2 = (Af w * Bf r w)⁻¹ *
      ((r - Pf r w / Af w) ^ 2 * Af w + 2 * (r - Pf r w / Af w) * (1 - r * Pf r w / Bf r w) * Pf r w
        + (1 - r * Pf r w / Bf r w) ^ 2 * Bf r w) := by
    simp_rw [h1, mul_pow]
    rw [← Finset.mul_sum, sum_lin_sq, hinv]
    rfl
  have e2 : ∑ k : Fin n, (L (Pi.single (Sum.inr k) 1)) ^ 2 = (Af w * Bf r w)⁻¹ *
      (sC r ^ 2 * (1 ^ 2 * Af w + 2 * 1 * (-(Pf r w / Bf r w)) * Pf r w
        + (-(Pf r w / Bf r w)) ^ 2 * Bf r w)) := by
    simp_rw [h2, mul_pow]
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_lin_sq, hinv]
    rfl
  rw [Fintype.sum_sum_type, e1, e2, ← mul_add]
  have hq : qf r w ^ 2 = Pf r w ^ 2 * (Af w * Bf r w)⁻¹ := by
    rw [qf, mul_pow, hinv]
  rw [hq]
  exact scal_total hA hB (sC_sq hr)

/-- The majorant `Γ` of `|∇f|²`. -/
noncomputable def Gam (cκ r : ℝ) (w : Fin n ⊕ Fin n → ℝ) : ℝ :=
  cκ * (1 + |r|) * (1 / Af w + 1 / Bf r w)

lemma grad_bound {r cκ : ℝ} {ψ ψ' : ℝ → ℝ} (hr : |r| ≤ 1) (hψ : ∀ a, HasDerivAt ψ (ψ' a) a)
    (hb : ∀ a : ℝ, |a| ≤ 1 → ψ' a ^ 2 * (1 - a ^ 2) ≤ cκ)
    {w : Fin n ⊕ Fin n → ℝ} (hw : w ∈ Uset r) :
    ∑ j, (fderiv ℝ (fun w : Fin n ⊕ Fin n → ℝ => ψ (qf r w)) w (Pi.single j 1)) ^ 2 ≤
      Gam cκ r w := by
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_qf hw
  have hf : fderiv ℝ (fun w : Fin n ⊕ Fin n → ℝ => ψ (qf r w)) w = ψ' (qf r w) • L :=
    ((hψ (qf r w)).comp_hasFDerivAt w hL).fderiv
  have hA : 0 < Af w := lt_of_le_of_ne (Af_nonneg w) (Ne.symm hw.1)
  have hB : 0 < Bf r w := lt_of_le_of_ne (Bf_nonneg r w) (Ne.symm hw.2)
  have hD := mul_pos_of_mem hw
  have hsum : ∑ j, (fderiv ℝ (fun w : Fin n ⊕ Fin n → ℝ => ψ (qf r w)) w (Pi.single j 1)) ^ 2 =
      ψ' (qf r w) ^ 2 * ((1 - qf r w ^ 2) *
        (1 / Af w + 1 / Bf r w - 2 * r * Pf r w / (Af w * Bf r w))) := by
    rw [hf, ← sum_sq_partials hr hw hLv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul, mul_pow]
  rw [hsum, ← mul_assoc]
  have hq := abs_qf_le_one r w
  have hX1 : ψ' (qf r w) ^ 2 * (1 - qf r w ^ 2) ≤ cκ := hb _ hq
  have hX0 : 0 ≤ ψ' (qf r w) ^ 2 * (1 - qf r w ^ 2) := by
    have : qf r w ^ 2 ≤ 1 := by
      have := sq_le_one_iff_abs_le_one (qf r w) |>.2 hq
      linarith
    exact mul_nonneg (sq_nonneg _) (by linarith)
  have h2P : |2 * Pf r w| ≤ Af w + Bf r w := by
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    nlinarith [Pf_sq_le r w, sq_nonneg (Af w - Bf r w)]
  have hrP : -(2 * r * Pf r w) ≤ |r| * (Af w + Bf r w) := by
    calc -(2 * r * Pf r w) ≤ |2 * r * Pf r w| := neg_le_abs _
      _ = |r| * |2 * Pf r w| := by rw [← abs_mul]; ring_nf
      _ ≤ |r| * (Af w + Bf r w) := mul_le_mul_of_nonneg_left h2P (abs_nonneg r)
  have hY : 1 / Af w + 1 / Bf r w - 2 * r * Pf r w / (Af w * Bf r w) ≤
      (1 + |r|) * (1 / Af w + 1 / Bf r w) := by
    have e1 : 1 / Af w + 1 / Bf r w = (Af w + Bf r w) / (Af w * Bf r w) := by
      field_simp
      ring
    rw [e1, ← sub_nonneg]
    have e2 : (1 + |r|) * ((Af w + Bf r w) / (Af w * Bf r w)) -
        ((Af w + Bf r w) / (Af w * Bf r w) - 2 * r * Pf r w / (Af w * Bf r w)) =
        (|r| * (Af w + Bf r w) + 2 * r * Pf r w) / (Af w * Bf r w) := by ring
    rw [e2]
    exact div_nonneg (by linarith) hD.le
  have hZ : 0 ≤ (1 + |r|) * (1 / Af w + 1 / Bf r w) := by positivity
  unfold Gam
  calc ψ' (qf r w) ^ 2 * (1 - qf r w ^ 2) *
        (1 / Af w + 1 / Bf r w - 2 * r * Pf r w / (Af w * Bf r w))
      ≤ ψ' (qf r w) ^ 2 * (1 - qf r w ^ 2) * ((1 + |r|) * (1 / Af w + 1 / Bf r w)) :=
        mul_le_mul_of_nonneg_left hY hX0
    _ ≤ cκ * ((1 + |r|) * (1 / Af w + 1 / Bf r w)) := mul_le_mul_of_nonneg_right hX1 hZ
    _ = cκ * (1 + |r|) * (1 / Af w + 1 / Bf r w) := by ring

end BstLean.Part107
