import BstLean.Part107P3a

/-!
# Part 107 (P3), file b: the derivative of `q` and the partial derivatives
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part105

variable {n : ℕ}

lemma hasFDerivAt_bil {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : Fin n → (E →L[ℝ] ℝ)) (w : E) :
    HasFDerivAt (fun w => ∑ i, a i w * b i w) (∑ i, (a i w • b i + b i w • a i)) w :=
  HasFDerivAt.fun_sum fun i _ => (a i).hasFDerivAt.fun_mul (b i).hasFDerivAt

/-- The coordinate `g_i` as a continuous linear map. -/
noncomputable def pL (i : Fin n) : (Fin n ⊕ Fin n → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (Sum.inl i)

/-- The coordinate `g′_i` as a continuous linear map. -/
noncomputable def pR (r : ℝ) (i : Fin n) : (Fin n ⊕ Fin n → ℝ) →L[ℝ] ℝ :=
  r • ContinuousLinearMap.proj (Sum.inl i) + sC r • ContinuousLinearMap.proj (Sum.inr i)

@[simp] lemma pL_apply (i : Fin n) (w : Fin n ⊕ Fin n → ℝ) : pL i w = gL w i := rfl

@[simp] lemma pR_apply (r : ℝ) (i : Fin n) (w : Fin n ⊕ Fin n → ℝ) : pR r i w = gR r w i := by
  simp [pR, gR]

/-- `dP(v)`. -/
noncomputable def dPv (r : ℝ) (w v : Fin n ⊕ Fin n → ℝ) : ℝ :=
  ∑ i, (gL w i * gR r v i + gR r w i * gL v i)

def dAv (w v : Fin n ⊕ Fin n → ℝ) : ℝ := ∑ i, (gL w i * gL v i + gL w i * gL v i)

noncomputable def dBv (r : ℝ) (w v : Fin n ⊕ Fin n → ℝ) : ℝ :=
  ∑ i, (gR r w i * gR r v i + gR r w i * gR r v i)

lemma hasFDerivAt_qf {r : ℝ} {w : Fin n ⊕ Fin n → ℝ} (hw : w ∈ Uset r) :
    ∃ L : (Fin n ⊕ Fin n → ℝ) →L[ℝ] ℝ, HasFDerivAt (qf r) L w ∧ ∀ v, L v =
      Pf r w * ((-(1 / (2 * Real.sqrt (Af w * Bf r w))) / Real.sqrt (Af w * Bf r w) ^ 2) *
        (Af w * dBv r w v + Bf r w * dAv w v)) + (Real.sqrt (Af w * Bf r w))⁻¹ * dPv r w v := by
  have hDpos := mul_pos_of_mem hw
  have hP := hasFDerivAt_bil (pL (n := n)) (pR r) w
  have hA := hasFDerivAt_bil (pL (n := n)) pL w
  have hB := hasFDerivAt_bil (pR (n := n) r) (pR r) w
  simp only [pL_apply, pR_apply] at hP hA hB
  have hD := hA.fun_mul hB
  have hs := ((Real.hasDerivAt_sqrt hDpos.ne').fun_inv
    (Real.sqrt_pos.2 hDpos).ne').comp_hasFDerivAt w hD
  have hq := hP.fun_mul hs
  refine ⟨_, hq, fun v => ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, smul_eq_mul, pL_apply, pR_apply, dPv, dAv, dBv]
  rfl

/-! ## The partial derivatives -/

lemma gL_single_inl (k : Fin n) : gL (Pi.single (Sum.inl k) (1 : ℝ)) = Pi.single k 1 := by
  funext i
  simp [gL, Pi.single_apply]

lemma gL_single_inr (k : Fin n) : gL (Pi.single (Sum.inr k) (1 : ℝ)) = 0 := by
  funext i
  simp [gL]

lemma gR_single_inl (r : ℝ) (k : Fin n) :
    gR r (Pi.single (Sum.inl k) (1 : ℝ)) = Pi.single k r := by
  funext i
  simp [gR, Pi.single_apply]

lemma gR_single_inr (r : ℝ) (k : Fin n) :
    gR r (Pi.single (Sum.inr k) (1 : ℝ)) = Pi.single k (sC r) := by
  funext i
  simp [gR, Pi.single_apply]

lemma dPv_inl (r : ℝ) (w : Fin n ⊕ Fin n → ℝ) (k : Fin n) :
    dPv r w (Pi.single (Sum.inl k) 1) = gL w k * r + gR r w k := by
  simp [dPv, gL_single_inl, gR_single_inl, Finset.sum_add_distrib, Pi.single_apply]

lemma dAv_inl (w : Fin n ⊕ Fin n → ℝ) (k : Fin n) :
    dAv w (Pi.single (Sum.inl k) 1) = gL w k + gL w k := by
  simp [dAv, gL_single_inl, Finset.sum_add_distrib, Pi.single_apply]

lemma dBv_inl (r : ℝ) (w : Fin n ⊕ Fin n → ℝ) (k : Fin n) :
    dBv r w (Pi.single (Sum.inl k) 1) = gR r w k * r + gR r w k * r := by
  simp [dBv, gR_single_inl, Finset.sum_add_distrib, Pi.single_apply]

lemma dPv_inr (r : ℝ) (w : Fin n ⊕ Fin n → ℝ) (k : Fin n) :
    dPv r w (Pi.single (Sum.inr k) 1) = gL w k * sC r := by
  simp [dPv, gL_single_inr, gR_single_inr, Pi.single_apply]

lemma dAv_inr (w : Fin n ⊕ Fin n → ℝ) (k : Fin n) :
    dAv w (Pi.single (Sum.inr k) 1) = 0 := by
  simp [dAv, gL_single_inr]

lemma dBv_inr (r : ℝ) (w : Fin n ⊕ Fin n → ℝ) (k : Fin n) :
    dBv r w (Pi.single (Sum.inr k) 1) = gR r w k * sC r + gR r w k * sC r := by
  simp [dBv, gR_single_inr, Finset.sum_add_distrib, Pi.single_apply]

/-! ## Scalar algebra -/

lemma scal_inl {P A B δ x y r : ℝ} (hA : 0 < A) (hδ : 0 < δ) (hB : B = δ ^ 2 / A) :
    P * ((-(1 / (2 * δ)) / δ ^ 2) * (A * (y * r + y * r) + B * (x + x))) + δ⁻¹ * (x * r + y) =
      δ⁻¹ * ((r - P / A) * x + (1 - r * P / B) * y) := by
  subst hB
  field_simp
  ring

lemma scal_inr {P A B δ x y s : ℝ} (hA : 0 < A) (hδ : 0 < δ) (hB : B = δ ^ 2 / A) :
    P * ((-(1 / (2 * δ)) / δ ^ 2) * (A * (y * s + y * s) + B * 0)) + δ⁻¹ * (x * s) =
      δ⁻¹ * (s * (1 * x + (-(P / B)) * y)) := by
  subst hB
  field_simp
  ring

lemma sum_lin_sq (x y : Fin n → ℝ) (c d : ℝ) :
    ∑ k, (c * x k + d * y k) ^ 2 =
      c ^ 2 * ∑ k, x k * x k + 2 * c * d * ∑ k, x k * y k + d ^ 2 * ∑ k, y k * y k := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma scal_total {P A B r t : ℝ} (hA : 0 < A) (hB : 0 < B) (ht : t = 1 - r ^ 2) :
    (A * B)⁻¹ * (((r - P / A) ^ 2 * A + 2 * (r - P / A) * (1 - r * P / B) * P +
        (1 - r * P / B) ^ 2 * B) +
      t * (1 ^ 2 * A + 2 * 1 * (-(P / B)) * P + (-(P / B)) ^ 2 * B)) =
      (1 - P ^ 2 * (A * B)⁻¹) * (1 / A + 1 / B - 2 * r * P / (A * B)) := by
  subst ht
  field_simp
  ring

end BstLean.Part107
