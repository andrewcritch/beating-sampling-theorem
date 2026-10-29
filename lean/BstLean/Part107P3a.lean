import BstLean.Part107Defs

/-!
# Part 107 (P3), file a: the function `q(w) = P/√(A B)` on `ℝ^{n ⊕ n}`

`w = (g, h)`, `g′ = r g + √(1−r²) h`, `P = g·g′`, `A = |g|²`, `B = |g′|²`, `q = a = x·x′`.
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part105

variable {n : ℕ}

/-- `g(w)`. -/
def gL (w : Fin n ⊕ Fin n → ℝ) : Fin n → ℝ := fun i => w (Sum.inl i)

/-- `h(w)`. -/
def hL (w : Fin n ⊕ Fin n → ℝ) : Fin n → ℝ := fun i => w (Sum.inr i)

/-- `g′(w) = r g + √(1−r²) h`. -/
noncomputable def gR (r : ℝ) (w : Fin n ⊕ Fin n → ℝ) : Fin n → ℝ :=
  fun i => r * w (Sum.inl i) + sC r * w (Sum.inr i)

noncomputable def Pf (r : ℝ) (w : Fin n ⊕ Fin n → ℝ) : ℝ := ∑ i, gL w i * gR r w i

def Af (w : Fin n ⊕ Fin n → ℝ) : ℝ := ∑ i, gL w i * gL w i

noncomputable def Bf (r : ℝ) (w : Fin n ⊕ Fin n → ℝ) : ℝ := ∑ i, gR r w i * gR r w i

noncomputable def qf (r : ℝ) (w : Fin n ⊕ Fin n → ℝ) : ℝ :=
  Pf r w * (Real.sqrt (Af w * Bf r w))⁻¹

/-- The open set where `g ≠ 0` and `g′ ≠ 0`. -/
def Uset (r : ℝ) : Set (Fin n ⊕ Fin n → ℝ) := {w | Af w ≠ 0 ∧ Bf r w ≠ 0}

lemma Af_nonneg (w : Fin n ⊕ Fin n → ℝ) : 0 ≤ Af w :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

lemma Bf_nonneg (r : ℝ) (w : Fin n ⊕ Fin n → ℝ) : 0 ≤ Bf r w :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

lemma sum_mul_self_eq_zero_iff (x : Fin n → ℝ) : (∑ i, x i * x i = 0) ↔ x = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg _]
  constructor
  · intro h
    funext i
    exact mul_self_eq_zero.1 (h i (Finset.mem_univ i))
  · intro h i _
    simp [h]

lemma Af_ne_zero_iff (w : Fin n ⊕ Fin n → ℝ) : Af w ≠ 0 ↔ gL w ≠ 0 :=
  not_congr (sum_mul_self_eq_zero_iff _)

lemma Bf_ne_zero_iff (r : ℝ) (w : Fin n ⊕ Fin n → ℝ) : Bf r w ≠ 0 ↔ gR r w ≠ 0 :=
  not_congr (sum_mul_self_eq_zero_iff _)

lemma gR_eq (r : ℝ) (w : Fin n ⊕ Fin n → ℝ) : gR r w = r • gL w + sC r • hL w := by
  funext i
  simp [gR, gL, hL]

lemma Af_eq (w : Fin n ⊕ Fin n → ℝ) : Af w = ∑ i, gL w i ^ 2 :=
  Finset.sum_congr rfl fun _ _ => (sq _).symm

lemma Bf_eq (r : ℝ) (w : Fin n ⊕ Fin n → ℝ) : Bf r w = ∑ i, gR r w i ^ 2 :=
  Finset.sum_congr rfl fun _ _ => (sq _).symm

/-- `a = q`. -/
lemma aR_eq (r : ℝ) (w : Fin n ⊕ Fin n → ℝ) : aR r (gL w, hL w) = qf r w := by
  unfold aR cosA
  simp only [← gR_eq]
  unfold dot sphProj qf
  rw [Real.sqrt_mul (Af_nonneg w), ← Af_eq, ← Bf_eq, Pf, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, mul_inv]
  ring

lemma Pf_sq_le (r : ℝ) (w : Fin n ⊕ Fin n → ℝ) : Pf r w ^ 2 ≤ Af w * Bf r w := by
  rw [Af_eq, Bf_eq]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma abs_qf_le_one (r : ℝ) (w : Fin n ⊕ Fin n → ℝ) : |qf r w| ≤ 1 := by
  unfold qf
  have h := Pf_sq_le r w
  have hD : 0 ≤ Af w * Bf r w := mul_nonneg (Af_nonneg w) (Bf_nonneg r w)
  have h1 : |Pf r w| ≤ Real.sqrt (Af w * Bf r w) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h
  rw [abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (Af w * Bf r w)) with h0 | h0
  · rw [← h0]; simp
  · rw [← div_eq_mul_inv, div_le_one h0]
    exact h1

lemma contDiff_Pf (r : ℝ) : ContDiff ℝ 1 (Pf (n := n) r) := by
  unfold Pf gL gR
  fun_prop

lemma contDiff_Af : ContDiff ℝ 1 (Af (n := n)) := by
  unfold Af gL
  fun_prop

lemma contDiff_Bf (r : ℝ) : ContDiff ℝ 1 (Bf (n := n) r) := by
  unfold Bf gR
  fun_prop

lemma isOpen_Uset (r : ℝ) : IsOpen (Uset (n := n) r) :=
  (isOpen_ne_fun contDiff_Af.continuous continuous_const).inter
    (isOpen_ne_fun (contDiff_Bf r).continuous continuous_const)

lemma mul_pos_of_mem {r : ℝ} {w : Fin n ⊕ Fin n → ℝ} (hw : w ∈ Uset r) :
    0 < Af w * Bf r w :=
  mul_pos (lt_of_le_of_ne (Af_nonneg w) (Ne.symm hw.1))
    (lt_of_le_of_ne (Bf_nonneg r w) (Ne.symm hw.2))

lemma contDiffOn_qf (r : ℝ) : ContDiffOn ℝ 1 (qf (n := n) r) (Uset r) := by
  unfold qf
  refine (contDiff_Pf r).contDiffOn.mul (ContDiffOn.inv ?_ ?_)
  · exact (contDiff_Af.mul (contDiff_Bf r)).contDiffOn.sqrt fun w hw => (mul_pos_of_mem hw).ne'
  · intro w hw
    exact (Real.sqrt_pos.2 (mul_pos_of_mem hw)).ne'

lemma measurable_qf (r : ℝ) : Measurable (qf (n := n) r) := by
  unfold qf
  exact (contDiff_Pf r).continuous.measurable.mul
    ((contDiff_Af.mul (contDiff_Bf r)).continuous.measurable.sqrt.inv)

section Psi

variable {ψ ψ' : ℝ → ℝ}

lemma contDiff_psi (hψ : ∀ a, HasDerivAt ψ (ψ' a) a) (hc : Continuous ψ') : ContDiff ℝ 1 ψ := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun a => (hψ a).differentiableAt, ?_⟩
  have : deriv ψ = ψ' := funext fun a => (hψ a).deriv
  rw [this]
  exact hc

lemma contDiffOn_f (hψ : ∀ a, HasDerivAt ψ (ψ' a) a) (hc : Continuous ψ') (r : ℝ) :
    ContDiffOn ℝ 1 (fun w : Fin n ⊕ Fin n → ℝ => ψ (qf r w)) (Uset r) :=
  (contDiff_psi hψ hc).comp_contDiffOn (contDiffOn_qf r)

lemma measurable_f (hψ : ∀ a, HasDerivAt ψ (ψ' a) a) (r : ℝ) :
    Measurable (fun w : Fin n ⊕ Fin n → ℝ => ψ (qf r w)) :=
  (continuous_iff_continuousAt.2 fun a => (hψ a).continuousAt).measurable.comp (measurable_qf r)

lemma memLp_f (hψ : ∀ a, HasDerivAt ψ (ψ' a) a) (r : ℝ) :
    MemLp (fun w : Fin n ⊕ Fin n → ℝ => ψ (qf r w)) 2 (stdGauss (Fin n ⊕ Fin n)) := by
  have hcont : Continuous ψ := continuous_iff_continuousAt.2 fun a => (hψ a).continuousAt
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine MemLp.of_bound (measurable_f hψ r).aestronglyMeasurable C (ae_of_all _ fun w => ?_)
  exact hC _ (abs_le.1 (abs_qf_le_one r w))

end Psi

end BstLean.Part107
