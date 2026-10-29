import BstLean.Part153SJ
import BstLean.Part134Split

/-!
# Part 153 Cr: the residual covariance (Lemma `lem:Cr`)

Paper source: `proofs/option-n/theorem5-04-standin-structure.tex`, Lemma "The residual
covariance": `‖C_r‖_op ≤ Ξ + t_A·|ā₂ − b|²`.

Every result holds for EVERY pair of matrices `A₁`, `A₂` (no probability over them).
Notation: `y = c + τξ`, `x = sphPt y`, `a₂(ξ) = hid2 A₁ A₂ x`, `t = 2/m`,
`r(ξ) = res b (a₂ ξ) = a₂ − λ·b` with `λ = ⟨a₂, b⟩/|b|²` (`lam`, `res` of Part 134),
`ā₂ = E_ξ a₂` (`hid2Mean_cr`).

* `hid2Mean_cr`: the mean vector `ā₂`.
* **`resCov_le_cr`**: `t·E_ξ⟨w, r⟩² ≤ (Ξ + t·|ā₂ − b|²)·|w|²` for every `w`.
* **`resCov_le_of_cr`**: the same with a bound `K ≥ Ξ` in the place of `Ξ`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part134 (lam res)

section Cr

variable {n m : ℕ}

/-- The mean vector `ā₂ = E_ξ h₂(x)`, `x = y/|y|`, `y = c + τξ`. -/
noncomputable def hid2Mean_cr (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) : Fin m → ℝ :=
  fun j => ∫ ξ, hid2 A₁ A₂ (sphPt (c + τ • ξ)) j ∂stdGauss (Fin n)

lemma hid2_zero_cr (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ) :
    hid2 A₁ A₂ 0 = 0 := by
  have h := hid2_smul A₁ A₂ (le_refl (0 : ℝ)) (0 : Fin n → ℝ)
  rwa [zero_smul, zero_smul] at h

/-- `|h₂(z)| ≤ ‖A₂‖_op·‖A₁‖_op·|z|`. -/
lemma nrm_hid2_le_cr (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (z : Fin n → ℝ) : nrm (hid2 A₁ A₂ z) ≤ opN A₂ * opN A₁ * nrm z := by
  have h := nrm_hid2_sub_le A₁ A₂ z 0
  rwa [hid2_zero_cr, sub_zero, sub_zero] at h

lemma nrm_of_normSq_one_cr {ι : Type*} [Fintype ι] {x : ι → ℝ} (hx : normSq x = 1) :
    nrm x = 1 := by
  unfold nrm; rw [hx, Real.sqrt_one]

/-- `|h₂(x)| ≤ ‖A₂‖_op·‖A₁‖_op` on the unit sphere. -/
lemma nrm_hid2_sph_le_cr (hn : 1 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (y : Fin n → ℝ) :
    nrm (hid2 A₁ A₂ (sphPt y)) ≤ opN A₂ * opN A₁ := by
  have h := nrm_hid2_le_cr A₁ A₂ (sphPt y)
  rwa [nrm_of_normSq_one_cr (normSq_sphPt hn y), mul_one] at h

lemma continuous_hid2_cr (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (fun z : Fin n → ℝ => hid2 A₁ A₂ z) := by
  unfold hid2
  exact continuous_reluV.comp (Continuous.matrix_mulVec continuous_const
    (continuous_reluV.comp (Continuous.matrix_mulVec continuous_const continuous_id)))

lemma measurable_hid2_sph_cr (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun ξ : Fin n → ℝ => hid2 A₁ A₂ (sphPt (c + τ • ξ))) :=
  (continuous_hid2_cr A₁ A₂).measurable.comp
    (measurable_sphPt.comp (measurable_const.add (measurable_const_smul τ)))

/-- A function `ξ ↦ ⟨u, h₂(x)⟩` is measurable and bounded. -/
lemma dot_hid2_bdd_cr (hn : 1 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) (τ : ℝ) (u : Fin m → ℝ) :
    Measurable (fun ξ : Fin n → ℝ => u ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ))) ∧
    ∀ ξ : Fin n → ℝ, |u ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ))| ≤ nrm u * (opN A₂ * opN A₁) := by
  refine ⟨?_, fun ξ => ?_⟩
  · have hc : Continuous (fun v : Fin m → ℝ => u ⬝ᵥ v) := by
      unfold dotProduct; fun_prop
    exact hc.measurable.comp (measurable_hid2_sph_cr A₁ A₂ c τ)
  · exact (abs_dot_le_nrm _ _).trans
      (mul_le_mul_of_nonneg_left (nrm_hid2_sph_le_cr hn A₁ A₂ _) (nrm_nonneg _))

lemma integrable_dot_hid2_cr (hn : 1 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) (τ : ℝ) (u : Fin m → ℝ) :
    Integrable (fun ξ : Fin n → ℝ => u ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ))) (stdGauss (Fin n)) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  obtain ⟨hm, hb⟩ := dot_hid2_bdd_cr hn A₁ A₂ c τ u
  exact Integrable.of_bound hm.aestronglyMeasurable (nrm u * (opN A₂ * opN A₁))
    (Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact hb ξ)

lemma integrable_hid2_coord_cr (hn : 1 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) (τ : ℝ) (j : Fin m) :
    Integrable (fun ξ : Fin n → ℝ => hid2 A₁ A₂ (sphPt (c + τ • ξ)) j) (stdGauss (Fin n)) := by
  have h := integrable_dot_hid2_cr hn A₁ A₂ c τ (Pi.single j 1)
  simpa using h

/-- `E_ξ⟨u, h₂(x)⟩ = ⟨u, ā₂⟩`. -/
lemma integral_dot_hid2_cr (hn : 1 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) (τ : ℝ) (u : Fin m → ℝ) :
    ∫ ξ, u ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) ∂stdGauss (Fin n) =
      u ⬝ᵥ hid2Mean_cr A₁ A₂ c τ := by
  unfold dotProduct hid2Mean_cr
  rw [integral_finsetSum _ fun j _ => (integrable_hid2_coord_cr hn A₁ A₂ c τ j).const_mul (u j)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- `XiS ≥ 0`. -/
lemma XiS_nonneg_cr (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) : 0 ≤ XiS A₁ A₂ c τ := by
  unfold XiS
  exact mul_nonneg (by positivity) (integral_nonneg fun ξ =>
    mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (normSq_nonneg _)))

/-- `Π_b w = w − (⟨w, b⟩/|b|²)·b`. -/
noncomputable def projB_cr (b w : Fin m → ℝ) : Fin m → ℝ := w - ((w ⬝ᵥ b) / normSq b) • b

lemma dot_self_cr (b : Fin m → ℝ) : b ⬝ᵥ b = normSq b := by
  unfold normSq dotProduct
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `⟨w, r⟩ = ⟨Π_b w, h⟩`. -/
lemma dot_res_cr (b w h : Fin m → ℝ) : w ⬝ᵥ res b h = projB_cr b w ⬝ᵥ h := by
  have e : lam b h = (h ⬝ᵥ b) / normSq b := rfl
  unfold res projB_cr
  rw [e, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    smul_eq_mul, dotProduct_comm b h]
  ring

lemma projB_dot_cr {b : Fin m → ℝ} (hb : normSq b ≠ 0) (w : Fin m → ℝ) :
    projB_cr b w ⬝ᵥ b = 0 := by
  unfold projB_cr
  rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, dot_self_cr]
  field_simp
  ring

lemma normSq_projB_le_cr {b : Fin m → ℝ} (hb : normSq b ≠ 0) (w : Fin m → ℝ) :
    normSq (projB_cr b w) ≤ normSq w := by
  have hb0 : 0 < normSq b := lt_of_le_of_ne (normSq_nonneg b) (Ne.symm hb)
  unfold projB_cr
  rw [normSq_sub_smul]
  have e : normSq w - 2 * ((w ⬝ᵥ b) / normSq b) * (w ⬝ᵥ b) +
      ((w ⬝ᵥ b) / normSq b) ^ 2 * normSq b = normSq w - (w ⬝ᵥ b) ^ 2 / normSq b := by
    field_simp
    ring
  rw [e]
  have : 0 ≤ (w ⬝ᵥ b) ^ 2 / normSq b := by positivity
  linarith

/-- **The residual covariance** (Lemma `lem:Cr`), `‖C_r‖_op ≤ Ξ + t·|ā₂ − b|²`: for every pair
of matrices `A₁`, `A₂`, every `b ≠ 0` and every vector `w`:
`t·E_ξ⟨w, r(x)⟩² ≤ (Ξ + t·|ā₂ − b|²)·|w|²`, `r = h₂ − λ·b`, `t = 2/m`. -/
theorem resCov_le_cr (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {b : Fin m → ℝ} (hb : normSq b ≠ 0) (w : Fin m → ℝ) :
    2 / (m : ℝ) * ∫ ξ, (w ⬝ᵥ res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) ^ 2 ∂stdGauss (Fin n) ≤
      (XiS A₁ A₂ c τ + 2 / (m : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - b)) * normSq w := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn1 : 1 ≤ n := by omega
  have ht0 : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  obtain ⟨u, hu⟩ : ∃ u : Fin m → ℝ, u = projB_cr b w := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : (Fin n → ℝ) → ℝ,
      f = fun ξ => u ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) := ⟨_, rfl⟩
  have e1 : (fun ξ : Fin n → ℝ => (w ⬝ᵥ res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) ^ 2) =
      fun ξ => f ξ ^ 2 := by
    funext ξ
    rw [dot_res_cr, hf, hu]
  rw [e1]
  obtain ⟨hfm, hfb⟩ := dot_hid2_bdd_cr hn1 A₁ A₂ c τ u
  rw [← hf] at hfm
  have hfb' : ∀ ξ, |f ξ| ≤ nrm u * (opN A₂ * opN A₁) := fun ξ => by rw [hf]; exact hfb ξ
  have hfi : Integrable f (stdGauss (Fin n)) := by
    rw [hf]; exact integrable_dot_hid2_cr hn1 A₁ A₂ c τ u
  have hf2 : Integrable (fun ξ => f ξ ^ 2) (stdGauss (Fin n)) :=
    Integrable.of_bound (hfm.pow_const 2).aestronglyMeasurable
      ((nrm u * (opN A₂ * opN A₁)) ^ 2) (Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq' (by linarith [(abs_le.mp (hfb' ξ)).1]) (abs_le.mp (hfb' ξ)).2)
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = ∫ ξ, f ξ ∂stdGauss (Fin n) := ⟨_, rfl⟩
  have hvar : ∫ ξ, (f ξ - μ) ^ 2 ∂stdGauss (Fin n) =
      ∫ ξ, f ξ ^ 2 ∂stdGauss (Fin n) - μ ^ 2 := by
    have e : (fun ξ => (f ξ - μ) ^ 2) = fun ξ => f ξ ^ 2 - 2 * μ * f ξ + μ ^ 2 :=
      funext fun ξ => by ring
    have hfi2 : Integrable (fun ξ => 2 * μ * f ξ) (stdGauss (Fin n)) := hfi.const_mul _
    have hd : Integrable (fun ξ => f ξ ^ 2 - 2 * μ * f ξ) (stdGauss (Fin n)) := hf2.sub hfi2
    rw [e, integral_add hd (integrable_const _),
      integral_sub hf2 hfi2, integral_const_mul, integral_const, ← hμ]
    rw [show (stdGauss (Fin n)).real Set.univ = 1 from by simp, one_smul]
    ring
  have hcov := cov_hid2_le hn A₁ A₂ c hτ u
  have hcov' : 2 / (m : ℝ) * ∫ ξ, (f ξ - μ) ^ 2 ∂stdGauss (Fin n) ≤
      XiS A₁ A₂ c τ * normSq u := by
    rw [hμ, hf]; exact hcov
  have hμ' : μ = u ⬝ᵥ (hid2Mean_cr A₁ A₂ c τ - b) := by
    rw [hμ, hf, integral_dot_hid2_cr hn1, dotProduct_sub, hu, projB_dot_cr hb, sub_zero]
  have hμ2 : μ ^ 2 ≤ normSq u * normSq (hid2Mean_cr A₁ A₂ c τ - b) := by
    have h1 := abs_dot_le_nrm u (hid2Mean_cr A₁ A₂ c τ - b)
    rw [← hμ'] at h1
    have h2 := pow_le_pow_left₀ (abs_nonneg μ) h1 2
    rwa [sq_abs, mul_pow, nrm_sq, nrm_sq] at h2
  have hu_le : normSq u ≤ normSq w := by rw [hu]; exact normSq_projB_le_cr hb w
  have hX0 := XiS_nonneg_cr A₁ A₂ c τ
  have hD0 : 0 ≤ normSq (hid2Mean_cr A₁ A₂ c τ - b) := normSq_nonneg _
  calc 2 / (m : ℝ) * ∫ ξ, f ξ ^ 2 ∂stdGauss (Fin n)
      = 2 / (m : ℝ) * ∫ ξ, (f ξ - μ) ^ 2 ∂stdGauss (Fin n) + 2 / (m : ℝ) * μ ^ 2 := by
        rw [hvar]; ring
    _ ≤ XiS A₁ A₂ c τ * normSq u +
        2 / (m : ℝ) * (normSq u * normSq (hid2Mean_cr A₁ A₂ c τ - b)) :=
        add_le_add hcov' (mul_le_mul_of_nonneg_left hμ2 ht0)
    _ = (XiS A₁ A₂ c τ + 2 / (m : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - b)) * normSq u := by
        ring
    _ ≤ (XiS A₁ A₂ c τ + 2 / (m : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - b)) * normSq w :=
        mul_le_mul_of_nonneg_left hu_le (add_nonneg hX0 (mul_nonneg ht0 hD0))

/-- **The residual covariance with a bound `K` of `Ξ`**:
`t·E_ξ⟨w, r(x)⟩² ≤ (K + t·|ā₂ − b|²)·|w|²` if `Ξ ≤ K`. -/
theorem resCov_le_of_cr (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {b : Fin m → ℝ} (hb : normSq b ≠ 0) (w : Fin m → ℝ) {K : ℝ} (hK : XiS A₁ A₂ c τ ≤ K) :
    2 / (m : ℝ) * ∫ ξ, (w ⬝ᵥ res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) ^ 2 ∂stdGauss (Fin n) ≤
      (K + 2 / (m : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - b)) * normSq w :=
  (resCov_le_cr hn A₁ A₂ c hτ hb w).trans
    (mul_le_mul_of_nonneg_right (by linarith) (normSq_nonneg w))

/-- `res b h = h − (⟨h, b⟩/|b|²)·b` (the definitions `lam`, `res` of Part 134, in the notation
of the dot product). -/
lemma res_eq_cr (b h : Fin m → ℝ) : res b h = h - ((h ⬝ᵥ b) / normSq b) • b := rfl

end Cr

end BstLean.Part153

open BstLean.Part153 in
#print axioms resCov_le_cr
open BstLean.Part153 in
#print axioms resCov_le_of_cr
