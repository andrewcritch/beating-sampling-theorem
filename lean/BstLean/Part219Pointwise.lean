import BstLean.Part215Direction
import BstLean.Part215Mean
import BstLean.Part215Operator

/-! The actual computed-centre gradient splits into ideal, error and transfer terms. -/
namespace BstLean.Part219
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part215
open BstLean.Part29 (stdGauss)

noncomputable def radial {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) : ℝ :=
  τ / nrm (c + τ • ξ)

noncomputable def idealSize {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) : ℝ :=
  radial c τ ξ * nrm (idealInputAverage c τ ξ)

noncomputable def errorSize {n : ℕ} (c : Fin n → ℝ) (τ : ℝ)
    (a : AgentPair n) (ξ : Fin n → ℝ) : ℝ :=
  radial c τ ξ * nrm (inputErrorAverage c τ a ξ)

noncomputable def operatorSize {n : ℕ} (c : Fin n → ℝ) (τ : ℝ)
    (a : AgentPair n) (ξ : Fin n → ℝ) : ℝ :=
  radial c τ ξ * opN (jacT a.1 a.2 (standPoint c τ ξ))

lemma radial_nonneg {n : ℕ} (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (ξ) :
    0 ≤ radial c τ ξ := div_nonneg hτ (nrm_nonneg _)

lemma measurable_radial {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) : Measurable (radial c τ) :=
  measurable_const.div ((BstLean.Part130.measurable_normSq.comp
    (measurable_const.add (measurable_id.const_smul τ))).sqrt)

lemma measurable_idealSize {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (idealSize c τ) := by
  have hm : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      BstLean.Part200.pairIdeal (standPoint c τ p.1) (standPoint c τ p.2)) := by
    have h := (continuous_pairIdeal (n := n)).measurable.comp
      (((measurable_standPoint c τ).comp measurable_fst).prodMk
        ((measurable_standPoint c τ).comp measurable_snd))
    simpa only [Function.comp_def] using h
  exact (measurable_radial c τ).mul ((BstLean.Part130.measurable_normSq.comp
    hm.stronglyMeasurable.integral_prod_right'.measurable).sqrt)

lemma measurable_errorSize {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (a : AgentPair n) :
    Measurable (errorSize c τ a) := by
  have hm := (measurable_inputErrorAverage c τ).comp
    (show Measurable (fun ξ : Fin n → ℝ => (a, ξ)) from
      measurable_const.prodMk measurable_id)
  exact (measurable_radial c τ).mul ((BstLean.Part130.measurable_normSq.comp hm).sqrt)

lemma measurable_operatorSize {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (a : AgentPair n) :
    Measurable (operatorSize c τ a) := by
  have h := (measurable_opN_jacT_sph c τ).comp
    (show Measurable (fun ξ : Fin n → ℝ => (a, ξ)) from
      measurable_const.prodMk measurable_id)
  have h' : Measurable (fun ξ => opN (jacT a.1 a.2 (standPoint c τ ξ))) := by
    simpa only [Function.comp_def, standPoint] using h
  exact (measurable_radial c τ).mul h'

/-- Scaling by sqrt(n) leaves the computed denominator equal to the centre norm. -/
theorem scaled_gradient_bound {n : ℕ} (hn : 1 ≤ n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (a : AgentPair n)
    (b : Fin (mA n) → ℝ) (hb : 0 < nrm b) :
    ∀ᵐ ξ ∂stdGauss (Fin n),
      √(n : ℝ) * √(BstLean.Part151.gradSq (computedCoordinate a.1 a.2 c τ b) ξ) ≤
        radial c τ ξ / nrm b * nrm ((jacT a.1 a.2 (standPoint c τ ξ))ᵀ *ᵥ b) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  filter_upwards [computed_gradient_bound hn a.1 a.2 c hτ b, ae_normSq_ne hn c hτ.ne']
    with ξ hg hy
  have hy0 : 0 < nrm (c + τ • ξ) := sqrt_pos.mpr (lt_of_le_of_ne
    (normSq_nonneg _) (Ne.symm hy))
  have hs : 0 < √(n : ℝ) := sqrt_pos.mpr hnR
  have hvec : ((√(n : ℝ) * nrm b)⁻¹ • b) ᵥ* jacT a.1 a.2 (standPoint c τ ξ) =
      (√(n : ℝ) * nrm b)⁻¹ • ((jacT a.1 a.2 (standPoint c τ ξ))ᵀ *ᵥ b) := by
    rw [Matrix.smul_vecMul]
    congr 1
    ext i
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  change _ ≤ τ ^ 2 * (normSq (((√(n : ℝ) * nrm b)⁻¹ • b) ᵥ*
    jacT a.1 a.2 (standPoint c τ ξ)) * (normSq (c + τ • ξ))⁻¹) at hg
  rw [hvec, normSq_smul] at hg
  apply (sq_le_sq₀ (by positivity) (mul_nonneg
    (div_nonneg (radial_nonneg c hτ.le ξ) hb.le) (nrm_nonneg _))).mp
  rw [mul_pow, sq_sqrt hnR.le, sq_sqrt (BstLean.Part151.gradSq_nonneg _ _)]
  have he : (radial c τ ξ / nrm b *
      nrm ((jacT a.1 a.2 (standPoint c τ ξ))ᵀ *ᵥ b)) ^ 2 =
      (n : ℝ) * (τ ^ 2 * (((√(n : ℝ) * nrm b)⁻¹ ^ 2 *
        normSq ((jacT a.1 a.2 (standPoint c τ ξ))ᵀ *ᵥ b)) *
        (normSq (c + τ • ξ))⁻¹)) := by
    unfold radial
    simp only [mul_pow, div_pow, inv_pow, nrm_sq, sq_sqrt hnR.le]
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left hg hnR.le

/-- The same matrices and computed denominator occur in all three summands. -/
theorem gradient_three_terms {n : ℕ} (hn : 1 ≤ n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (a : AgentPair n)
    (b : Fin (mA n) → ℝ) {e ξhp : ℝ} (he : 0 < e) (hξ : 0 ≤ ξhp)
    (hb : (n : ℝ) * e ≤ normSq b)
    (hfull : normSq (hid2Mean_cr a.1 a.2 c τ - b) ≤ ξhp) :
    ∀ᵐ ξ ∂stdGauss (Fin n),
      √(n : ℝ) * √(BstLean.Part151.gradSq (computedCoordinate a.1 a.2 c τ b) ξ) ≤
        (√(n : ℝ) / √e) * idealSize c τ ξ +
        (√(n : ℝ) / √e) * errorSize c τ a ξ +
        √(ξhp / ((n : ℝ) * e)) * operatorSize c τ a ξ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb0 : 0 < nrm b := sqrt_pos.mpr (lt_of_lt_of_le (mul_pos hnR he) hb)
  have hc : (n : ℝ) / nrm b ≤ √(n : ℝ) / √e := by
    apply (div_le_div_iff₀ hb0 (sqrt_pos.mpr he)).mpr
    have hl : √((n : ℝ) * e) ≤ nrm b := sqrt_le_sqrt hb
    rw [sqrt_mul hnR.le] at hl
    have hh := mul_le_mul_of_nonneg_left hl (sqrt_nonneg (n : ℝ))
    rw [← mul_assoc, ← sq, sq_sqrt hnR.le] at hh
    exact hh
  filter_upwards [scaled_gradient_bound hn c hτ a b hb0] with ξ hg
  set J := jacT a.1 a.2 (standPoint c τ ξ)
  set μ := hid2Mean_cr a.1 a.2 c τ
  have hr := radial_nonneg c hτ.le ξ
  have ht := tangent_transfer_of_full J μ b (a := radial c τ ξ / nrm b)
    (div_nonneg hr hb0.le) hnR he hξ hb hfull
  have hi : nrm (Jᵀ *ᵥ μ) ≤ (n : ℝ) *
      (nrm (inputErrorAverage c τ a ξ) + nrm (idealInputAverage c τ ξ)) := by
    have hm := mean_tangent_identity hn c τ a ξ
    have hnorm := congrArg nrm hm
    rw [nrm_smul, abs_of_nonneg (inv_nonneg.mpr hnR.le)] at hnorm
    have ha := nrm_add_le (inputErrorAverage c τ a ξ) (idealInputAverage c τ ξ)
    rw [hnorm] at ha
    change (n : ℝ)⁻¹ * nrm (Jᵀ *ᵥ μ) ≤ _ at ha
    have hh := mul_le_mul_of_nonneg_left ha hnR.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hnR.ne', one_mul] using hh
  have hh := mul_le_mul_of_nonneg_left hi (div_nonneg hr hb0.le)
  have hcc := mul_le_mul_of_nonneg_right hc
    (mul_nonneg hr (add_nonneg (nrm_nonneg (inputErrorAverage c τ a ξ))
      (nrm_nonneg (idealInputAverage c τ ξ))))
  have heq : (radial c τ ξ / nrm b * nrm b * opN J) = operatorSize c τ a ξ := by
    unfold operatorSize
    dsimp only [J]
    field_simp
  rw [heq] at ht
  calc
    _ ≤ radial c τ ξ / nrm b * nrm (Jᵀ *ᵥ μ) +
        operatorSize c τ a ξ * √(ξhp / ((n : ℝ) * e)) := hg.trans ht
    _ ≤ radial c τ ξ / nrm b * ((n : ℝ) *
        (nrm (inputErrorAverage c τ a ξ) + nrm (idealInputAverage c τ ξ))) +
        operatorSize c τ a ξ * √(ξhp / ((n : ℝ) * e)) := add_le_add hh le_rfl
    _ ≤ _ := by
      unfold idealSize errorSize
      convert _root_.add_le_add_right hcc
        (operatorSize c τ a ξ * √(ξhp / ((n : ℝ) * e))) using 1 <;> ring

#print axioms scaled_gradient_bound
#print axioms gradient_three_terms
end BstLean.Part219
