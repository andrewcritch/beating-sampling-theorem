import BstLean.Part200Derivative
import BstLean.Part200Mean
import BstLean.Part200Lengths
import BstLean.Part200Complement
import BstLean.Part145B1
import BstLean.Part153Asm

/-! The paper pair error and its low-length complement under the Agent distribution. -/
namespace BstLean.Part200
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153

variable {n : ℕ}

/-- The derivative of `κ ∘ κ`, multiplied by the tangent input. -/
noncomputable def pairIdeal (x x' : Fin n → ℝ) : Fin n → ℝ :=
  (BstLean.Part145.kg (kappa (x ⬝ᵥ x')) * BstLean.Part145.kg (x ⬝ᵥ x')) •
    (projT x *ᵥ x')

lemma pairIdeal_le {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    nrm (pairIdeal x x') ≤ 1 := by
  have h0 := mul_nonneg (BstLean.Part145.kg_nonneg (kappa (x ⬝ᵥ x')))
    (BstLean.Part145.kg_nonneg (x ⬝ᵥ x'))
  have h1 : BstLean.Part145.kg (kappa (x ⬝ᵥ x')) * BstLean.Part145.kg (x ⬝ᵥ x') ≤ 1 := by
    have h := mul_le_mul (BstLean.Part145.kg_le_one (kappa (x ⬝ᵥ x')))
      (BstLean.Part145.kg_le_one (x ⬝ᵥ x')) (BstLean.Part145.kg_nonneg (x ⬝ᵥ x'))
      zero_le_one
    simpa using h
  have h2 : nrm (projT x *ᵥ x') ≤ 1 := by
    simpa only [nrm, hx', sqrt_one] using nrm_projT_le hx x'
  unfold pairIdeal
  rw [nrm_smul, abs_of_nonneg h0]
  exact (mul_le_mul h1 h2 (nrm_nonneg _) zero_le_one).trans_eq (by ring)

noncomputable def paperPairError (x x' : Fin n → ℝ)
    (θ : Matrix (Fin (n ^ 2)) (Fin n) ℝ × Matrix (Fin (n ^ 2)) (Fin (n ^ 2)) ℝ) : ℝ :=
  nrm ((n : ℝ)⁻¹ • pairVector θ.1 θ.2 x x' - pairIdeal x x')

lemma paperPairError_nonneg (x x' : Fin n → ℝ) (θ) : 0 ≤ paperPairError x x' θ :=
  nrm_nonneg _

lemma measurable_paperPairError (x x' : Fin n → ℝ) : Measurable (paperPairError x x') := by
  unfold paperPairError nrm
  have hm := ((measurable_pairVector (m := n ^ 2) (p := n ^ 2) x x').const_smul
    ((n : ℝ)⁻¹)).sub (measurable_const (a := pairIdeal x x'))
  have h := (BstLean.Part130.measurable_normSq.comp hm).sqrt
  simpa only [Function.comp_def, Pi.sub_apply, Pi.smul_apply] using h

/-- This constant records a coarse all-order bound. It does not replace the paper epsilon. -/
noncomputable def coarsePairMoment (n s : ℕ) : ℝ :=
  2 ^ (s - 1) * ((n : ℝ)⁻¹ ^ s *
    (matrixMoment (n ^ 2) n s (2 / n) * matrixMoment (n ^ 2) (n ^ 2) s (2 / n ^ 2)) + 1)

theorem paperPairError_moment (hn : 1 ≤ n) {s : ℕ} (hs : 1 ≤ s)
    {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    Integrable (fun θ => paperPairError x x' θ ^ s) (nuA n) ∧
    (∫ θ, paperPairError x x' θ ^ s ∂nuA n) ≤ coarsePairMoment n s := by
  simp only [nuA, mA, Nat.cast_pow]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hi, hb⟩ := pairError_joint_moment (m := n ^ 2) (p := n ^ 2) hs
    (v₁ := 2 / n) (v₂ := 2 / (n : ℝ) ^ 2) (by positivity) (by positivity)
    hx x' ((n : ℝ)⁻¹) (pairIdeal x x')
  have hnr : nrm x' = 1 := by simp only [nrm, hx', sqrt_one]
  rw [hnr, one_pow, mul_one, abs_of_nonneg (inv_nonneg.mpr hn0.le)] at hb
  refine ⟨hi, hb.trans ?_⟩
  unfold coarsePairMoment
  have hideal : nrm (pairIdeal x x') ^ s ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (nrm_nonneg _) (pairIdeal_le hx hx') s
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl hideal)
    (by positivity)

/-- The corresponding absolute moment norm has a proved, coarse constant. -/
theorem paperPairError_coarse_norm (hn : 1 ≤ n) {s : ℕ} (hs : 1 ≤ s)
    {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    BstLean.Part161.momN (nuA n) s (paperPairError x x') ≤
      coarsePairMoment n s ^ ((s : ℝ)⁻¹) := by
  have hb := (paperPairError_moment hn hs hx hx').2
  dsimp only [nuA, mA] at hb ⊢
  unfold BstLean.Part161.momN
  simp_rw [abs_of_nonneg (paperPairError_nonneg x x' _)]
  exact rpow_le_rpow (integral_nonneg fun θ => pow_nonneg (paperPairError_nonneg x x' θ) s)
    hb (inv_nonneg.mpr (Nat.cast_nonneg s))

def pairLowLength (x x' : Fin n → ℝ) (η : ℝ) :
    Set (Matrix (Fin (n ^ 2)) (Fin n) ℝ × Matrix (Fin (n ^ 2)) (Fin (n ^ 2)) ℝ) :=
  {θ | η < |layerLength θ.1 x - 1| ∨ η < |layerLength θ.1 x' - 1|}

lemma measurableSet_pairLowLength (x x' : Fin n → ℝ) (η : ℝ) :
    MeasurableSet (pairLowLength x x' η) :=
  (measurableSet_lt measurable_const
    (((measurable_layerLength x).comp measurable_fst).sub measurable_const).abs).union
  (measurableSet_lt measurable_const
    (((measurable_layerLength x').comp measurable_fst).sub measurable_const).abs)

theorem pairLowLength_probability (hn : 2 ≤ n) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) {η : ℝ} (hη : 2 / (n : ℝ) ^ 2 ≤ η) :
    (nuA n).real (pairLowLength x x' η) ≤
      4 * exp (-(n : ℝ) ^ 2 * (η - 2 / (n : ℝ) ^ 2) ^ 2 / 4) := by
  dsimp only [nuA, mA, pairLowLength]
  change ((gaussMat (n ^ 2) n (2 / n)).prod
      (gaussMat (n ^ 2) (n ^ 2) (2 / ((n ^ 2 : ℕ) : ℝ)))).real
    {θ | θ.1 ∈ {A | η < |layerLength A x - 1| ∨ η < |layerLength A x' - 1|}} ≤ _
  rw [prod_real_fst {A | η < |layerLength A x - 1| ∨ η < |layerLength A x' - 1|}]
  exact pair_lowLength_probability hn hx hx' hη

/-- The paper cutoff `η = 1/100` is admissible from dimension 15. -/
theorem pairLowLength_probability_one_percent (hn : 15 ≤ n) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    (nuA n).real (pairLowLength x x' (1 / 100)) ≤
      4 * exp (-(n : ℝ) ^ 2 * (1 / 100 - 2 / (n : ℝ) ^ 2) ^ 2 / 4) := by
  have hnR : (15 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  apply pairLowLength_probability (by omega) hx hx'
  rw [div_le_iff₀ (pow_pos hn0 2)]
  nlinarith

/-- The actual low-length complement has the paper probability and a proved higher moment.
Its moment constant is coarse; this theorem does not supply the sharp `B_s`. -/
theorem paperPairError_lowLength (hn : 2 ≤ n) {s : ℕ} (hs : 1 ≤ s)
    {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    {η : ℝ} (hη : 2 / (n : ℝ) ^ 2 ≤ η) :
    (∫ θ in pairLowLength x x' η, paperPairError x x' θ ^ s ∂nuA n) ≤
      √(coarsePairMoment n (2 * s)) *
        √(4 * exp (-(n : ℝ) ^ 2 * (η - 2 / (n : ℝ) ^ 2) ^ 2 / 4)) := by
  obtain ⟨hi, hb⟩ := paperPairError_moment (by omega) (s := 2 * s) (by omega) hx hx'
  dsimp only [nuA, mA] at hi hb ⊢
  letI : IsProbabilityMeasure (gaussMat (n ^ 2) n (2 / (n : ℝ))) := inferInstance
  letI : IsProbabilityMeasure (gaussMat (n ^ 2) (n ^ 2) (2 / ((n ^ 2 : ℕ) : ℝ))) :=
    inferInstance
  exact restricted_moment_bound
    (μ := (gaussMat (n ^ 2) n (2 / (n : ℝ))).prod
      (gaussMat (n ^ 2) (n ^ 2) (2 / ((n ^ 2 : ℕ) : ℝ))))
    (measurable_paperPairError x x')
    (paperPairError_nonneg x x') hi (measurableSet_pairLowLength x x' η) hb
    (pairLowLength_probability hn hx hx' hη)

end BstLean.Part200
