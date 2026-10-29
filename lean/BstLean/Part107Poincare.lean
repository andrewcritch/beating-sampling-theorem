import BstLean.Part107PoincareB

/-!
# Part 107: the Gaussian Poincaré inequality with constant 1 (`Poincare107`)

Route: the rotation path `θ ↦ cos θ · x + sin θ · z` (energy bound `energy107` of file B) and the
Gebelein inequality of Part 105 (`gebelein_L2`):
`2 (1 − cos a) V ≤ E (f(X_a) − f(X))² ≤ a² ∫ Γ`, then `a → 0⁺`.
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part48 (rotX rotY rot_preserving)
open BstLean.Part105

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma var_eq107 (f : (ι → ℝ) → ℝ) (hf2 : MemLp f 2 (stdGauss ι)) :
    ∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι =
      (∫ x, f x ^ 2 ∂stdGauss ι) - (∫ y, f y ∂stdGauss ι) ^ 2 := by
  set m := ∫ y, f y ∂stdGauss ι with hm
  have hi : Integrable f (stdGauss ι) := hf2.integrable (by norm_num)
  have hs : Integrable (fun x => f x ^ 2) (stdGauss ι) := hf2.integrable_sq
  have e : ∀ x, (f x - m) ^ 2 = f x ^ 2 - 2 * m * f x + m ^ 2 := fun x => by ring
  simp_rw [e]
  have h2 : Integrable (fun x => 2 * m * f x) (stdGauss ι) := hi.const_mul _
  have h3 : Integrable (fun x => f x ^ 2 - 2 * m * f x) (stdGauss ι) := hs.sub h2
  rw [integral_add h3 (integrable_const _), integral_sub hs h2, integral_const_mul, ← hm]
  simp
  ring

/-- `2 (1 − cos a) V ≤ a² ∫ Γ` for `0 ≤ a ≤ 1`. -/
lemma step107 (f : (ι → ℝ) → ℝ) (U : Set (ι → ℝ)) (Γ : (ι → ℝ) → ℝ) (hUo : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hf2 : MemLp f 2 (stdGauss ι)) (hΓ : Integrable Γ (stdGauss ι))
    (hb : ∀ x ∈ U, ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2 ≤ Γ x)
    (hpath : ∀ᵐ p ∂(stdGauss ι).prod (stdGauss ι), ∀ θ : ℝ, rotX θ p.1 p.2 ∈ U)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    2 * (1 - Real.cos a) * ∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι ≤
      a ^ 2 * ∫ x, Γ x ∂stdGauss ι := by
  have hI := (gradPhi_lintegral_le107 f U Γ hΓ hb (ae_fst_mem107 U hpath)).1
  have hen := energy107 f U Γ hUo hf hΓ hb hpath ha
  have hpi : a ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hcos : 0 ≤ Real.cos a := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hpi⟩
  have hsin : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi ha (by linarith [Real.pi_gt_three])
  have hρ : |Real.cos a| ≤ 1 := Real.abs_cos_le_one a
  have hsC : sC (Real.cos a) = Real.sin a := by
    unfold sC
    rw [← Real.sin_sq_add_cos_sq a, add_sub_cancel_right, Real.sqrt_sq hsin]
  have hφ : ∀ w : (ι → ℝ) × (ι → ℝ),
      Real.cos a • w.1 + sC (Real.cos a) • w.2 = rotX a w.1 w.2 := fun w => by
    rw [hsC, rotX_eq107]
  have mp2 := ou_mp_snd (ι := ι) hρ
  have mp1 := ou_mp_fst (ι := ι)
  simp_rw [hφ] at mp2
  have hgeb := gebelein_L2 hρ hf2 hf2
  have hci := gebelein_L2_integrable hρ hf2 hf2
  simp_rw [hφ] at hgeb hci
  set V := ∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι with hV
  have hV0 : 0 ≤ V := integral_nonneg fun x => sq_nonneg _
  rw [mul_assoc, Real.mul_self_sqrt hV0, abs_of_nonneg hcos] at hgeb
  have hV' := var_eq107 f hf2
  rw [← hV] at hV'
  set m := ∫ y, f y ∂stdGauss ι
  set S := ∫ x, f x ^ 2 ∂stdGauss ι
  set C := ∫ w, f w.1 * f (rotX a w.1 w.2) ∂(stdGauss ι).prod (stdGauss ι)
  have hC : C ≤ m ^ 2 + Real.cos a * V := by
    have := (abs_le.mp hgeb).2
    nlinarith [this]
  have hsm : AEStronglyMeasurable (fun x => f x ^ 2) (stdGauss ι) :=
    hf2.integrable_sq.aestronglyMeasurable
  have A2 : ∫ w, f (rotX a w.1 w.2) ^ 2 ∂(stdGauss ι).prod (stdGauss ι) = S :=
    mp_integral_ae mp2 hsm
  have A1 : ∫ w : (ι → ℝ) × (ι → ℝ), f w.1 ^ 2 ∂(stdGauss ι).prod (stdGauss ι) = S :=
    mp_integral_ae mp1 hsm
  have i2 : Integrable (fun w : (ι → ℝ) × (ι → ℝ) => f (rotX a w.1 w.2) ^ 2)
      ((stdGauss ι).prod (stdGauss ι)) := (hf2.comp_measurePreserving mp2).integrable_sq
  have i1 : Integrable (fun w : (ι → ℝ) × (ι → ℝ) => f w.1 ^ 2)
      ((stdGauss ι).prod (stdGauss ι)) := (hf2.comp_measurePreserving mp1).integrable_sq
  have e : ∀ w : (ι → ℝ) × (ι → ℝ), (f (rotX a w.1 w.2) - f w.1) ^ 2 =
      f (rotX a w.1 w.2) ^ 2 + f w.1 ^ 2 - 2 * (f w.1 * f (rotX a w.1 w.2)) := fun w => by ring
  have hint : Integrable (fun w : (ι → ℝ) × (ι → ℝ) => (f (rotX a w.1 w.2) - f w.1) ^ 2)
      ((stdGauss ι).prod (stdGauss ι)) := by
    simp_rw [e]
    exact (i2.add i1).sub (hci.const_mul 2)
  have hD : ∫ w : (ι → ℝ) × (ι → ℝ), (f (rotX a w.1 w.2) - f w.1) ^ 2
      ∂(stdGauss ι).prod (stdGauss ι) = 2 * S - 2 * C := by
    simp_rw [e]
    have i12 : Integrable (fun w : (ι → ℝ) × (ι → ℝ) => f (rotX a w.1 w.2) ^ 2 + f w.1 ^ 2)
        ((stdGauss ι).prod (stdGauss ι)) := i2.add i1
    have i3 : Integrable (fun w : (ι → ℝ) × (ι → ℝ) => 2 * (f w.1 * f (rotX a w.1 w.2)))
        ((stdGauss ι).prod (stdGauss ι)) := hci.const_mul 2
    rw [integral_sub i12 i3, integral_add i2 i1, integral_const_mul, A1, A2]
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun w => sq_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg a) hI), hD] at hen
  nlinarith [hen, hC, hV']

theorem poincare107 : Poincare107 := by
  intro ι _ _ f U Γ hUo hf _ hf2 hΓ hb hpath
  have hpath' : ∀ᵐ p ∂(stdGauss ι).prod (stdGauss ι), ∀ θ : ℝ, rotX θ p.1 p.2 ∈ U := by
    filter_upwards [hpath] with p hp θ
    rw [rotX_eq107]
    exact hp θ
  set V := ∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι with hV
  set I := ∫ x, Γ x ∂stdGauss ι with hI
  have hV0 : 0 ≤ V := integral_nonneg fun x => sq_nonneg _
  have ht : Tendsto (fun a : ℝ => (1 - 5 / 48 * a ^ 2) * V) (𝓝[>] 0) (𝓝 V) := by
    have hc : Continuous (fun a : ℝ => (1 - 5 / 48 * a ^ 2) * V) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  refine le_of_tendsto ht ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with a ha
  have hs := step107 f U Γ hUo hf hf2 hΓ hb hpath' ha.1.le ha.2
  rw [← hV, ← hI] at hs
  have hcb := (abs_le.mp (Real.cos_bound (x := a) (by rw [abs_of_pos ha.1]; exact ha.2))).2
  rw [abs_of_pos ha.1] at hcb
  have h2 : a ^ 2 * ((1 - 5 / 48 * a ^ 2) * V) ≤ a ^ 2 * I := by
    have : (a ^ 2 - 5 / 48 * a ^ 4) * V ≤ 2 * (1 - Real.cos a) * V :=
      mul_le_mul_of_nonneg_right (by linarith) hV0
    nlinarith [this, hs]
  exact le_of_mul_le_mul_left h2 (pow_pos ha.1 2)

theorem poincare107_C1 {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) (hf2 : MemLp f 2 (stdGauss ι))
    (hG : Integrable (fun x => ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2) (stdGauss ι)) :
    ∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι ≤
      ∫ x, ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2 ∂stdGauss ι :=
  poincare107 ι f Set.univ _ isOpen_univ hf.contDiffOn hf.continuous.measurable hf2 hG
    (fun _ _ => le_rfl) (Eventually.of_forall fun _ _ => Set.mem_univ _)

end BstLean.Part107

#print axioms BstLean.Part107.poincare107
#print axioms BstLean.Part107.poincare107_C1
