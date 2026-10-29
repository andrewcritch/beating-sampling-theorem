import BstLean.Part182SBlk2
import BstLean.Part182OBlk
import BstLean.Part182Mask2

/-!
# Part 182 (file `SBlk3`): the S block of Lemma TI as one probabilistic statement

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `proofs/option-n/theorem7-04-frame-numerator.tex`, Lemma `t7:p04:ti`, the scalar block.

* `s3_scalar_eq`: `⟨J(x)e, J(x')e'⟩` is the masked second-layer row sum `s3R A₂ a a' p p'`
  (`a = ReLU(A₁x)`, `p = D₁A₁e`).
* `s3_cond_tail`: the Fubini step under `nuA n` — on the first-layer good set `s3G1`,
  `|s − E[s | A₁]| ≤ r_s` except with probability `2e^{−τ}` (`s2_scalar_dev` for each `A₁`).
* `s3_mean_eq`: the two forms of the conditional mean agree when `m·t = 2`.
* **`s3_Sblock`**: `Pr_{A₁,A₂}(|s| > n k_s) ≤ 23 e^{−τ} + 2 e^{−2η²m}`, `n k_s = max(|𝖴|, |𝖫|)` with
  the paper's constants (`s3ap`, `s3am`, `s3dm`, `s3c1`, `s3pp`, `s3e0`, `s3rs`, `s3Cpa`, `s3r1`,
  `s3Cpp`, `s3rpp`, `s3Lam`, `s3U`, `s3L`, `s3nks`), given the paper's conditions on them.
  Tails used: `nm_overlap_tail` (5), `nm_tail_a_upper/lower` (4), `single_tail` (2, Hoeffding),
  `ob_p_tail` (2), `ob_eps_tail` (4), `sb_tail_pa` (4), `sb_tail_pp` (2), `s3_cond_tail` (2).
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (mask measurable_mask jac)
open BstLean.Part153 (nrm nuA)

variable {n : ℕ}

/-- The first-layer tangent vector `p = D₁ A₁ e`. -/
noncomputable def s3p {m k : ℕ} (x e : Fin k → ℝ) (A : Matrix (Fin m) (Fin k) ℝ) : Fin m → ℝ :=
  obD (A *ᵥ x) *ᵥ (A *ᵥ e)

/-- The masked second-layer row sum. -/
noncomputable def s3R {m k : ℕ} (B : Matrix (Fin m) (Fin k) ℝ) (a a' p p' : Fin k → ℝ) : ℝ :=
  ∑ i, mask ((B *ᵥ a) i) * mask ((B *ᵥ a') i) * ((B *ᵥ p) i * (B *ᵥ p') i)

/-- The conditional mean in the form of `s2_scalar_dev`. -/
noncomputable def s3M {k : ℕ} (m : ℕ) (t : ℝ) (a a' p p' : Fin k → ℝ) : ℝ :=
  m * t * (kdot (s2_unit a ⬝ᵥ s2_unit a') / 2 * (p ⬝ᵥ p') +
    ((p ⬝ᵥ s2_unit a) * (p' ⬝ᵥ s2_unit a') + (p' ⬝ᵥ s2_unit a) * (p ⬝ᵥ s2_unit a') -
      (s2_unit a ⬝ᵥ s2_unit a') * ((p ⬝ᵥ s2_unit a) * (p' ⬝ᵥ s2_unit a) +
        (p ⬝ᵥ s2_unit a') * (p' ⬝ᵥ s2_unit a'))) /
      (2 * π * √(1 - (s2_unit a ⬝ᵥ s2_unit a') ^ 2)))

lemma s3_obD_mulVec {k : ℕ} (u w : Fin k → ℝ) (i : Fin k) : (obD u *ᵥ w) i = mask (u i) * w i := by
  unfold obD; rw [Matrix.mulVec_diagonal]

/-- **The scalar of the S block is the masked row sum**:
`⟨J(x)e, J(x')e'⟩ = ∑ᵢ 1{(A₂a)ᵢ>0}1{(A₂a')ᵢ>0}(A₂p)ᵢ(A₂p')ᵢ`. -/
theorem s3_scalar_eq {m m₂ k : ℕ} (A₁ : Matrix (Fin m) (Fin k) ℝ) (A₂ : Matrix (Fin m₂) (Fin m) ℝ)
    (x x' e e' : Fin k → ℝ) :
    (jac A₁ A₂ x *ᵥ e) ⬝ᵥ (jac A₁ A₂ x' *ᵥ e') =
      s3R A₂ (reluV (A₁ *ᵥ x)) (reluV (A₁ *ᵥ x')) (s3p x e A₁) (s3p x' e' A₁) := by
  have h1 : jac A₁ A₂ x *ᵥ e = obD (A₂ *ᵥ reluV (A₁ *ᵥ x)) *ᵥ (A₂ *ᵥ s3p x e A₁) := by
    rw [ob_jac_eq]; unfold s3p; simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have h2 : jac A₁ A₂ x' *ᵥ e' = obD (A₂ *ᵥ reluV (A₁ *ᵥ x')) *ᵥ (A₂ *ᵥ s3p x' e' A₁) := by
    rw [ob_jac_eq]; unfold s3p; simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [h1, h2]
  unfold s3R dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s3_obD_mulVec, s3_obD_mulVec]; ring

/-! ## Measurability -/

lemma s3_meas_mulVec {α : Type*} [MeasurableSpace α] {p q : ℕ} {F : α → Matrix (Fin p) (Fin q) ℝ}
    {G : α → Fin q → ℝ} (hF : Measurable F) (hG : Measurable G) :
    Measurable (fun z => F z *ᵥ G z) := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hF)).mul
    ((measurable_pi_apply j).comp hG)

lemma s3_meas_dot {α : Type*} [MeasurableSpace α] {q : ℕ} {f g : α → Fin q → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun z => f z ⬝ᵥ g z) := by
  unfold dotProduct
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hf).mul ((measurable_pi_apply i).comp hg)

lemma s3_meas_normSq {α : Type*} [MeasurableSpace α] {q : ℕ} {f : α → Fin q → ℝ}
    (hf : Measurable f) : Measurable (fun z => normSq (f z)) := by
  unfold normSq
  exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hf).pow_const 2

lemma s3_meas_unit {α : Type*} [MeasurableSpace α] {q : ℕ} {f : α → Fin q → ℝ}
    (hf : Measurable f) : Measurable (fun z => s2_unit (f z)) := by
  unfold s2_unit
  exact ((s3_meas_normSq hf).sqrt.inv).smul hf

lemma s3_meas_kdot : Measurable kdot := by
  unfold kdot
  exact (measurable_const.sub (Real.continuous_arccos.measurable.div_const _))

lemma s3_meas_relu {α : Type*} [MeasurableSpace α] {q : ℕ} {f : α → Fin q → ℝ}
    (hf : Measurable f) : Measurable (fun z => reluV (f z)) := by
  refine measurable_pi_iff.mpr fun i => ?_
  unfold reluV relu
  exact measurable_const.max ((measurable_pi_apply i).comp hf)

lemma s3_meas_p {m k : ℕ} {α : Type*} [MeasurableSpace α] (x e : Fin k → ℝ)
    {F : α → Matrix (Fin m) (Fin k) ℝ} (hF : Measurable F) :
    Measurable (fun z => s3p x e (F z)) := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [s3p, s3_obD_mulVec]
  exact (measurable_mask.comp ((measurable_pi_apply i).comp (s3_meas_mulVec hF measurable_const))).mul
    ((measurable_pi_apply i).comp (s3_meas_mulVec hF measurable_const))

lemma s3_meas_R {α : Type*} [MeasurableSpace α] {m k : ℕ} {B : α → Matrix (Fin m) (Fin k) ℝ}
    {a a' p p' : α → Fin k → ℝ} (hB : Measurable B) (ha : Measurable a) (ha' : Measurable a')
    (hp : Measurable p) (hp' : Measurable p') :
    Measurable (fun z => s3R (B z) (a z) (a' z) (p z) (p' z)) := by
  unfold s3R
  refine Finset.measurable_sum _ fun i _ => ?_
  have h := fun (g : α → Fin k → ℝ) (hg : Measurable g) =>
    (measurable_pi_apply i).comp (s3_meas_mulVec hB hg)
  exact ((measurable_mask.comp (h a ha)).mul (measurable_mask.comp (h a' ha'))).mul
    ((h p hp).mul (h p' hp'))

lemma s3_meas_M {α : Type*} [MeasurableSpace α] {k : ℕ} (m : ℕ) (t : ℝ)
    {a a' p p' : α → Fin k → ℝ} (ha : Measurable a) (ha' : Measurable a')
    (hp : Measurable p) (hp' : Measurable p') :
    Measurable (fun z => s3M m t (a z) (a' z) (p z) (p' z)) := by
  unfold s3M
  have hu := s3_meas_unit ha
  have hu' := s3_meas_unit ha'
  have hq := s3_meas_dot hu hu'
  refine measurable_const.mul ((((s3_meas_kdot.comp hq).div_const _).mul (s3_meas_dot hp hp')).add ?_)
  refine Measurable.div ?_ (measurable_const.mul ((measurable_const.sub (hq.pow_const 2)).sqrt))
  exact (((s3_meas_dot hp hu).mul (s3_meas_dot hp' hu')).add
    ((s3_meas_dot hp' hu).mul (s3_meas_dot hp hu'))).sub
    (hq.mul (((s3_meas_dot hp hu).mul (s3_meas_dot hp' hu)).add
      ((s3_meas_dot hp hu').mul (s3_meas_dot hp' hu'))))

lemma s3_ne_of_pos {k : ℕ} {a : Fin k → ℝ} (h : 0 < normSq a) : a ≠ 0 := by
  rintro rfl; simp [normSq] at h

/-- The first-layer good set of the conditional step. -/
def s3G1 {m k : ℕ} (x x' e e' : Fin k → ℝ) (pp : ℝ) (A : Matrix (Fin m) (Fin k) ℝ) : Prop :=
  0 < normSq (reluV (A *ᵥ x)) ∧ 0 < normSq (reluV (A *ᵥ x')) ∧
    (s2_unit (reluV (A *ᵥ x)) ⬝ᵥ s2_unit (reluV (A *ᵥ x'))) ^ 2 < 1 ∧
    0 < normSq (s3p x e A) ∧ 0 < normSq (s3p x' e' A) ∧
    √(normSq (s3p x e A)) ≤ pp ∧ √(normSq (s3p x' e' A)) ≤ pp

lemma s3_meas_G1 {m k : ℕ} (x x' e e' : Fin k → ℝ) (pp : ℝ) :
    MeasurableSet {A : Matrix (Fin m) (Fin k) ℝ | s3G1 x x' e e' pp A} := by
  have ha := s3_meas_relu (s3_meas_mulVec (F := fun A : Matrix (Fin m) (Fin k) ℝ => A)
    measurable_id (measurable_const (a := x)))
  have ha' := s3_meas_relu (s3_meas_mulVec (F := fun A : Matrix (Fin m) (Fin k) ℝ => A)
    measurable_id (measurable_const (a := x')))
  have hp := s3_meas_p x e (F := fun A : Matrix (Fin m) (Fin k) ℝ => A) measurable_id
  have hp' := s3_meas_p x' e' (F := fun A : Matrix (Fin m) (Fin k) ℝ => A) measurable_id
  unfold s3G1
  refine (measurableSet_lt measurable_const (s3_meas_normSq ha)).inter
    ((measurableSet_lt measurable_const (s3_meas_normSq ha')).inter
    ((measurableSet_lt ((s3_meas_dot (s3_meas_unit ha) (s3_meas_unit ha')).pow_const 2)
      measurable_const).inter
    ((measurableSet_lt measurable_const (s3_meas_normSq hp)).inter
    ((measurableSet_lt measurable_const (s3_meas_normSq hp')).inter
    ((measurableSet_le (s3_meas_normSq hp).sqrt measurable_const).inter
      (measurableSet_le (s3_meas_normSq hp').sqrt measurable_const))))))

/-- **The conditional scalar deviation under `nuA`** (Fubini over `A₁`, `s2_scalar_dev` for each
fixed `A₁`): on the first-layer good set, `|s − E[s | A₁]| ≤ r_s = 2t p₊²(√(2mτ) + τ)` except with
probability `2e^{−τ}`. -/
theorem s3_cond_tail (hn : 1 ≤ n) (x x' e e' : Fin n → ℝ) {pp τ : ℝ} (hτ : 0 ≤ τ) :
    (nuA n).real {θ | s3G1 x x' e e' pp θ.1 ∧
      2 * (2 / ((mA n : ℕ) : ℝ) * pp ^ 2) * (√(2 * (mA n : ℕ) * τ) + τ) <
        |s3R θ.2 (reluV (θ.1 *ᵥ x)) (reluV (θ.1 *ᵥ x')) (s3p x e θ.1) (s3p x' e' θ.1) -
          s3M (mA n) (2 / ((mA n : ℕ) : ℝ)) (reluV (θ.1 *ᵥ x)) (reluV (θ.1 *ᵥ x'))
            (s3p x e θ.1) (s3p x' e' θ.1)|} ≤ 2 * exp (-τ) := by
  classical
  have hm : 0 < mA n := by unfold mA; positivity
  have hmR : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by exact_mod_cast hm
  have ht : (0 : ℝ) < 2 / ((mA n : ℕ) : ℝ) := by positivity
  have hP1 : IsProbabilityMeasure (gaussMat (mA n) n (2 / (n : ℝ))) := by
    unfold gaussMat; infer_instance
  have hP2 : IsProbabilityMeasure (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) := by
    unfold gaussMat; infer_instance
  set t := 2 / ((mA n : ℕ) : ℝ) with htd
  set S := {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      s3G1 x x' e e' pp θ.1 ∧ 2 * (t * pp ^ 2) * (√(2 * (mA n : ℕ) * τ) + τ) <
        |s3R θ.2 (reluV (θ.1 *ᵥ x)) (reluV (θ.1 *ᵥ x')) (s3p x e θ.1) (s3p x' e' θ.1) -
          s3M (mA n) t (reluV (θ.1 *ᵥ x)) (reluV (θ.1 *ᵥ x')) (s3p x e θ.1) (s3p x' e' θ.1)|}
    with hS
  have hSm : MeasurableSet S := by
    have h1 : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
        Matrix (Fin (mA n)) (Fin (mA n)) ℝ => θ.1) := measurable_fst
    have ha := s3_meas_relu (s3_meas_mulVec h1 (measurable_const (a := x)))
    have ha' := s3_meas_relu (s3_meas_mulVec h1 (measurable_const (a := x')))
    have hp := s3_meas_p x e h1
    have hp' := s3_meas_p x' e' h1
    refine (measurable_fst (s3_meas_G1 (m := mA n) x x' e e' pp)).inter ?_
    exact measurableSet_lt measurable_const
      ((s3_meas_R measurable_snd ha ha' hp hp').sub (s3_meas_M (mA n) t ha ha' hp hp')).abs
  have hB : 0 ≤ 2 * exp (-τ) := by positivity
  rw [Measure.real]
  unfold nuA
  rw [Measure.prod_apply hSm]
  have hle : ∫⁻ A, (gaussMat (mA n) (mA n) t) (Prod.mk A ⁻¹' S)
      ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ∫⁻ _A, ENNReal.ofReal (2 * exp (-τ)) ∂gaussMat (mA n) n (2 / (n : ℝ)) := by
    refine lintegral_mono fun A => ?_
    by_cases hA : s3G1 x x' e e' pp A
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hA
      have hd := s2_scalar_dev (m := mA n) ht (s3_ne_of_pos h1) (s3_ne_of_pos h2) h3
        (s3_ne_of_pos h4) (s3_ne_of_pos h5) h6 h7 hm hτ
      have e1 : Prod.mk A ⁻¹' S = {B | 2 * (t * pp ^ 2) * (√(2 * (mA n : ℕ) * τ) + τ) <
          |s3R B (reluV (A *ᵥ x)) (reluV (A *ᵥ x')) (s3p x e A) (s3p x' e' A) -
            s3M (mA n) t (reluV (A *ᵥ x)) (reluV (A *ᵥ x')) (s3p x e A) (s3p x' e' A)|} := by
        ext B
        simp only [hS, Set.mem_preimage, Set.mem_setOf_eq]
        exact ⟨fun h => h.2, fun h => ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h⟩⟩
      rw [e1, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal hd
    · have e1 : Prod.mk A ⁻¹' S = ∅ := by
        ext B
        simp only [hS, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hA h.1
      rw [e1, measure_empty]
      exact bot_le
  rw [lintegral_const, measure_univ, mul_one] at hle
  calc (∫⁻ A, (gaussMat (mA n) (mA n) t) (Prod.mk A ⁻¹' S)
        ∂gaussMat (mA n) n (2 / (n : ℝ))).toReal
      ≤ (ENNReal.ofReal (2 * exp (-τ))).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = 2 * exp (-τ) := ENNReal.toReal_ofReal hB

/-- The two forms of the conditional mean agree when `m·t = 2`. -/
lemma s3_mean_eq {m k : ℕ} {t : ℝ} (ht : 0 < t) (hmt : (m : ℝ) * t = 2) {a a' p p' : Fin k → ℝ}
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hq : (s2_unit a ⬝ᵥ s2_unit a') ^ 2 < 1) :
    s3M m t a a' p p' =
      kdot (s2_unit a ⬝ᵥ s2_unit a') * (p ⬝ᵥ p') +
        1 / (π * √(1 - (s2_unit a ⬝ᵥ s2_unit a') ^ 2)) *
          ((p ⬝ᵥ s2_unit a') - (s2_unit a ⬝ᵥ s2_unit a') * (p ⬝ᵥ s2_unit a)) *
          ((p' ⬝ᵥ s2_unit a) - (s2_unit a ⬝ᵥ s2_unit a') * (p' ⬝ᵥ s2_unit a')) +
        √(1 - (s2_unit a ⬝ᵥ s2_unit a') ^ 2) / π * (p ⬝ᵥ s2_unit a) * (p' ⬝ᵥ s2_unit a') := by
  have h1 := s2_mean_s (m := m) (p := p) (p' := p') ht ha ha' hq
  have h2 := s2_cond_mean (m := m) (p := p) (p' := p') ht hmt ha ha' hq
  unfold s3M
  rw [← h1, h2]

lemma s3_unit_dot {k : ℕ} (a b : Fin k → ℝ) :
    s2_unit a ⬝ᵥ s2_unit b = (a ⬝ᵥ b) / (√(normSq a) * √(normSq b)) := by
  unfold s2_unit
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  field_simp

lemma s3_dot_unit {k : ℕ} (p a : Fin k → ℝ) : p ⬝ᵥ s2_unit a = (p ⬝ᵥ a) / √(normSq a) := by
  unfold s2_unit
  rw [dotProduct_smul, smul_eq_mul]
  field_simp

lemma s3_relu_dot_nonneg {k : ℕ} (u w : Fin k → ℝ) : 0 ≤ reluV u ⬝ᵥ reluV w := by
  unfold dotProduct reluV relu
  exact Finset.sum_nonneg fun i _ => mul_nonneg (le_max_left _ _) (le_max_left _ _)

/-- The positive factor of the conditional mean (deterministic). -/
lemma s3_lam {D C r N am ap ε ε0 q : ℝ} (hD : |D - C| ≤ r) (hN1 : am < N) (hN2 : N < ap)
    (ham : 0 < am) (hε : |ε| ≤ ε0) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hCr : 0 ≤ C - r)
    (hpos : ε0 ≤ (C - r) / ap) :
    0 ≤ D / N - q * ε ∧ D / N - q * ε ≤ (C + r) / am + ε0 := by
  have hN : 0 < N := ham.trans hN1
  have hap : 0 < ap := hN.trans hN2
  obtain ⟨hD1, hD2⟩ := abs_le.1 hD
  have hqe : |q * ε| ≤ ε0 := by
    rw [abs_mul, abs_of_nonneg hq0]
    calc q * |ε| ≤ 1 * |ε| := mul_le_mul_of_nonneg_right hq1 (abs_nonneg _)
      _ ≤ ε0 := by linarith
  obtain ⟨he1, he2⟩ := abs_le.1 hqe
  constructor
  · have h1 : (C - r) / ap ≤ D / N := by
      calc (C - r) / ap ≤ (C - r) / N := div_le_div_of_nonneg_left hCr hN hN2.le
        _ ≤ D / N := div_le_div_of_nonneg_right (by linarith) hN.le
    linarith
  · have h1 : D / N ≤ (C + r) / am := by
      calc D / N ≤ (C + r) / N := div_le_div_of_nonneg_right (by linarith) hN.le
        _ ≤ (C + r) / am := div_le_div_of_nonneg_left (by linarith) ham hN1.le
    linarith

/-! ## The constants of the S block (paper notation; `m = mA n`, `γ = 2/n`, `υ = √(2τ)`) -/

/-- `a₊ = √n + υ√γ`. -/
noncomputable def s3ap (n : ℕ) (τ : ℝ) : ℝ := √(n : ℝ) + √(2 * τ) * √(2 / (n : ℝ))
/-- `a₋ = √(n − γ) − υ√γ`. -/
noncomputable def s3am (n : ℕ) (τ : ℝ) : ℝ := √((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ))
/-- `d₋ = √(2n(1 − κ(c)) − 4γ) − 2υ√γ`. -/
noncomputable def s3dm (n : ℕ) (τ c : ℝ) : ℝ :=
  √(2 * n * (1 - kappa c) - 4 * (2 / n)) - 2 * (√(2 * τ) * √(2 / (n : ℝ)))
/-- `c₁⁺ = (2a₊² − d₋²)/(2a₋²)`. -/
noncomputable def s3c1 (n : ℕ) (τ c : ℝ) : ℝ :=
  (2 * s3ap n τ ^ 2 - s3dm n τ c ^ 2) / (2 * s3am n τ ^ 2)
/-- `K₁⁺ = m(1/2 + η)`. -/
noncomputable def s3K (n : ℕ) (η : ℝ) : ℝ := ((mA n : ℕ) : ℝ) * (1 / 2 + η)
/-- `p₊ = √γ(√K₁⁺ + υ)`. -/
noncomputable def s3pp (n : ℕ) (τ η : ℝ) : ℝ := √(2 / (n : ℝ)) * (√(s3K n η) + √(2 * τ))
/-- `ε₀ = υ√γ`. -/
noncomputable def s3e0 (n : ℕ) (τ : ℝ) : ℝ := √(2 / (n : ℝ)) * √(2 * τ)
/-- `r_s = 2 t p₊²(√(2mτ) + τ)`, `t = 2/m`. -/
noncomputable def s3rs (n : ℕ) (τ η : ℝ) : ℝ :=
  2 * (2 / ((mA n : ℕ) : ℝ) * s3pp n τ η ^ 2) * (√(2 * (mA n : ℕ) * τ) + τ)
/-- `nV(c)` (as `m γ V(c)/2`). -/
noncomputable def s3Cpa (n : ℕ) (c : ℝ) : ℝ :=
  ((mA n : ℕ) : ℝ) * (2 / (n : ℝ)) * (√(1 - c ^ 2) * kdot c) / 2
/-- `r₁ = 2(3γ)(√(2mτ) + τ)`. -/
noncomputable def s3r1 (n : ℕ) (τ : ℝ) : ℝ := 2 * (3 * (2 / (n : ℝ))) * (√(2 * (mA n : ℕ) * τ) + τ)
/-- `nM(c)` (as `m γ M(c)/2`). -/
noncomputable def s3Cpp (n : ℕ) (c : ℝ) : ℝ :=
  ((mA n : ℕ) : ℝ) * (2 / (n : ℝ)) * (√(1 - c ^ 2) / π - c * kdot c) / 2
/-- `r_pp = 2(2γ)(√(2mτ) + τ)`. -/
noncomputable def s3rpp (n : ℕ) (τ : ℝ) : ℝ := 2 * (2 * (2 / (n : ℝ))) * (√(2 * (mA n : ℕ) * τ) + τ)
/-- `Λ = (nV + r₁)/a₋ + υ√γ`. -/
noncomputable def s3Lam (n : ℕ) (τ c : ℝ) : ℝ := (s3Cpa n c + s3r1 n τ) / s3am n τ + s3e0 n τ
/-- The upper bound `𝖴`. -/
noncomputable def s3U (n : ℕ) (τ η c : ℝ) : ℝ :=
  (if 0 ≤ s3Cpp n c + s3rpp n τ then kdot (s3c1 n τ c) * (s3Cpp n c + s3rpp n τ)
    else (s3Cpp n c + s3rpp n τ) / 2) +
    s3Lam n τ c ^ 2 / (π * √(1 - s3c1 n τ c ^ 2)) + s3e0 n τ ^ 2 + s3rs n τ η
/-- The lower bound `𝖫`. -/
noncomputable def s3L (n : ℕ) (τ η c : ℝ) : ℝ :=
  kdot (s3c1 n τ c) * min (s3Cpp n c - s3rpp n τ) 0 - s3e0 n τ ^ 2 - s3rs n τ η
/-- `n k_s = max(|𝖴|, |𝖫|)`. -/
noncomputable def s3nks (n : ℕ) (τ η c : ℝ) : ℝ := max |s3U n τ η c| |s3L n τ η c|

lemma s3_real_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {S : Set α}
    {r : ℝ} (hr : 0 ≤ r) (h : μ S ≤ ENNReal.ofReal r) : μ.real S ≤ r :=
  ENNReal.toReal_le_of_le_ofReal hr h

lemma s3_union {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {S T : Set α}
    {a b : ℝ} (hS : μ.real S ≤ a) (hT : μ.real T ≤ b) : μ.real (S ∪ T) ≤ a + b :=
  (measureReal_union_le S T).trans (add_le_add hS hT)

lemma s3_pa_eq {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (x x' e : Fin k → ℝ) :
    s3p x e A ⬝ᵥ reluV (A *ᵥ x') = ∑ i, mask ((A *ᵥ x) i) * (A *ᵥ e) i * relu ((A *ᵥ x') i) := by
  unfold dotProduct reluV
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s3p, s3_obD_mulVec]

lemma s3_pp_eq {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (x x' e e' : Fin k → ℝ) :
    s3p x e A ⬝ᵥ s3p x' e' A =
      ∑ i, (mask ((A *ᵥ x) i) * (A *ᵥ e) i) * (mask ((A *ᵥ x') i) * (A *ᵥ e') i) := by
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s3p, s3p, s3_obD_mulVec, s3_obD_mulVec]

lemma s3R_zero_left {m k : ℕ} (B : Matrix (Fin m) (Fin k) ℝ) (a a' p' : Fin k → ℝ) :
    s3R B a a' 0 p' = 0 := by
  unfold s3R; simp

lemma s3R_zero_right {m k : ℕ} (B : Matrix (Fin m) (Fin k) ℝ) (a a' p : Fin k → ℝ) :
    s3R B a a' p 0 = 0 := by
  unfold s3R; simp

/-- **The S block of Lemma TI under `nuA n`**: for a fixed pair of unit inputs with `c² < 1`
(`c = x·x'`, `e = eTan x x'`, `e' = eTan x' x`), the scalar `s = ⟨J(x)e, J(x')e'⟩` satisfies
`|s| ≤ n k_s = max(|𝖴|, |𝖫|)` except with probability `23 e^{−τ} + 2 e^{−2η²m}`. The constants are
the paper's (`s3ap`, …, `s3nks`); the hypotheses on them are the paper's conditions (`a₋ > 0`,
`d₋ ≥ 0`, `d₋² ≤ 2a₊²`, `c₁⁺ < 1`, the positive-factor condition `υ√γ ≤ (nV − r₁)/a₊` with
`nV − r₁ ≥ 0`). -/
theorem s3_Sblock (hn : 1 ≤ n) {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    (hc : (x ⬝ᵥ x') ^ 2 < 1) {τ η : ℝ} (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (ham : 0 < s3am n τ) (hdm : 0 ≤ s3dm n τ (x ⬝ᵥ x'))
    (h6 : s3dm n τ (x ⬝ᵥ x') ^ 2 ≤ 2 * s3ap n τ ^ 2) (hc1 : s3c1 n τ (x ⬝ᵥ x') < 1)
    (hr1 : 0 ≤ s3Cpa n (x ⬝ᵥ x') - s3r1 n τ)
    (hpos : s3e0 n τ ≤ (s3Cpa n (x ⬝ᵥ x') - s3r1 n τ) / s3ap n τ) :
    (nuA n).real {θ | s3nks n τ η (x ⬝ᵥ x') <
      |(jac θ.1 θ.2 x *ᵥ eTan x x') ⬝ᵥ (jac θ.1 θ.2 x' *ᵥ eTan x' x)|} ≤
      23 * exp (-τ) + 2 * exp (-2 * η ^ 2 * (mA n : ℕ)) := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hm : 0 < mA n := by unfold mA; positivity
  have hmR : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by exact_mod_cast hm
  have hP1 : IsProbabilityMeasure (gaussMat (mA n) n (2 / (n : ℝ))) := by
    unfold gaussMat; infer_instance
  have hPA : IsProbabilityMeasure (nuA n) := by unfold nuA gaussMat; infer_instance
  set c := x ⬝ᵥ x' with hcd
  have hc' : (x' ⬝ᵥ x) ^ 2 < 1 := by rw [dotProduct_comm]; exact hc
  obtain ⟨-, hee, hxe, -, -⟩ := sb_frame hx hx' hc
  obtain ⟨-, hee', hxe', -, -⟩ := sb_frame hx' hx hc'
  have he1 : normSq (eTan x x') = 1 := by rw [← ms_dot_self]; exact hee
  have he1' : normSq (eTan x' x) = 1 := by rw [← ms_dot_self]; exact hee'
  have hx0 : x ≠ 0 := by rintro rfl; simp [normSq] at hx
  have hx0' : x' ≠ 0 := by rintro rfl; simp [normSq] at hx'
  set e := eTan x x' with hed
  set e' := eTan x' x with hed'
  set μ₁ := gaussMat (mA n) n (2 / (n : ℝ)) with hμ₁
  set K := s3K n η with hKd
  set pp := s3pp n τ η with hppd
  set e0 := s3e0 n τ with he0d
  have hγ : √(2 / (n : ℝ)) = √(2 / (n : ℝ)) := rfl
  -- the first-layer bad sets
  set B1 := {M : Matrix (Fin (mA n)) (Fin n) ℝ | ¬ (0 < nmA x M ∧ 0 < nmA x' M ∧
        (reluV (M *ᵥ x) ⬝ᵥ reluV (M *ᵥ x')) / (nmA x M * nmA x' M) ≤ s3c1 n τ c)} with hB1
  set B2 := {M : Matrix (Fin (mA n)) (Fin n) ℝ | s3ap n τ ≤ nmA x M} with hB2
  set B3 := {M : Matrix (Fin (mA n)) (Fin n) ℝ | s3ap n τ ≤ nmA x' M} with hB3
  set B4 := {M : Matrix (Fin (mA n)) (Fin n) ℝ | nmA x M ≤ s3am n τ} with hB4
  set B5 := {M : Matrix (Fin (mA n)) (Fin n) ℝ | nmA x' M ≤ s3am n τ} with hB5
  set B6 := {G : Matrix (Fin (mA n)) (Fin n) ℝ | ((mA n : ℕ) : ℝ) * (1 / 2 + η) <
    ∑ i, mask ((G *ᵥ x) i)} with hB6
  set B7 := {G : Matrix (Fin (mA n)) (Fin n) ℝ | ((mA n : ℕ) : ℝ) * (1 / 2 + η) <
    ∑ i, mask ((G *ᵥ x') i)} with hB7
  set B8 := {A : Matrix (Fin (mA n)) (Fin n) ℝ | ∑ i, mask ((A *ᵥ x) i) ≤ K ∧
    pp ≤ nrm (obD (A *ᵥ x) *ᵥ (A *ᵥ e))} with hB8
  set B9 := {A : Matrix (Fin (mA n)) (Fin n) ℝ | ∑ i, mask ((A *ᵥ x') i) ≤ K ∧
    pp ≤ nrm (obD (A *ᵥ x') *ᵥ (A *ᵥ e'))} with hB9
  set B10 := {A : Matrix (Fin (mA n)) (Fin n) ℝ | e0 < |((nrm (reluV (A *ᵥ x)))⁻¹ •
    reluV (A *ᵥ x)) ⬝ᵥ (obD (A *ᵥ x) *ᵥ (A *ᵥ e))|} with hB10
  set B11 := {A : Matrix (Fin (mA n)) (Fin n) ℝ | e0 < |((nrm (reluV (A *ᵥ x')))⁻¹ •
    reluV (A *ᵥ x')) ⬝ᵥ (obD (A *ᵥ x') *ᵥ (A *ᵥ e'))|} with hB11
  set B12 := {A : Matrix (Fin (mA n)) (Fin n) ℝ | 2 * (3 * (2 / (n : ℝ))) *
      (√(2 * (mA n : ℕ) * τ) + τ) <
    |∑ i, mask ((A *ᵥ x) i) * (A *ᵥ e) i * relu ((A *ᵥ x') i) -
      ((mA n : ℕ) : ℝ) * (2 / (n : ℝ)) * (√(1 - (x ⬝ᵥ x') ^ 2) * kdot (x ⬝ᵥ x')) / 2|} with hB12
  set B13 := {A : Matrix (Fin (mA n)) (Fin n) ℝ | 2 * (3 * (2 / (n : ℝ))) *
      (√(2 * (mA n : ℕ) * τ) + τ) <
    |∑ i, mask ((A *ᵥ x') i) * (A *ᵥ e') i * relu ((A *ᵥ x) i) -
      ((mA n : ℕ) : ℝ) * (2 / (n : ℝ)) * (√(1 - (x' ⬝ᵥ x) ^ 2) * kdot (x' ⬝ᵥ x)) / 2|} with hB13
  set B14 := {A : Matrix (Fin (mA n)) (Fin n) ℝ | 2 * (2 * (2 / (n : ℝ))) *
      (√(2 * (mA n : ℕ) * τ) + τ) <
    |∑ i, (mask ((A *ᵥ x) i) * (A *ᵥ e) i) * (mask ((A *ᵥ x') i) * (A *ᵥ e') i) -
      ((mA n : ℕ) : ℝ) * (2 / (n : ℝ)) * (√(1 - (x ⬝ᵥ x') ^ 2) / π - (x ⬝ᵥ x') * kdot (x ⬝ᵥ x')) /
        2|} with hB14
  set Bad := B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6 ∪ B7 ∪ B8 ∪ B9 ∪ B10 ∪ B11 ∪ B12 ∪ B13 ∪ B14 with hBad
  -- the tails
  have t1 : μ₁.real B1 ≤ 5 * exp (-τ) := nm_overlap_tail hn hx hx' hτ ham hdm h6
  have t2 : μ₁.real B2 ≤ exp (-τ) := nm_tail_a_upper hn hx hτ
  have t3 : μ₁.real B3 ≤ exp (-τ) := nm_tail_a_upper hn hx' hτ
  have t4 : μ₁.real B4 ≤ exp (-τ) := nm_tail_a_lower hn hx hτ
  have t5 : μ₁.real B5 ≤ exp (-τ) := nm_tail_a_lower hn hx' hτ
  have t6 : μ₁.real B6 ≤ exp (-2 * η ^ 2 * (mA n : ℕ)) := single_tail hv hx0 hη
  have t7 : μ₁.real B7 ≤ exp (-2 * η ^ 2 * (mA n : ℕ)) := single_tail hv hx0' hη
  have t8 : μ₁.real B8 ≤ exp (-τ) :=
    s3_real_le (exp_pos _).le (ob_p_tail hv hx he1 hxe hτ)
  have t9 : μ₁.real B9 ≤ exp (-τ) :=
    s3_real_le (exp_pos _).le (ob_p_tail hv hx' he1' hxe' hτ)
  have t10 : μ₁.real B10 ≤ 2 * exp (-τ) :=
    s3_real_le (by positivity) (ob_eps_tail hv hx he1 hxe hτ)
  have t11 : μ₁.real B11 ≤ 2 * exp (-τ) :=
    s3_real_le (by positivity) (ob_eps_tail hv hx' he1' hxe' hτ)
  have t12 : μ₁.real B12 ≤ 2 * exp (-τ) := sb_tail_pa hv hx hx' hc hm hτ
  have t13 : μ₁.real B13 ≤ 2 * exp (-τ) := sb_tail_pa hv hx' hx hc' hm hτ
  have t14 : μ₁.real B14 ≤ 2 * exp (-τ) := sb_tail_pp hv hx hx' hc hm hτ
  have tBad : μ₁.real Bad ≤ 21 * exp (-τ) + 2 * exp (-2 * η ^ 2 * (mA n : ℕ)) := by
    have := s3_union (s3_union (s3_union (s3_union (s3_union (s3_union (s3_union (s3_union
      (s3_union (s3_union (s3_union (s3_union (s3_union t1 t2) t3) t4) t5) t6) t7) t8) t9) t10)
      t11) t12) t13) t14
    linarith
  -- the conditional step
  set C := {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      s3G1 x x' e e' pp θ.1 ∧
      2 * (2 / ((mA n : ℕ) : ℝ) * pp ^ 2) * (√(2 * (mA n : ℕ) * τ) + τ) <
        |s3R θ.2 (reluV (θ.1 *ᵥ x)) (reluV (θ.1 *ᵥ x')) (s3p x e θ.1) (s3p x' e' θ.1) -
          s3M (mA n) (2 / ((mA n : ℕ) : ℝ)) (reluV (θ.1 *ᵥ x)) (reluV (θ.1 *ᵥ x'))
            (s3p x e θ.1) (s3p x' e' θ.1)|} with hCd
  have tC : (nuA n).real C ≤ 2 * exp (-τ) := s3_cond_tail hn x x' e e' hτ
  have tprod : (nuA n).real (Bad ×ˢ Set.univ) = μ₁.real Bad := by
    unfold nuA
    rw [Measure.real, Measure.prod_prod, measure_univ, mul_one]
    rfl
  -- the deterministic step
  have hsub : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      s3nks n τ η c < |(jac θ.1 θ.2 x *ᵥ e) ⬝ᵥ (jac θ.1 θ.2 x' *ᵥ e')|} ⊆
      (Bad ×ˢ Set.univ) ∪ C := by
    intro θ hθ
    by_contra hno
    simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, not_or] at hno
    obtain ⟨hnB, hnC⟩ := hno
    simp only [hBad, Set.mem_union, not_or] at hnB
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨n1, n2⟩, n3⟩, n4⟩, n5⟩, n6⟩, n7⟩, n8⟩, n9⟩, n10⟩, n11⟩, n12⟩, n13⟩, n14⟩ :=
      hnB
    apply (lt_irrefl (s3nks n τ η c)).elim
    refine lt_of_lt_of_le hθ ?_
    rw [s3_scalar_eq]
    set A := θ.1 with hAd
    set B := θ.2 with hBd
    set a := reluV (A *ᵥ x) with had
    set a' := reluV (A *ᵥ x') with had'
    set p := s3p x e A with hpd
    set p' := s3p x' e' A with hpd'
    have hnks0 : 0 ≤ s3nks n τ η c := le_max_of_le_left (abs_nonneg _)
    -- the first-layer norms
    have hNa1 : s3am n τ < √(normSq a) := not_le.mp n4
    have hNa2 : √(normSq a) < s3ap n τ := not_le.mp n2
    have hNb1 : s3am n τ < √(normSq a') := not_le.mp n5
    have hNb2 : √(normSq a') < s3ap n τ := not_le.mp n3
    have ha0 : 0 < normSq a := Real.sqrt_pos.mp (ham.trans hNa1)
    have hb0 : 0 < normSq a' := Real.sqrt_pos.mp (ham.trans hNb1)
    -- the overlap
    have hcos : (a ⬝ᵥ a') / (√(normSq a) * √(normSq a')) ≤ s3c1 n τ c := (not_not.mp n1).2.2
    set q := s2_unit a ⬝ᵥ s2_unit a' with hqd
    have hq1 : q ≤ s3c1 n τ c := by rw [hqd, s3_unit_dot]; exact hcos
    have hq0 : 0 ≤ q := by
      rw [hqd, s3_unit_dot]
      exact div_nonneg (s3_relu_dot_nonneg _ _) (by positivity)
    have hq2 : q ^ 2 < 1 := by
      have h1 : q < 1 := lt_of_le_of_lt hq1 hc1
      nlinarith only [h1, hq0]
    -- the tangent lengths
    have hcnt : ∑ i, mask ((A *ᵥ x) i) ≤ K := not_lt.mp n6
    have hcnt' : ∑ i, mask ((A *ᵥ x') i) ≤ K := not_lt.mp n7
    have hpn : √(normSq p) < pp := by
      by_contra h; exact n8 ⟨hcnt, not_lt.mp h⟩
    have hpn' : √(normSq p') < pp := by
      by_contra h; exact n9 ⟨hcnt', not_lt.mp h⟩
    by_cases hp0 : normSq p = 0
    · rw [BstLean.Part134.eq_zero_of_normSq hp0, s3R_zero_left, abs_zero]; exact hnks0
    by_cases hp0' : normSq p' = 0
    · rw [BstLean.Part134.eq_zero_of_normSq hp0', s3R_zero_right, abs_zero]; exact hnks0
    have hpp0 : 0 < normSq p := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Ne.symm hp0)
    have hpp0' : 0 < normSq p' := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Ne.symm hp0')
    -- the conditional deviation
    have hG1 : s3G1 x x' e e' pp A := ⟨ha0, hb0, hq2, hpp0, hpp0', hpn.le, hpn'.le⟩
    have hdev : |s3R B a a' p p' - s3M (mA n) (2 / ((mA n : ℕ) : ℝ)) a a' p p'| ≤
        2 * (2 / ((mA n : ℕ) : ℝ) * pp ^ 2) * (√(2 * (mA n : ℕ) * τ) + τ) :=
      not_lt.mp fun h => hnC ⟨hG1, h⟩
    have hmt : ((mA n : ℕ) : ℝ) * (2 / ((mA n : ℕ) : ℝ)) = 2 := by field_simp
    rw [s3_mean_eq (by positivity) hmt (s3_ne_of_pos ha0) (s3_ne_of_pos hb0) hq2] at hdev
    -- the tangent components
    have hε : |p ⬝ᵥ s2_unit a| ≤ e0 := by
      have h : |s2_unit a ⬝ᵥ p| ≤ e0 := not_lt.mp n10
      rwa [dotProduct_comm] at h
    have hε' : |p' ⬝ᵥ s2_unit a'| ≤ e0 := by
      have h : |s2_unit a' ⬝ᵥ p'| ≤ e0 := not_lt.mp n11
      rwa [dotProduct_comm] at h
    -- the positive factors
    have hD1 : |p ⬝ᵥ a' - s3Cpa n c| ≤ s3r1 n τ := by
      have h : |∑ i, mask ((A *ᵥ x) i) * (A *ᵥ e) i * relu ((A *ᵥ x') i) - s3Cpa n c| ≤
          s3r1 n τ := not_lt.mp n12
      rwa [← s3_pa_eq] at h
    have hD2 : |p' ⬝ᵥ a - s3Cpa n c| ≤ s3r1 n τ := by
      have h : |∑ i, mask ((A *ᵥ x') i) * (A *ᵥ e') i * relu ((A *ᵥ x) i) -
          ((mA n : ℕ) : ℝ) * (2 / (n : ℝ)) * (√(1 - (x' ⬝ᵥ x) ^ 2) * kdot (x' ⬝ᵥ x)) / 2| ≤
          s3r1 n τ := not_lt.mp n13
      rw [← s3_pa_eq, dotProduct_comm x' x] at h
      exact h
    have hqle : q ≤ 1 := hq1.trans hc1.le
    obtain ⟨hF1, hF1'⟩ := s3_lam hD1 hNb1 hNb2 ham hε hq0 hqle hr1 hpos
    obtain ⟨hF2, hF2'⟩ := s3_lam hD2 hNa1 hNa2 ham hε' hq0 hqle hr1 hpos
    rw [← s3_dot_unit] at hF1 hF1' hF2 hF2'
    have hPP : |p ⬝ᵥ p' - s3Cpp n c| ≤ s3rpp n τ := by
      have h : |∑ i, (mask ((A *ᵥ x) i) * (A *ᵥ e) i) * (mask ((A *ᵥ x') i) * (A *ᵥ e') i) -
          s3Cpp n c| ≤ s3rpp n τ := not_lt.mp n14
      rwa [← s3_pp_eq] at h
    obtain ⟨hPL, hPU⟩ := abs_le.1 hPP
    have he00 : 0 ≤ e0 := (abs_nonneg _).trans hε
    have hR : |p ⬝ᵥ s2_unit a| * |p' ⬝ᵥ s2_unit a'| ≤ e0 ^ 2 := by
      rw [sq]; exact mul_le_mul hε hε' (abs_nonneg _) he00
    obtain ⟨hup, hlo⟩ := s2_scalar_det hq0 hq1 hc1 (show s3Cpp n c - s3rpp n τ ≤ p ⬝ᵥ p' by linarith only [hPL])
      (show p ⬝ᵥ p' ≤ s3Cpp n c + s3rpp n τ by linarith only [hPU]) hF1 hF1' hF2 hF2' hR hdev
    rw [abs_le]
    constructor
    · have h1 : -s3nks n τ η c ≤ -|s3L n τ η c| := neg_le_neg (le_max_right _ _)
      have h2 : -|s3L n τ η c| ≤ s3L n τ η c := neg_abs_le _
      exact h1.trans (h2.trans hlo)
    · exact hup.trans ((le_abs_self _).trans (le_max_left _ _))
  calc (nuA n).real {θ | s3nks n τ η c < |(jac θ.1 θ.2 x *ᵥ e) ⬝ᵥ (jac θ.1 θ.2 x' *ᵥ e')|}
      ≤ (nuA n).real ((Bad ×ˢ Set.univ) ∪ C) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (nuA n).real (Bad ×ˢ Set.univ) + (nuA n).real C := measureReal_union_le _ _
    _ ≤ 23 * exp (-τ) + 2 * exp (-2 * η ^ 2 * (mA n : ℕ)) := by
        rw [tprod]; linarith only [tBad, tC]

end BstLean.Part182

open BstLean.Part182 in
#print axioms s3_scalar_eq
open BstLean.Part182 in
#print axioms s3_cond_tail
open BstLean.Part182 in
#print axioms s3_mean_eq
open BstLean.Part182 in
#print axioms s3_Sblock
