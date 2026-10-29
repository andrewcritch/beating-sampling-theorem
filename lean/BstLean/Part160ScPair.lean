import BstLean.Part160Eb
import BstLean.Part160Cov

/-!
# Part 160 (file `ScPair`): the mean of the squared first-layer mean as a pair integral

Do not use `sorry`, `native_decide` or `axiom`.

Notation: `y = c + τ ξ`, `y′ = c + τ ξ′` (`ξ`, `ξ′` independent standard Gaussian vectors),
`h̄_i = hO A₁ c τ i = E_ξ relu((A₁ y)_i)`, `A₁ ∼ gaussMat m n (2/n)`.

* `kappa_neg_eq`: `κ(−t) = κ(t) − t`; `kappa_quad_all`: `κ(r) ≤ 1/π + r/2 + (1/2 − 1/π) r²` on
  `[−1, 1]`.
* `pair_bound`: `a b κ(d/(ab)) ≤ ab/π + d/2 + (1/2 − 1/π)(d²/a² + d²/b²)/2` for `|d| ≤ ab`.
* `Kn c τ (ξ, ξ′) = |y||y′| κ(⟨y, y′⟩/(|y||y′|))`.
* `hO_sq_mean`: `E_{A₁} h̄_i² = (1/n)·E_{ξ,ξ′} Kn` (Fubini and the Gaussian ReLU pair identity
  `row_formula` of Part 130).
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part150 (hO froSq)
open BstLean.Part153 (nrm)

variable {n m : ℕ}

/-- `κ(−t) = κ(t) − t`. -/
lemma kappa_neg_eq (t : ℝ) : kappa (-t) = kappa t - t := by
  unfold kappa
  rw [neg_sq, Real.arccos_neg]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- `κ(r) ≤ 1/π + r/2 + (1/2 − 1/π) r²` on `[−1, 1]`. -/
theorem kappa_quad_all {r : ℝ} (h0 : -1 ≤ r) (h1 : r ≤ 1) :
    kappa r ≤ 1 / π + r / 2 + (1 / 2 - 1 / π) * r ^ 2 := by
  rcases le_total 0 r with hr | hr
  · exact kappa_quad hr h1
  · have h := kappa_quad (r := -r) (by linarith) (by linarith)
    rw [kappa_neg_eq, neg_sq] at h
    linarith

lemma c2_nonneg : (0 : ℝ) ≤ 1 / 2 - 1 / π := by
  have h := Real.pi_gt_three
  have : 1 / π ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith

/-- **The pair bound**: for `a, b ≥ 0` and `|d| ≤ ab`:
`a b κ(d/(ab)) ≤ ab/π + d/2 + (1/2 − 1/π)(d²/a² + d²/b²)/2`. -/
theorem pair_bound {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : |d| ≤ a * b) :
    a * b * kappa (d / (a * b)) ≤
      a * b / π + d / 2 + (1 / 2 - 1 / π) * ((d ^ 2 / a ^ 2 + d ^ 2 / b ^ 2) / 2) := by
  have hc2 := c2_nonneg
  rcases eq_or_lt_of_le (mul_nonneg ha hb) with hab | hab
  · have hd0 : d = 0 := by
      rw [← hab] at hd
      exact abs_eq_zero.mp (le_antisymm hd (abs_nonneg d))
    rw [← hab, hd0]
    simp
  · have ha0 : 0 < a := by
      rcases eq_or_lt_of_le ha with h | h
      · rw [← h, zero_mul] at hab; exact absurd hab (lt_irrefl _)
      · exact h
    have hb0 : 0 < b := by
      rcases eq_or_lt_of_le hb with h | h
      · rw [← h, mul_zero] at hab; exact absurd hab (lt_irrefl _)
      · exact h
    have hr : -1 ≤ d / (a * b) ∧ d / (a * b) ≤ 1 := by
      obtain ⟨h1, h2⟩ := abs_le.mp hd
      constructor
      · rw [le_div_iff₀ hab]; linarith
      · rw [div_le_one hab]; exact h2
    have hq := kappa_quad_all hr.1 hr.2
    have h1 := mul_le_mul_of_nonneg_left hq hab.le
    have e1 : a * b * (1 / π + d / (a * b) / 2 + (1 / 2 - 1 / π) * (d / (a * b)) ^ 2) =
        a * b / π + d / 2 + (1 / 2 - 1 / π) * (d ^ 2 * (a⁻¹ * b⁻¹)) := by
      field_simp
    rw [e1] at h1
    have h2 : d ^ 2 * (a⁻¹ * b⁻¹) ≤ (d ^ 2 / a ^ 2 + d ^ 2 / b ^ 2) / 2 := by
      have e2 : (d ^ 2 / a ^ 2 + d ^ 2 / b ^ 2) / 2 = d ^ 2 * ((a⁻¹ ^ 2 + b⁻¹ ^ 2) / 2) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, inv_pow, inv_pow]; ring
      rw [e2]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg d)
      nlinarith [sq_nonneg (a⁻¹ - b⁻¹)]
    have h3 := mul_le_mul_of_nonneg_left h2 hc2
    linarith

/-- The pair kernel `|y||y′| κ(⟨y, y′⟩/(|y||y′|))`, `y = c + τ ξ`, `y′ = c + τ ξ′`. -/
noncomputable def Kn (c : Fin n → ℝ) (τ : ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  nrm (c + τ • z.1) * nrm (c + τ • z.2) *
    kappa ((∑ j, (c + τ • z.1) j * (c + τ • z.2) j) / (nrm (c + τ • z.1) * nrm (c + τ • z.2)))

lemma continuous_shift (c : Fin n → ℝ) (τ : ℝ) : Continuous (fun ξ : Fin n → ℝ => c + τ • ξ) :=
  continuous_const.add (continuous_const_smul τ)

lemma measurable_nrm1 (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => nrm (c + τ • z.1)) :=
  (measurable_nrmShift c τ).comp measurable_fst

lemma measurable_nrm2 (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => nrm (c + τ • z.2)) :=
  (measurable_nrmShift c τ).comp measurable_snd

lemma measurable_dotz (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => ∑ j, (c + τ • z.1) j * (c + τ • z.2) j) := by
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_pi_apply j).comp ((continuous_shift c τ).measurable.comp measurable_fst)).mul
    ((measurable_pi_apply j).comp ((continuous_shift c τ).measurable.comp measurable_snd))

lemma measurable_Kn (c : Fin n → ℝ) (τ : ℝ) : Measurable (Kn c τ) := by
  unfold Kn
  exact ((measurable_nrm1 c τ).mul (measurable_nrm2 c τ)).mul
    (continuous_kappa.measurable.comp
      ((measurable_dotz c τ).div ((measurable_nrm1 c τ).mul (measurable_nrm2 c τ))))

lemma dot_abs_le (y y' : Fin n → ℝ) : |∑ j, y j * y' j| ≤ nrm y * nrm y' := abs_dot_le y y'

lemma Kn_bounds (c : Fin n → ℝ) (τ : ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    0 ≤ Kn c τ z ∧ Kn c τ z ≤ nrm (c + τ • z.1) * nrm (c + τ • z.2) := by
  have ha := BstLean.Part153.nrm_nonneg (c + τ • z.1)
  have hb := BstLean.Part153.nrm_nonneg (c + τ • z.2)
  have hab := mul_nonneg ha hb
  have hd := dot_abs_le (c + τ • z.1) (c + τ • z.2)
  have hr : -1 ≤ (∑ j, (c + τ • z.1) j * (c + τ • z.2) j) /
      (nrm (c + τ • z.1) * nrm (c + τ • z.2)) ∧
      (∑ j, (c + τ • z.1) j * (c + τ • z.2) j) /
      (nrm (c + τ • z.1) * nrm (c + τ • z.2)) ≤ 1 := by
    rcases eq_or_lt_of_le hab with h0 | h0
    · rw [← h0, div_zero]; constructor <;> norm_num
    · obtain ⟨h1, h2⟩ := abs_le.mp hd
      constructor
      · rw [le_div_iff₀ h0]; linarith
      · rw [div_le_one h0]; exact h2
  obtain ⟨k0, k1⟩ := kappa_mem hr.1 hr.2
  unfold Kn
  exact ⟨mul_nonneg hab k0, by nlinarith⟩

lemma integrable_nrmShift (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (fun ξ : Fin n → ℝ => nrm (c + τ • ξ)) (stdGauss (Fin n)) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add (BstLean.Part153.int_normSq_shift c τ).1)
    (measurable_nrmShift c τ).aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  have h0 := BstLean.Part153.nrm_nonneg (c + τ • ξ)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  have h2 := BstLean.Part153.nrm_sq (c + τ • ξ)
  show nrm (c + τ • ξ) ≤ 1 + normSq (c + τ • ξ)
  nlinarith [sq_nonneg (nrm (c + τ • ξ) - 1)]

lemma integrable_nrm_prod (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => nrm (c + τ • z.1) * nrm (c + τ • z.2))
      ((stdGauss (Fin n)).prod (stdGauss (Fin n))) :=
  (integrable_nrmShift c τ).mul_prod (integrable_nrmShift c τ)

lemma integrable_Kn (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (Kn c τ) ((stdGauss (Fin n)).prod (stdGauss (Fin n))) := by
  refine Integrable.mono' (integrable_nrm_prod c τ) (measurable_Kn c τ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Kn_bounds c τ z).1]
  exact (Kn_bounds c τ z).2

/-- `|(A y)_i| ≤ √(froSq A)·|y|`. -/
lemma abs_mulVec_le (A : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) (i : Fin m) :
    |(A.mulVec y) i| ≤ √(froSq A) * nrm y := by
  have h1 : |∑ j, A i j * y j| ≤ √(normSq (fun j => A i j)) * √(normSq y) :=
    abs_dot_le (fun j => A i j) y
  have h2 : normSq (fun j => A i j) ≤ froSq A := by
    unfold froSq normSq
    exact Finset.single_le_sum (f := fun i => ∑ j, A i j ^ 2)
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ i)
  calc |(A.mulVec y) i| = |∑ j, A i j * y j| := rfl
    _ ≤ √(normSq (fun j => A i j)) * √(normSq y) := h1
    _ ≤ √(froSq A) * nrm y :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)

/-- **The mean of the squared first-layer mean** (Fubini and the pair identity):
`E_{A₁} h̄_i² = (1/n)·E_{ξ,ξ′}[|y||y′| κ(⟨y, y′⟩/(|y||y′|))]`. -/
theorem hO_sq_mean (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (i : Fin m) :
    Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => hO A c τ i ^ 2) (gaussMat m n (2 / (n : ℝ))) ∧
    ∫ A : Matrix (Fin m) (Fin n) ℝ, hO A c τ i ^ 2 ∂gaussMat m n (2 / (n : ℝ)) =
      1 / (n : ℝ) * ∫ z, Kn c τ z ∂((stdGauss (Fin n)).prod (stdGauss (Fin n))) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hv : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  obtain ⟨f, hf⟩ : ∃ f : Matrix (Fin m) (Fin n) ℝ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ,
      f = fun A z => relu ((A.mulVec (c + τ • z.1)) i) * relu ((A.mulVec (c + τ • z.2)) i) :=
    ⟨_, rfl⟩
  have hfc : Continuous (Function.uncurry f) := by
    rw [hf]
    have h1 : Continuous (fun p : Matrix (Fin m) (Fin n) ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        (p.1.mulVec (c + τ • p.2.1)) i) :=
      (continuous_apply i).comp (Continuous.matrix_mulVec continuous_fst
        ((continuous_shift c τ).comp (continuous_fst.comp continuous_snd)))
    have h2 : Continuous (fun p : Matrix (Fin m) (Fin n) ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        (p.1.mulVec (c + τ • p.2.2)) i) :=
      (continuous_apply i).comp (Continuous.matrix_mulVec continuous_fst
        ((continuous_shift c τ).comp (continuous_snd.comp continuous_snd)))
    exact (continuous_relu.comp h1).mul (continuous_relu.comp h2)
  have hf0 : ∀ A z, 0 ≤ f A z := fun A z => by
    rw [hf]; exact mul_nonneg (relu_nonneg _) (relu_nonneg _)
  have h1 : ∀ A, Integrable (f A) ((stdGauss (Fin n)).prod (stdGauss (Fin n))) := fun A => by
    rw [hf]
    exact (BstLean.Part150.hO_eq_gauss A c τ i).1.mul_prod (BstLean.Part150.hO_eq_gauss A c τ i).1
  have hsq : ∀ A, hO A c τ i ^ 2 =
      ∫ z, f A z ∂((stdGauss (Fin n)).prod (stdGauss (Fin n))) := fun A => by
    have hp := integral_prod_mul (μ := stdGauss (Fin n)) (ν := stdGauss (Fin n))
      (fun ξ : Fin n → ℝ => relu ((A.mulVec (c + τ • ξ)) i))
      (fun ξ : Fin n → ℝ => relu ((A.mulVec (c + τ • ξ)) i))
    rw [← (BstLean.Part150.hO_eq_gauss A c τ i).2] at hp
    rw [hf, sq]
    exact hp.symm
  have h2 : ∀ z, Integrable (fun A => f A z) (gaussMat m n (2 / (n : ℝ))) ∧
      ∫ A, f A z ∂gaussMat m n (2 / (n : ℝ)) = 1 / (n : ℝ) * Kn c τ z := by
    intro z
    constructor
    · have hm : Measurable (fun A => f A z) :=
        (hfc.comp (Continuous.prodMk continuous_id continuous_const)).measurable
      refine Integrable.mono' ((BstLean.Part150.froSq_integral (m := m) hn).1.mul_const
        (nrm (c + τ • z.1) * nrm (c + τ • z.2))) hm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun A => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 A z), hf]
      have a1 := abs_mulVec_le A (c + τ • z.1) i
      have a2 := abs_mulVec_le A (c + τ • z.2) i
      have r1 := (relu_nonneg ((A.mulVec (c + τ • z.1)) i))
      have r2 := (relu_nonneg ((A.mulVec (c + τ • z.2)) i))
      have b1 : relu ((A.mulVec (c + τ • z.1)) i) ≤ √(froSq A) * nrm (c + τ • z.1) :=
        (le_abs_self _).trans ((abs_relu_le _).trans a1)
      have b2 : relu ((A.mulVec (c + τ • z.2)) i) ≤ √(froSq A) * nrm (c + τ • z.2) :=
        (le_abs_self _).trans ((abs_relu_le _).trans a2)
      have hF : 0 ≤ froSq A := by
        unfold froSq; exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
      calc relu ((A.mulVec (c + τ • z.1)) i) * relu ((A.mulVec (c + τ • z.2)) i)
          ≤ (√(froSq A) * nrm (c + τ • z.1)) * (√(froSq A) * nrm (c + τ • z.2)) :=
            mul_le_mul b1 b2 r2 (mul_nonneg (Real.sqrt_nonneg _) (BstLean.Part153.nrm_nonneg _))
        _ = froSq A * (nrm (c + τ • z.1) * nrm (c + τ • z.2)) := by
            have := Real.mul_self_sqrt hF
            calc _ = (√(froSq A) * √(froSq A)) * (nrm (c + τ • z.1) * nrm (c + τ • z.2)) := by ring
              _ = _ := by rw [this]
    · have hr := row_formula (m := m) hv (c + τ • z.1) (c + τ • z.2) i
      rw [hf]
      unfold Kn nrm
      have : (2 : ℝ) / n * (√(normSq (c + τ • z.1)) * √(normSq (c + τ • z.2)) *
          kappa ((∑ j, (c + τ • z.1) j * (c + τ • z.2) j) /
            (√(normSq (c + τ • z.1)) * √(normSq (c + τ • z.2))))) =
          2 * (1 / (n : ℝ) * (√(normSq (c + τ • z.1)) * √(normSq (c + τ • z.2)) *
          kappa ((∑ j, (c + τ • z.1) j * (c + τ • z.2) j) /
            (√(normSq (c + τ • z.1)) * √(normSq (c + τ • z.2)))))) := by ring
      rw [this] at hr
      linarith
  obtain ⟨hi, he⟩ := BstLean.Part153.integral_swap_of_nonneg
    (ν := gaussMat m n (2 / (n : ℝ))) (μ := (stdGauss (Fin n)).prod (stdGauss (Fin n)))
    hfc.measurable hf0 h1 (b := fun z => 1 / (n : ℝ) * Kn c τ z) h2
    ((integrable_Kn c τ).const_mul _)
  simp_rw [hsq]
  refine ⟨hi, ?_⟩
  rw [he, integral_const_mul]

end BstLean.Part160

open BstLean.Part160 in
#print axioms pair_bound
open BstLean.Part160 in
#print axioms hO_sq_mean
