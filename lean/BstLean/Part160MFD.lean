import BstLean.Part160MFAll
import BstLean.Part160Event

/-!
# Part 160 (file `MFD`): the smaller deviation of `|𝐝|` over `A₂` (change (D))

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-05-centre.tex`, Lemma `t7:p05:MA` (the event `E_D′`).

* `relu_slope`, `psiS_slope`: the increments of `relu` and of `ψ_s` are the increment of the
  argument times a number of `[0, 1]`.
* `row_lip`: one row of `𝐝` is Lipschitz with the constant `√(τ²·opN(A₁)² + |h̄₁|²)`.
* `dC_lip'`: `|𝐝|` is Lipschitz in `A₂` with the constant
  `L_D = √(t(τ²·opN(A₁)² + |h̄₁|²)) = √(ℓ² + Γ̄)` (the paper has `ℓ + √Γ̄`, which is larger;
  Part 154 has `2√Γ`).
* `BadD'`, `ED'_prob`: the new event of `A₂` and its charge `e^{−L_c}`.
* `SD' n`, `measurableSet_SD'`, `SD'_charge`: the event as a set of `AgFam n`, charge
  `615/10⁸` (`≥ e^{−12}`).
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152 BstLean.Part154
open BstLean.Part137 (psiS)
open BstLean.Part153 (nrm nrm_nonneg nrm_sq abs_dot_le_nrm abs_nrm_sub_le h1n memLp_h1n nuA)

/-- For `0 ≤ p ≤ 1`: `|relu a − relu b − p(a − b)| ≤ |a − b|`. -/
lemma relu_slope (a b : ℝ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |relu a - relu b - p * (a - b)| ≤ |a - b| := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [relu_of_nonneg ha, relu_of_nonneg hb]
    have e : a - b - p * (a - b) = (1 - p) * (a - b) := by ring
    rw [e, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - p)]
    exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)
  · rw [relu_of_nonneg ha, relu_of_nonpos hb, abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - b)]
    rw [abs_le]
    constructor <;> nlinarith
  · rw [relu_of_nonpos ha, relu_of_nonneg hb, abs_of_nonpos (by linarith : a - b ≤ 0)]
    rw [abs_le]
    constructor <;> nlinarith
  · rw [relu_of_nonpos ha, relu_of_nonpos hb]
    have e : (0 : ℝ) - 0 - p * (a - b) = -(p * (a - b)) := by ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg hp0]
    exact mul_le_of_le_one_left (abs_nonneg _) hp1

lemma relu_mono' {a b : ℝ} (h : a ≤ b) : relu a ≤ relu b := max_le_max le_rfl h

lemma psiS_mono (s : ℝ) {x x' : ℝ} (h : x ≤ x') : psiS s x ≤ psiS s x' := by
  unfold psiS
  exact integral_mono (BstLean.Part137.integrable_relu_shift x s)
    (BstLean.Part137.integrable_relu_shift x' s) fun z => relu_mono' (by linarith)

/-- `ψ_s(x) − ψ_s(x′) = p·(x − x′)` with `0 ≤ p ≤ 1`. -/
lemma psiS_slope (s x x' : ℝ) : ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ psiS s x - psiS s x' = p * (x - x') := by
  by_cases hxx : x = x'
  · exact ⟨0, le_rfl, zero_le_one, by rw [hxx]; ring⟩
  have hne : x - x' ≠ 0 := sub_ne_zero.mpr hxx
  have hl := BstLean.Part141.psiS_lip_x s x x'
  refine ⟨(psiS s x - psiS s x') / (x - x'), ?_, ?_, by field_simp⟩
  · rcases lt_or_gt_of_ne hxx with h | h
    · exact div_nonneg_of_nonpos (by linarith [psiS_mono s h.le]) (by linarith)
    · exact div_nonneg (by linarith [psiS_mono s h.le]) (by linarith)
  · rcases lt_or_gt_of_ne hxx with h | h
    · have h1 := psiS_mono s h.le
      rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)] at hl
      exact (div_le_one_of_neg (by linarith)).mpr (by linarith)
    · have h1 := psiS_mono s h.le
      rw [abs_of_nonneg (by linarith), abs_of_pos (by linarith)] at hl
      exact (div_le_one (by linarith)).mpr hl

variable {n m : ℕ}

lemma prob_stdGauss_D (n : ℕ) : IsProbabilityMeasure (stdGauss (Fin n)) := by
  unfold stdGauss; infer_instance

/-- **One row of `𝐝` is Lipschitz** with the constant `√(τ²·opN(A₁)² + |h̄₁|²)`. -/
theorem row_lip (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ s : ℝ) (a a' : Fin m → ℝ) :
    |(∫ ξ, relu (a ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ))) ∂stdGauss (Fin n) -
        psiS s (a ⬝ᵥ hO A₁ c τ)) -
      (∫ ξ, relu (a' ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ))) ∂stdGauss (Fin n) -
        psiS s (a' ⬝ᵥ hO A₁ c τ))| ≤
      nrm (a - a') * √(τ ^ 2 * opN A₁ ^ 2 + normSq (hO A₁ c τ)) := by
  have hμ := prob_stdGauss_D n
  set w : Fin m → ℝ := a - a' with hw
  obtain ⟨h, hh⟩ : ∃ h : (Fin n → ℝ) → Fin m → ℝ, h = fun ξ => reluV (A₁ *ᵥ (c + τ • ξ)) :=
    ⟨_, rfl⟩
  have hcont : Continuous h := by rw [hh]; exact BstLean.Part153.continuous_h1 A₁ c τ
  have hdotc : ∀ u : Fin m → ℝ, Continuous (fun ξ => u ⬝ᵥ h ξ) := fun u => by
    have : Continuous (fun v : Fin m → ℝ => u ⬝ᵥ v) := by unfold dotProduct; fun_prop
    exact this.comp hcont
  have hn1 : Integrable (fun ξ => nrm (h ξ)) (stdGauss (Fin n)) := by
    have := (memLp_h1n A₁ c τ).integrable one_le_two
    rw [hh]; exact this
  have hdoti : ∀ u : Fin m → ℝ, Integrable (fun ξ => u ⬝ᵥ h ξ) (stdGauss (Fin n)) := fun u =>
    Integrable.mono' (hn1.const_mul (nrm u)) (hdotc u).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs]; exact abs_dot_le_nrm _ _)
  have hreli : ∀ u : Fin m → ℝ, Integrable (fun ξ => relu (u ⬝ᵥ h ξ)) (stdGauss (Fin n)) :=
    fun u => Integrable.mono' (hn1.const_mul (nrm u))
      (continuous_relu.comp (hdotc u)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs]
        exact (abs_relu_le _).trans (abs_dot_le_nrm _ _))
  have hmean : ∀ u : Fin m → ℝ, ∫ ξ, u ⬝ᵥ h ξ ∂stdGauss (Fin n) = u ⬝ᵥ hO A₁ c τ := by
    intro u
    rw [hh]
    simp only [dotProduct, reluV]
    rw [integral_finsetSum _ fun i _ => (hO_eq_gauss A₁ c τ i).1.const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, (hO_eq_gauss A₁ c τ i).2]
  obtain ⟨p, hp0, hp1, hp⟩ := psiS_slope s (a ⬝ᵥ hO A₁ c τ) (a' ⬝ᵥ hO A₁ c τ)
  have hwdot : ∀ v : Fin m → ℝ, a ⬝ᵥ v - a' ⬝ᵥ v = w ⬝ᵥ v := fun v => by
    rw [hw, sub_dotProduct]
  -- the difference as one integral
  have e1 : (∫ ξ, relu (a ⬝ᵥ h ξ) ∂stdGauss (Fin n) - psiS s (a ⬝ᵥ hO A₁ c τ)) -
      (∫ ξ, relu (a' ⬝ᵥ h ξ) ∂stdGauss (Fin n) - psiS s (a' ⬝ᵥ hO A₁ c τ)) =
      ∫ ξ, (relu (a ⬝ᵥ h ξ) - relu (a' ⬝ᵥ h ξ) - p * (w ⬝ᵥ h ξ)) ∂stdGauss (Fin n) := by
    have i1 : Integrable (fun ξ => relu (a ⬝ᵥ h ξ) - relu (a' ⬝ᵥ h ξ)) (stdGauss (Fin n)) :=
      (hreli a).sub (hreli a')
    have hA : ∫ ξ, (relu (a ⬝ᵥ h ξ) - relu (a' ⬝ᵥ h ξ) - p * (w ⬝ᵥ h ξ)) ∂stdGauss (Fin n) =
        ∫ ξ, (relu (a ⬝ᵥ h ξ) - relu (a' ⬝ᵥ h ξ)) ∂stdGauss (Fin n) -
          ∫ ξ, p * (w ⬝ᵥ h ξ) ∂stdGauss (Fin n) := integral_sub i1 ((hdoti w).const_mul p)
    have hB : ∫ ξ, (relu (a ⬝ᵥ h ξ) - relu (a' ⬝ᵥ h ξ)) ∂stdGauss (Fin n) =
        ∫ ξ, relu (a ⬝ᵥ h ξ) ∂stdGauss (Fin n) - ∫ ξ, relu (a' ⬝ᵥ h ξ) ∂stdGauss (Fin n) :=
      integral_sub (hreli a) (hreli a')
    rw [hA, hB, integral_const_mul, hmean w, ← hwdot]
    linarith
  have e0 : (∫ ξ, relu (a ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ))) ∂stdGauss (Fin n) -
        psiS s (a ⬝ᵥ hO A₁ c τ)) -
      (∫ ξ, relu (a' ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ))) ∂stdGauss (Fin n) -
        psiS s (a' ⬝ᵥ hO A₁ c τ)) =
      (∫ ξ, relu (a ⬝ᵥ h ξ) ∂stdGauss (Fin n) - psiS s (a ⬝ᵥ hO A₁ c τ)) -
      (∫ ξ, relu (a' ⬝ᵥ h ξ) ∂stdGauss (Fin n) - psiS s (a' ⬝ᵥ hO A₁ c τ)) := by rw [hh]
  rw [e0, e1]
  -- the pointwise bound and Cauchy–Schwarz
  have hptw : ∀ ξ, |relu (a ⬝ᵥ h ξ) - relu (a' ⬝ᵥ h ξ) - p * (w ⬝ᵥ h ξ)| ≤ |w ⬝ᵥ h ξ| := by
    intro ξ
    have := relu_slope (a ⬝ᵥ h ξ) (a' ⬝ᵥ h ξ) hp0 hp1
    rwa [hwdot] at this
  have hcov0 := BstLean.Part153.covH_le A₁ c τ w
  have hcov : Integrable (fun ξ : Fin n → ℝ => (w ⬝ᵥ h ξ -
      ∫ ξ', w ⬝ᵥ h ξ' ∂stdGauss (Fin n)) ^ 2) (stdGauss (Fin n)) ∧
    ∫ ξ, (w ⬝ᵥ h ξ - ∫ ξ', w ⬝ᵥ h ξ' ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
      τ ^ 2 * opN A₁ ^ 2 * normSq w := by rw [hh]; exact hcov0
  rw [hmean w] at hcov
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = w ⬝ᵥ hO A₁ c τ := ⟨_, rfl⟩
  rw [← hM] at hcov
  have hsqi : Integrable (fun ξ => (w ⬝ᵥ h ξ) ^ 2) (stdGauss (Fin n)) := by
    have e : (fun ξ => (w ⬝ᵥ h ξ) ^ 2) =
        fun ξ => (w ⬝ᵥ h ξ - M) ^ 2 + (2 * M * (w ⬝ᵥ h ξ) - M ^ 2) := by
      funext ξ; ring
    rw [e]
    exact hcov.1.add (((hdoti w).const_mul _).sub (integrable_const _))
  have hsq : ∫ ξ, (w ⬝ᵥ h ξ) ^ 2 ∂stdGauss (Fin n) ≤
      (τ ^ 2 * opN A₁ ^ 2 + normSq (hO A₁ c τ)) * normSq w := by
    have e : ∀ ξ, (w ⬝ᵥ h ξ - M) ^ 2 = (w ⬝ᵥ h ξ) ^ 2 - 2 * M * (w ⬝ᵥ h ξ) + M ^ 2 :=
      fun ξ => by ring
    have h2 := hcov.2
    simp_rw [e] at h2
    have ea : ∫ ξ, ((w ⬝ᵥ h ξ) ^ 2 - 2 * M * (w ⬝ᵥ h ξ) + M ^ 2) ∂stdGauss (Fin n) =
        ∫ ξ, ((w ⬝ᵥ h ξ) ^ 2 - 2 * M * (w ⬝ᵥ h ξ)) ∂stdGauss (Fin n) +
          ∫ _ξ, M ^ 2 ∂stdGauss (Fin n) :=
      integral_add (hsqi.sub ((hdoti w).const_mul _)) (integrable_const _)
    have eb : ∫ ξ, ((w ⬝ᵥ h ξ) ^ 2 - 2 * M * (w ⬝ᵥ h ξ)) ∂stdGauss (Fin n) =
        ∫ ξ, (w ⬝ᵥ h ξ) ^ 2 ∂stdGauss (Fin n) - ∫ ξ, 2 * M * (w ⬝ᵥ h ξ) ∂stdGauss (Fin n) :=
      integral_sub hsqi ((hdoti w).const_mul _)
    rw [ea, eb, integral_const_mul, hmean w, ← hM, integral_const, probReal_univ,
      one_smul] at h2
    have hM2 : M ^ 2 ≤ normSq w * normSq (hO A₁ c τ) := by
      have h1 := abs_dot_le_nrm w (hO A₁ c τ)
      rw [← hM] at h1
      have h3 := pow_le_pow_left₀ (abs_nonneg M) h1 2
      rwa [sq_abs, mul_pow, nrm_sq, nrm_sq] at h3
    nlinarith
  have habs2 : Integrable (fun ξ => |w ⬝ᵥ h ξ| ^ 2) (stdGauss (Fin n)) := by
    simp_rw [sq_abs]; exact hsqi
  have hCS := BstLean.Part133.sq_integral_le (ρ := stdGauss (Fin n)) (f := fun ξ => |w ⬝ᵥ h ξ|)
    habs2
  simp_rw [sq_abs] at hCS
  have hI0 : 0 ≤ ∫ ξ, |w ⬝ᵥ h ξ| ∂stdGauss (Fin n) := integral_nonneg fun ξ => abs_nonneg _
  have hfin : ∫ ξ, |w ⬝ᵥ h ξ| ∂stdGauss (Fin n) ≤
      nrm w * √(τ ^ 2 * opN A₁ ^ 2 + normSq (hO A₁ c τ)) := by
    have hk : 0 ≤ τ ^ 2 * opN A₁ ^ 2 + normSq (hO A₁ c τ) :=
      add_nonneg (by positivity) (normSq_nonneg _)
    rw [← Real.sqrt_sq hI0]
    unfold BstLean.Part153.nrm
    rw [← Real.sqrt_mul (normSq_nonneg w)]
    refine Real.sqrt_le_sqrt ?_
    calc _ ≤ _ := hCS
      _ ≤ _ := hsq
      _ = _ := by ring
  calc |∫ ξ, (relu (a ⬝ᵥ h ξ) - relu (a' ⬝ᵥ h ξ) - p * (w ⬝ᵥ h ξ)) ∂stdGauss (Fin n)|
      ≤ ∫ ξ, |relu (a ⬝ᵥ h ξ) - relu (a' ⬝ᵥ h ξ) - p * (w ⬝ᵥ h ξ)| ∂stdGauss (Fin n) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ ξ, |w ⬝ᵥ h ξ| ∂stdGauss (Fin n) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => abs_nonneg _)
          (hdoti w).abs (Filter.Eventually.of_forall hptw)
    _ ≤ _ := hfin

/-- `L_D = √(t·(τ²·opN(A₁)² + |h̄₁|²)) = √(ℓ² + Γ̄)`. -/
noncomputable def LD (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  √(2 / (m : ℝ) * (τ ^ 2 * opN A₁ ^ 2 + normSq (hO A₁ c τ)))

lemma LD_nonneg (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) : 0 ≤ LD A₁ c τ :=
  Real.sqrt_nonneg _

/-- **Change (D)**: `|𝐝|` is Lipschitz in `A₂` with the constant `L_D = √(ℓ² + Γ̄)`. -/
theorem dC_lip' (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (A₂ A₂' : Matrix (Fin m) (Fin m) ℝ) :
    |dC A₁ A₂ c τ - dC A₁ A₂' c τ| ≤ LD A₁ c τ * √(∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) := by
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = τ ^ 2 * opN A₁ ^ 2 + normSq (hO A₁ c τ) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact add_nonneg (by positivity) (normSq_nonneg _)
  have hrow : ∀ j, ((hbar2 A₁ A₂ c τ - bO A₁ A₂ c τ) j -
      (hbar2 A₁ A₂' c τ - bO A₁ A₂' c τ) j) ^ 2 ≤
      normSq (fun k => A₂ j k - A₂' j k) * κ := by
    intro j
    have h := row_lip A₁ c τ (sO A₁ c τ) (fun k => A₂ j k) (fun k => A₂' j k)
    rw [← hκ] at h
    have e : (hbar2 A₁ A₂ c τ - bO A₁ A₂ c τ) j - (hbar2 A₁ A₂' c τ - bO A₁ A₂' c τ) j =
        (∫ ξ, relu ((fun k => A₂ j k) ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ))) ∂stdGauss (Fin n) -
          psiS (sO A₁ c τ) ((fun k => A₂ j k) ⬝ᵥ hO A₁ c τ)) -
        (∫ ξ, relu ((fun k => A₂' j k) ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ))) ∂stdGauss (Fin n) -
          psiS (sO A₁ c τ) ((fun k => A₂' j k) ⬝ᵥ hO A₁ c τ)) := rfl
    rw [e]
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs, mul_pow, nrm_sq, Real.sq_sqrt hκ0] at h2
    exact h2
  have hsum : normSq ((hbar2 A₁ A₂ c τ - bO A₁ A₂ c τ) -
      (hbar2 A₁ A₂' c τ - bO A₁ A₂' c τ)) ≤ (∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) * κ := by
    unfold normSq
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hrow j
  have hF0 : 0 ≤ ∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  unfold dC
  rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 := abs_nrm_sub_le (hbar2 A₁ A₂ c τ - bO A₁ A₂ c τ) (hbar2 A₁ A₂' c τ - bO A₁ A₂' c τ)
  have h2 : nrm ((hbar2 A₁ A₂ c τ - bO A₁ A₂ c τ) - (hbar2 A₁ A₂' c τ - bO A₁ A₂' c τ)) ≤
      √(∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) * √κ := by
    unfold BstLean.Part153.nrm
    rw [← Real.sqrt_mul hF0]
    exact Real.sqrt_le_sqrt hsum
  unfold LD
  rw [← hκ, Real.sqrt_mul (by positivity)]
  calc √(2 / (m : ℝ)) * |nrm (hbar2 A₁ A₂ c τ - bO A₁ A₂ c τ) -
        nrm (hbar2 A₁ A₂' c τ - bO A₁ A₂' c τ)|
      ≤ √(2 / (m : ℝ)) * (√(∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) * √κ) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- The complement of `E_D′`: `|𝐝| > E|𝐝| + √(2L_c t)·L_D`. -/
def BadD' (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) (Lc : ℝ) :
    Set (Matrix (Fin m) (Fin m) ℝ) :=
  {A₂ | ∫ A₂, dC A₁ A₂ c τ ∂gaussMat m m (2 / (m : ℝ)) +
      √(2 * Lc * (2 / (m : ℝ))) * LD A₁ c τ < dC A₁ A₂ c τ}

theorem ED'_prob (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) {Lc : ℝ}
    (hLc : 0 ≤ Lc) : (gaussMat m m (2 / (m : ℝ))).real (BadD' A₁ c τ Lc) ≤ rexp (-Lc) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hv : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  exact BstLean.Part153.conc_upper_strict (g := fun A₂ => dC A₁ A₂ c τ) (LD_nonneg A₁ c τ)
    (dC_lip' A₁ c τ) hv hLc

/-! ## The event as a set of `AgFam n` -/

/-- The good set of change (D), `L_c = 12`. -/
def SD' (n : ℕ) : Set (AgFam n) := {x | x.2.2 ∉ BadD' x.2.1 x.1.1 x.1.2 12}

lemma measurable_y_fam : Measurable (fun q : AgFam n × (Fin n → ℝ) => q.1.1.1 + q.1.1.2 • q.2) :=
  (measurable_fst.comp (measurable_fst.comp measurable_fst)).add
    ((measurable_snd.comp (measurable_fst.comp measurable_fst)).smul measurable_snd)

/-- `((c, τ), A₁, B) ↦ |𝐝|(A₁, B)` is measurable. -/
lemma measurable_dC_gen {X : Type*} [MeasurableSpace X] {c : X → Fin n → ℝ} {τ : X → ℝ}
    {A₁ : X → Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : X → Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (hc : Measurable c) (hτ : Measurable τ) (hA₁ : Measurable A₁) (hA₂ : Measurable A₂) :
    Measurable (fun x => dC (A₁ x) (A₂ x) (c x) (τ x)) := by
  have hmv1 : Continuous (fun q : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin n → ℝ) => q.1 *ᵥ q.2) :=
    Continuous.matrix_mulVec continuous_fst continuous_snd
  have hmv2 : Continuous (fun q : Matrix (Fin (mA n)) (Fin (mA n)) ℝ × (Fin (mA n) → ℝ) =>
      q.1 *ᵥ q.2) := Continuous.matrix_mulVec continuous_fst continuous_snd
  have hy : Measurable (fun q : X × (Fin n → ℝ) => c q.1 + τ q.1 • q.2) :=
    (hc.comp measurable_fst).add ((hτ.comp measurable_fst).smul measurable_snd)
  have h1 : Measurable (fun q : X × (Fin n → ℝ) => reluV (A₁ q.1 *ᵥ (c q.1 + τ q.1 • q.2))) :=
    continuous_reluV.measurable.comp (hmv1.measurable.comp ((hA₁.comp measurable_fst).prodMk hy))
  have hb2 : Measurable (fun x => hbar2 (A₁ x) (A₂ x) (c x) (τ x)) := by
    refine measurable_pi_iff.mpr fun j => ?_
    have hF : Measurable (fun q : X × (Fin n → ℝ) =>
        hid2 (A₁ q.1) (A₂ q.1) (c q.1 + τ q.1 • q.2) j) :=
      (measurable_pi_apply j).comp (continuous_reluV.measurable.comp
        (hmv2.measurable.comp ((hA₂.comp measurable_fst).prodMk h1)))
    unfold hbar2
    exact (hF.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable
  have hbo : Measurable (fun x => bO (A₁ x) (A₂ x) (c x) (τ x)) := by
    have h := (measurable_bO (n := n) (m := mA n)).comp
      (((hc.prodMk hτ).prodMk (hA₁.prodMk hA₂)) :
        Measurable (fun x => (((c x, τ x), (A₁ x, A₂ x)) :
          ((Fin n → ℝ) × ℝ) × BstLean.Part136.HidParam n (mA n))))
    simpa only [Function.comp_def] using h
  unfold dC
  exact ((continuous_normSq.measurable.comp (hb2.sub hbo)).sqrt).const_mul _

lemma measurable_LD_fam : Measurable (fun x : AgFam n => LD x.2.1 x.1.1 x.1.2) := by
  have hho : Measurable (fun x : AgFam n => hO x.2.1 x.1.1 x.1.2) := by
    exact measurable_hO (n := n) (m := mA n)
  have hop : Measurable (fun x : AgFam n => opN x.2.1) :=
    opN_continuous.measurable.comp (measurable_fst.comp measurable_snd)
  unfold LD
  exact (((((measurable_snd.comp measurable_fst).pow_const 2).mul (hop.pow_const 2)).add
    (continuous_normSq.measurable.comp hho)).const_mul _).sqrt

/-- The event `SD' n` is measurable (jointly in `(c, τ, A₁, A₂)`). -/
theorem measurableSet_SD' (n : ℕ) : MeasurableSet (SD' n) := by
  have hd : Measurable (fun x : AgFam n => dC x.2.1 x.2.2 x.1.1 x.1.2) :=
    measurable_dC_gen (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst)
      (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
  have hF : Measurable (fun q : AgFam n × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      dC q.1.2.1 q.2 q.1.1.1 q.1.1.2) :=
    measurable_dC_gen ((measurable_fst.comp measurable_fst).comp measurable_fst)
      ((measurable_snd.comp measurable_fst).comp measurable_fst)
      ((measurable_fst.comp measurable_snd).comp measurable_fst) measurable_snd
  have hint : Measurable (fun x : AgFam n =>
      ∫ B, dC x.2.1 B x.1.1 x.1.2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) :=
    (hF.stronglyMeasurable.integral_prod_right'
      (ν := gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)))).measurable
  have hbad : MeasurableSet {x : AgFam n | x.2.2 ∈ BadD' x.2.1 x.1.1 x.1.2 12} :=
    measurableSet_lt (hint.add (measurable_LD_fam.const_mul _)) hd
  exact hbad.compl

/-- The charge of the new event: `e^{−12} ≤ 615/10⁸`, for every `(c, τ)`. -/
theorem SD'_charge (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SD' n} ≤ 615 / 10 ^ 8 := by
  have hm := BstLean.Part130.one_le_mA hn
  have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      ((c, τ), θ) ∉ SD' n} = {θ | θ.2 ∈ BadD' θ.1 c τ 12} := by
    ext θ
    show ¬ ¬ (θ.2 ∈ BadD' θ.1 c τ 12) ↔ _
    exact not_not
  rw [e]
  have hmeas : MeasurableSet {θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ | θ.2 ∈ BadD' θ.1 c τ 12} := by
    have h := (measurableSet_SD' n).compl.preimage
      (measurable_prodMk_left (x := ((c, τ) : (Fin n → ℝ) × ℝ)) :
        Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
          Matrix (Fin (mA n)) (Fin (mA n)) ℝ => (((c, τ), θ) : AgFam n)))
    rw [← e]
    exact h
  have h := BstLean.Part153.prod_real_le_of_fibre (μ₁ := gaussMat (mA n) n (2 / (n : ℝ)))
    (μ₂ := gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) hmeas (Real.exp_pos (-12)).le
    (fun A₁ => ED'_prob hm A₁ c τ (by norm_num))
  exact h.trans exp_neg_twelve_le

end BstLean.Part160

open BstLean.Part160 in
#print axioms dC_lip'
open BstLean.Part160 in
#print axioms measurableSet_SD'
open BstLean.Part160 in
#print axioms SD'_charge
