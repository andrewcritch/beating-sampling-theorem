import BstLean.Part152Op
import BstLean.Part151FStage

/-!
# Part 151: Lemma ON (the operator norms) for the feature map of `F`

Role: `delegations/statements/p151-spec.md`, item 4; paper source
`proofs/option-n/theorem5-08-F-rows.tex`, Lemma ON.

Part 152 (`Part152Op`) has Gordon's bound with the sharp Gaussian tail:
`Pr(opN M ≥ √v(√p + √q + u)) ≤ exp(−u²/2)` (`opN_tail'`). So no net argument is needed, and the
constants are those of the document.

* `normSq_mulVec_le_opN`: `|M x|² ≤ opN(M)²·|x|²`.
* `K1 n m u = √(2/n)(√m + √n + u)`, `K2 m u = √(2/m)(2√m + u)`: the thresholds of the events
  `E_{F1}`, `E_{F2}` of the document (`u = u_F = √(2L_c)`).
* `hid2_lip_op`: `|z_F(y) − z_F(y′)|² ≤ (opN F₁·opN F₂)²·|y − y′|²`.
* **`lemmaON`**: outside an event of `(F₁, F₂)` of probability at most `2·exp(−u²/2)`,
  `z_F` is Lipschitz with the constant `L_F = K1·K2`.
* **`tF_LF_sq`**: `t_F·(K1·K2)² = (32/n)·l_F`, `l_F = (1 + u/(2√m))²(1 + (√n + u)/√m)²`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open BstLean.Part130 BstLean.Part131
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part152 (opN opN_nonneg mulVec_le_opN opN_tail')

/-- `|M x|² ≤ opN(M)²·|x|²`. -/
lemma normSq_mulVec_le_opN {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (x : Fin q → ℝ) :
    normSq (M *ᵥ x) ≤ opN M ^ 2 * normSq x := by
  have h := mulVec_le_opN M x
  have h0 : 0 ≤ ∑ i, (M *ᵥ x) i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt h0, mul_pow, Real.sq_sqrt h1] at h2
  exact h2

/-- `|z_F(y) − z_F(y′)|² ≤ (opN F₁·opN F₂)²·|y − y′|²` (operator norms). -/
theorem hid2_lip_op {k m₁ m₂ : ℕ} (M₁ : Matrix (Fin m₁) (Fin k) ℝ)
    (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ) (y y' : Fin k → ℝ) :
    normSq (hid2 M₁ M₂ y - hid2 M₁ M₂ y') ≤ (opN M₁ * opN M₂) ^ 2 * normSq (y - y') := by
  unfold hid2
  have h2 : 0 ≤ opN M₂ ^ 2 := sq_nonneg _
  calc normSq (reluV (M₂ *ᵥ reluV (M₁ *ᵥ y)) - reluV (M₂ *ᵥ reluV (M₁ *ᵥ y')))
      ≤ normSq (M₂ *ᵥ reluV (M₁ *ᵥ y) - M₂ *ᵥ reluV (M₁ *ᵥ y')) := normSq_reluV_sub_le _ _
    _ = normSq (M₂ *ᵥ (reluV (M₁ *ᵥ y) - reluV (M₁ *ᵥ y'))) := by rw [Matrix.mulVec_sub]
    _ ≤ opN M₂ ^ 2 * normSq (reluV (M₁ *ᵥ y) - reluV (M₁ *ᵥ y')) := normSq_mulVec_le_opN _ _
    _ ≤ opN M₂ ^ 2 * (opN M₁ ^ 2 * normSq (y - y')) := by
        refine mul_le_mul_of_nonneg_left ?_ h2
        calc normSq (reluV (M₁ *ᵥ y) - reluV (M₁ *ᵥ y'))
            ≤ normSq (M₁ *ᵥ y - M₁ *ᵥ y') := normSq_reluV_sub_le _ _
          _ = normSq (M₁ *ᵥ (y - y')) := by rw [Matrix.mulVec_sub]
          _ ≤ opN M₁ ^ 2 * normSq (y - y') := normSq_mulVec_le_opN _ _
    _ = (opN M₁ * opN M₂) ^ 2 * normSq (y - y') := by ring

/-- The threshold of the event `E_{F1}`: `√γ_A·(√m + √n + u)`, `γ_A = 2/n`. -/
noncomputable def K1 (n m : ℕ) (u : ℝ) : ℝ := √(2 / (n : ℝ)) * (√(m : ℝ) + √(n : ℝ) + u)

/-- The threshold of the event `E_{F2}`: `√t_F·(2√m + u)`, `t_F = 2/m`. -/
noncomputable def K2 (m : ℕ) (u : ℝ) : ℝ := √(2 / (m : ℝ)) * (√(m : ℝ) + √(m : ℝ) + u)

lemma K1_nonneg (n m : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ K1 n m u := by unfold K1; positivity

lemma K2_nonneg (m : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ K2 m u := by unfold K2; positivity

/-- The events `E_{F1} ∩ E_{F2}` of the document, as a set of `(F₁, F₂)`. -/
def EON (n m : ℕ) (u : ℝ) : Set (HidParam n m) :=
  {θ | opN θ.1 < K1 n m u ∧ opN θ.2 < K2 m u}

/-- On `E_{F1} ∩ E_{F2}` the feature map is Lipschitz with the constant `L_F = K1·K2`. -/
theorem lip_of_EON {n m : ℕ} {u : ℝ} {θ : HidParam n m} (hθ : θ ∈ EON n m u) (y y' : Fin n → ℝ) :
    normSq (hid2 θ.1 θ.2 y - hid2 θ.1 θ.2 y') ≤ (K1 n m u * K2 m u) ^ 2 * normSq (y - y') := by
  refine (hid2_lip_op θ.1 θ.2 y y').trans ?_
  have h1 := opN_nonneg θ.1
  have h2 := opN_nonneg θ.2
  have h3 : opN θ.1 * opN θ.2 ≤ K1 n m u * K2 m u :=
    mul_le_mul hθ.1.le hθ.2.le h2 (h1.trans hθ.1.le)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg h1 h2) h3 2) (normSq_nonneg _)

/-- **Lemma ON, the charge**: `Pr((E_{F1} ∩ E_{F2})ᶜ) ≤ 2·exp(−u²/2)` for `n, m ≥ 1`, `u ≥ 0`
(the document: `u = u_F = √(2L_c)`, charge `2e^{−L_c}`). -/
theorem EON_prob {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {u : ℝ} (hu : 0 ≤ u) :
    (hidGauss n m).real (EON n m u)ᶜ ≤ 2 * Real.exp (-u ^ 2 / 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have t1 := opN_tail' (p := m) (q := n) (v := 2 / (n : ℝ)) (by positivity) hu
  have t2 := opN_tail' (p := m) (q := m) (v := 2 / (m : ℝ)) (by positivity) hu
  have hsub : (EON n m u)ᶜ ⊆
      ({M : Matrix (Fin m) (Fin n) ℝ | K1 n m u ≤ opN M} ×ˢ
        (univ : Set (Matrix (Fin m) (Fin m) ℝ))) ∪
      ((univ : Set (Matrix (Fin m) (Fin n) ℝ)) ×ˢ
        {M : Matrix (Fin m) (Fin m) ℝ | K2 m u ≤ opN M}) := by
    intro θ hθ
    by_cases h1 : opN θ.1 < K1 n m u
    · refine Or.inr ⟨mem_univ _, ?_⟩
      by_contra h2
      exact hθ ⟨h1, not_le.mp h2⟩
    · exact Or.inl ⟨not_lt.mp h1, mem_univ _⟩
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  unfold hidGauss
  rw [measureReal_prod_prod, measureReal_prod_prod]
  simp only [probReal_univ, mul_one, one_mul]
  unfold K1 K2
  linarith

/-- **Lemma ON**: outside an event of `(F₁, F₂)` of probability at most `2·exp(−u²/2)`, the
feature map `z_F` is Lipschitz with the constant `L_F = K1·K2`. -/
theorem lemmaON {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {u : ℝ} (hu : 0 ≤ u) :
    (hidGauss n m).real {θ | ¬ ∀ y y' : Fin n → ℝ,
        normSq (hid2 θ.1 θ.2 y - hid2 θ.1 θ.2 y') ≤ (K1 n m u * K2 m u) ^ 2 * normSq (y - y')} ≤
      2 * Real.exp (-u ^ 2 / 2) := by
  refine (measureReal_mono ?_).trans (EON_prob hn hm hu)
  intro θ hθ hE
  exact hθ fun y y' => lip_of_EON hE y y'

/-- **`t_F·L_F² = (32/n)·l_F`**, `l_F = (1 + u/(2√m))²(1 + (√n + u)/√m)²`: the display of
Lemma ON of the document, as an equality. -/
theorem tF_LF_sq {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (u : ℝ) :
    2 / (m : ℝ) * (K1 n m u * K2 m u) ^ 2 =
      32 / (n : ℝ) * ((1 + u / (2 * √(m : ℝ))) ^ 2 * (1 + (√(n : ℝ) + u) / √(m : ℝ)) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < √(m : ℝ) := Real.sqrt_pos.mpr hm0
  have hsm : √(m : ℝ) ^ 2 = m := Real.sq_sqrt hm0.le
  unfold K1 K2
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have e1 : (√(m : ℝ) + √(n : ℝ) + u) = √(m : ℝ) * (1 + (√(n : ℝ) + u) / √(m : ℝ)) := by
    field_simp; ring
  have e2 : (√(m : ℝ) + √(m : ℝ) + u) = 2 * √(m : ℝ) * (1 + u / (2 * √(m : ℝ))) := by
    field_simp; ring
  rw [e1, e2, mul_pow, mul_pow, mul_pow, hsm]
  field_simp
  ring

end BstLean.Part151

