import BstLean.Part153Asm
import BstLean.Part153Sc
import BstLean.Part153Weak
import BstLean.Part153PPs4

/-!
# Part 153: the `A`-stage event with every charge proved (weak Jacobian constant)

`BscS n c τ = {A₁ | s_h² < c_s·τ²}` (the complement of `E_sc`, `c_s = 0.95·2(1 − 1/π)`), charge
`3445/n²` (`Esc_prob`). `GoodAw n c τ (BscS n c τ)` is the intersection of
`E_op, E_e, E_N12, E_N14, E_sc` (events of `A₁`), `E_be, E_N22, E_N24` (events of `A₂` given
`A₁`) and `{Ξ₄ ≤ 10·γ_A/n}` (an event of `(A₁, A₂)`), all at the level `L_c = 12`.

* **`AStage_weak_prob`**: for `n ≥ 8192`, `τ > 0`, every `c`:
  `Pr((A₁, A₂) ∉ GoodAw) ≤ exp(−n/2) + 7·exp(−12) + 3445/n² + 1/1000`.
* **`AStage_weak_eb`**: on the event, if `θ_in ≥ θ_lo`: `e_b° ≤ 1 + 2δ_e − (1 − 1/π)(c_s/2)θ_lo`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150

/-- The complement of the event `E_sc`: `s_h² < c_s·τ²`, `c_s = 0.95·2(1 − 1/π)`. -/
def BscS (n : ℕ) (c : Fin n → ℝ) (τ : ℝ) : Set (Matrix (Fin (mA n)) (Fin n) ℝ) :=
  {A₁ | sO2 A₁ c τ < 0.95 * 2 * (1 - 1 / π) * τ ^ 2}

/-- **The `A`-stage event, all charges proved** (weak constant `M = 10` for `Ξ₄`). -/
theorem AStage_weak_prob {n : ℕ} (hn : 8192 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real (GoodAw n c τ (BscS n c τ))ᶜ ≤
      Real.exp (-(n : ℝ) / 2) + 7 * Real.exp (-12) + 3445 / (n : ℝ) ^ 2 + 1 / 1000 :=
  GoodAw_prob hn c hτ (Esc_prob (by omega) c hτ)

/-- **Lemma EN (iii) on the event.** -/
theorem AStage_weak_eb {n : ℕ} (hn : 8192 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ) {θlo : ℝ}
    (hθ : θlo ≤ (n : ℝ) * τ ^ 2 / (normSq c + (n : ℝ) * τ ^ 2))
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodAw n c τ (BscS n c τ)) :
    2 / ((mA n : ℕ) : ℝ) * normSq (bO A₁ A₂ c τ) / (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) ≤
      1 + 2 * (11 / 1000) - (1 - 1 / π) * (0.95 * 2 * (1 - 1 / π) / 2) * θlo := by
  have hpi : (0 : ℝ) ≤ 1 - 1 / π := by
    have : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
    rw [sub_nonneg, div_le_one Real.pi_pos]
    exact this
  exact GoodA_EN_iii hn hτ (cs := 0.95 * 2 * (1 - 1 / π)) (by positivity) (fun A hA => hA) hθ h


/-! ## The event with the sharp Jacobian constant (Lemma PP with `P = 200`, `η_P = 0.006`; the constant `1.2578` is the script value of `M_P` of the paper at `n ≥ 8192`) -/

/-- The complement of the event `E_Pp`, with the constant `12578/10000` in the place of `M_P`. -/
def BXiS (n : ℕ) (c : Fin n → ℝ) (τ : ℝ) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  {θ | (12578 / 10000 : ℝ) * (2 / (n : ℝ)) / n < Xi4 θ.1 θ.2 c τ}

/-- **The `A`-stage event of the paper** (the events `E_op, E_sc, E_e, E_N12, E_N14, E_be, E_N22,
E_N24, E_Pp` at `L_c = 12`). -/
def GoodAs (n : ℕ) (c : Fin n → ℝ) (τ : ℝ) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  GoodA n c τ (BscS n c τ) (BXiS n c τ)

/-- **The charge of the `A`-stage event**: for `n ≥ 8192`, `τ > 0`, every `c`:
`Pr((A₁, A₂) ∉ GoodAs) ≤ exp(−n/2) + 7·exp(−12) + 3445/n² + 5·10⁻⁵`. -/
theorem AStage_prob {n : ℕ} (hn : 8192 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real (GoodAs n c τ)ᶜ ≤
      Real.exp (-(n : ℝ) / 2) + 7 * Real.exp (-12) + 3445 / (n : ℝ) ^ 2 + 5 / 100000 :=
  GoodA_prob (by omega) c τ (Esc_prob (by omega) c hτ) (lemmaPP_numeric_8192 hn c hτ)

/-- **The covariance bound on the event**: `Ξ ≤ (12578/10000)·γ_A/n`, `t_A·Var_x⟨w, a₂(x)⟩ ≤
(12578/10000)·(γ_A/n)·|w|²`, and `Var_x φ(q(x)) ≤ L_φ²·(12578/10000)·γ_A/n` for a Lipschitz `φ`. -/
theorem AStage_Xi {n : ℕ} (hn : 8192 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodAs n c τ) :
    XiS A₁ A₂ c τ ≤ 12578 / 10000 * (2 / (n : ℝ)) / n ∧
    (∀ w : Fin (mA n) → ℝ,
      2 / ((mA n : ℕ) : ℝ) * ∫ ξ, (w ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) -
        ∫ ξ', w ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
        12578 / 10000 * (2 / (n : ℝ)) / n * normSq w) ∧
    (∀ (φ : (Fin (mA n) → ℝ) → ℝ) (Lφ : ℝ), 0 ≤ Lφ → BstLean.Part148.EuLip φ Lφ →
      ∫ ξ, (φ (√(2 / ((mA n : ℕ) : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) -
        ∫ ξ', φ (√(2 / ((mA n : ℕ) : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ'))) ∂stdGauss (Fin n)) ^ 2
          ∂stdGauss (Fin n) ≤ Lφ ^ 2 * (12578 / 10000 * (2 / (n : ℝ)) / n)) :=
  GoodA_Xi (by omega) hτ (fun θ hθ => hθ) h

/-- **Lemma EN (iii) on the event.** -/
theorem AStage_eb {n : ℕ} (hn : 8192 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ) {θlo : ℝ}
    (hθ : θlo ≤ (n : ℝ) * τ ^ 2 / (normSq c + (n : ℝ) * τ ^ 2))
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodAs n c τ) :
    2 / ((mA n : ℕ) : ℝ) * normSq (bO A₁ A₂ c τ) / (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) ≤
      1 + 2 * (11 / 1000) - (1 - 1 / π) * (0.95 * 2 * (1 - 1 / π) / 2) * θlo :=
  by
  have hpi : (0 : ℝ) ≤ 1 - 1 / π := by
    have : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
    rw [sub_nonneg, div_le_one Real.pi_pos]
    exact this
  exact GoodA_EN_iii hn hτ (cs := 0.95 * 2 * (1 - 1 / π)) (by positivity) (fun A hA => hA) hθ h

/-- The other deterministic bounds on the event: `E_op`, the energy, the four norm deviations. -/
theorem AStage_bounds {n : ℕ} (hn : 8192 ≤ n) {c : Fin n → ℝ} {τ : ℝ}
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodAs n c τ) :
    (A₁ ∈ Eop n ∧ 2 / ((mA n : ℕ) : ℝ) * BstLean.Part152.opN A₁ ^ 2 ≤ 4 * wn n / n ∧
      GamS A₁ c τ ≤ 4 * wn n / n * (normSq c + (n : ℝ) * τ ^ 2)) ∧
    |GamS A₁ c τ - 2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)| ≤
      11 / 1000 * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) ∧
    (N1 2 A₁ c τ ≤ N12bar n 12 ∧ N1 4 A₁ c τ ≤ N14bar n 12 ∧
      N2 2 A₁ A₂ c τ ≤ N22bar n 12 ∧ N2 4 A₁ A₂ c τ ≤ N24bar n 12 ∧
      ∫ ξ, |sq2 A₁ A₂ c τ ξ ^ 2 - 1| ∂stdGauss (Fin n) ≤ N22bar n 12 * (2 + N22bar n 12)) ∧
    0.95 * 2 * (1 - 1 / π) * τ ^ 2 ≤ sO2 A₁ c τ :=
  ⟨GoodA_op (by omega) h, GoodA_energy hn h, GoodA_norms (by omega) h,
    not_lt.mp (GoodA_unpack h).2.2.2.2.1⟩

#print axioms AStage_prob
#print axioms AStage_Xi
#print axioms AStage_eb
#print axioms AStage_bounds


/-! ## The same event for `n ≥ 16384`, with the constant `1.1911` (the paper's `M_P` there) -/

/-- The `A`-stage event with the constant `11911/10000` for `Ξ₄`. -/
def GoodAs16 (n : ℕ) (c : Fin n → ℝ) (τ : ℝ) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  GoodA n c τ (BscS n c τ) {θ | (11911 / 10000 : ℝ) * (2 / (n : ℝ)) / n < Xi4 θ.1 θ.2 c τ}

theorem AStage16_prob {n : ℕ} (hn : 16384 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real (GoodAs16 n c τ)ᶜ ≤
      Real.exp (-(n : ℝ) / 2) + 7 * Real.exp (-12) + 3445 / (n : ℝ) ^ 2 + 5 / 100000 :=
  GoodA_prob (by omega) c τ (Esc_prob (by omega) c hτ) (lemmaPP_numeric_16384 hn c hτ)

theorem AStage16_Xi {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodAs16 n c τ) :
    XiS A₁ A₂ c τ ≤ 11911 / 10000 * (2 / (n : ℝ)) / n :=
  (GoodA_Xi (by omega) hτ (fun θ hθ => hθ) h).1

/-- The events are measurable. -/
theorem measurableSet_GoodAs {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ)
    (hB : MeasurableSet (BscS n c τ)) : MeasurableSet (GoodAs n c τ) :=
  measurableSet_GoodA hn c τ hB
    (measurableSet_lt measurable_const (measurable_Xi4 c τ))

#print axioms AStage16_prob
#print axioms AStage16_Xi
#print axioms measurableSet_GoodAs
#print axioms AStage_weak_prob
#print axioms AStage_weak_eb

end BstLean.Part153
