import BstLean.Part150Num
import BstLean.Part150AllC

/-!
# Part 150, item 3 with the constants of Lemma B-F: Proposition P45 (i), (ii), deterministic form

Role: `delegations/statements/p150-spec.md`, item 3. Paper source: `onW45-opus-prover.md` §3
(Proposition P45 (i), (ii); "Notation for both routes": `α(J) = c_1(J)/J`, `β(J) = c_2(J)/J`).

* `alphaJ J = c1F kappa4 J / J`, `betaJ J = c2F kappa4 J / J`: the MAIN route of the paper.
* **`centre150_first`**: for every `A₁`, `c`, `τ ≥ 0`, `J₁ ≥ 1`:
  `|h̃ − h̄|² ≤ α(J₁)²τ²‖A₁‖²_F`, `|γ̃_Γ − γ_Γ| ≤ β(J₁)·t·τ²‖A₁‖²_F`,
  `0 ≤ s̃² ≤ t·τ²‖A₁‖²_F`, and the bound of `|s̃² − s²|` with the cross term.
* **`centre150_second`**: for every `A₁`, `A₂`, `c`, `τ`, `J₂ ≥ 1`, coordinate by coordinate:
  `|b̃′_j − b′_j| ≤ α(J₂)·s̃ + φ(0)·|s̃ − s| + |(A₂(h̃ − h̄))_j|`, `φ(0) = 1/√(2π)`; and the norm form
  `|b̃′ − b′| ≤ √m·(α(J₂)·s̃ + φ(0)|s̃ − s|) + |A₂(h̃ − h̄)|` (Proposition P45 (i) without `√t`).
* `alphaJ_le`, `betaJ_le`: `α(J) ≤ 0.1792/J` (`J ≥ 1 000`), `β(J) ≤ 0.081/J` (`J ≥ 4 096`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part132 BstLean.Part137 BstLean.Part141

/-- `α(J) = c_1(J)/J` (the main route of the paper). -/
noncomputable def alphaJ (J : ℕ) : ℝ := c1F kappa4 J / J

/-- `β(J) = c_2(J)/J` (the main route of the paper, with `56807/6750` for `7ζ(3)`). -/
noncomputable def betaJ (J : ℕ) : ℝ := c2F kappa4 J / J

lemma c1F_nonneg {c : ℝ} (hc : 0 ≤ c) (J : ℕ) : 0 ≤ c1F c J := by
  unfold c1F; positivity

lemma c2F_nonneg {c : ℝ} (hc : 0 ≤ c) (J : ℕ) : 0 ≤ c2F c J := by
  unfold c2F; positivity

lemma alphaJ_nonneg (J : ℕ) : 0 ≤ alphaJ J :=
  div_nonneg (c1F_nonneg kappa4_nonneg J) (Nat.cast_nonneg J)

lemma betaJ_nonneg (J : ℕ) : 0 ≤ betaJ J :=
  div_nonneg (c2F_nonneg kappa4_nonneg J) (Nat.cast_nonneg J)

/-- Lemma B-F (i) in the form that item 3 uses. -/
theorem alphaJ_spec {J : ℕ} (hJ : 1 ≤ J) : ∀ a s : ℝ, 0 ≤ s →
    |binMean J (fun z => relu (a + s * z)) - psiS s a| ≤ alphaJ J * s := by
  intro a s hs
  refine (lemmaBF1_paper hJ a hs).trans (le_of_eq ?_)
  unfold alphaJ; ring

/-- Lemma B-F (ii) in the form that item 3 uses. -/
theorem betaJ_spec {J : ℕ} (hJ : 1 ≤ J) : ∀ a s : ℝ, 0 ≤ s →
    |binMean J (fun z => relu (a + s * z) ^ 2) - ∫ z, relu (a + s * z) ^ 2 ∂gaussianReal 0 1| ≤
      betaJ J * s ^ 2 := by
  intro a s hs
  refine (lemmaBF2_paper hJ a hs).trans (le_of_eq ?_)
  unfold betaJ; ring

theorem alphaJ_le {J : ℕ} (hJ : 1000 ≤ J) : alphaJ J ≤ 1792 / 10000 / J := by
  have hJpos : (0 : ℝ) < J := by
    have : (1000 : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  exact div_le_div_of_nonneg_right (c1F_kappa4_le hJ) hJpos.le

theorem betaJ_le {J : ℕ} (hJ : 4096 ≤ J) : betaJ J ≤ 81 / 1000 / J := by
  have hJpos : (0 : ℝ) < J := by
    have : (4096 : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  exact div_le_div_of_nonneg_right (c2F_kappa4_le_4096 hJ) hJpos.le

variable {n m : ℕ}

/-- **Proposition P45 (ii), deterministic form: the first layer.** -/
theorem centre150_first {J₁ : ℕ} (hJ : 1 ≤ J₁) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ∑ i, (hT J₁ A₁ c τ i - hO A₁ c τ i) ^ 2 ≤ alphaJ J₁ ^ 2 * τ ^ 2 * froSq A₁ ∧
    |gT J₁ A₁ c τ - gO A₁ c τ| ≤ betaJ J₁ * (2 / (m : ℝ)) * τ ^ 2 * froSq A₁ ∧
    0 ≤ sT2 J₁ A₁ c τ ∧
    sT2 J₁ A₁ c τ ≤ 2 / (m : ℝ) * (τ ^ 2 * froSq A₁) ∧
    |sT2 J₁ A₁ c τ - sO2 A₁ c τ| ≤ betaJ J₁ * (2 / (m : ℝ)) * τ ^ 2 * froSq A₁ +
      2 / (m : ℝ) * (2 * (alphaJ J₁ * τ * √(froSq A₁)) * √(∑ i, hO A₁ c τ i ^ 2) +
        alphaJ J₁ ^ 2 * τ ^ 2 * froSq A₁) :=
  ⟨hT_sub_hO_sq (alphaJ_spec hJ) A₁ c hτ, gT_sub_gO (betaJ_spec hJ) A₁ c hτ,
    sT2_nonneg J₁ A₁ c τ, sT2_le (le_of_eq (binMean_sq hJ)) A₁ c τ,
    sT2_sub_sO2 (alphaJ_nonneg J₁) (alphaJ_spec hJ) (betaJ_spec hJ) A₁ c hτ⟩

/-- **Proposition P45 (i), deterministic form: the second layer.** -/
theorem centre150_second (J₁ : ℕ) {J₂ : ℕ} (hJ : 1 ≤ J₂) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    (∀ j, |bT J₁ J₂ A₁ A₂ c τ j - bO A₁ A₂ c τ j| ≤
      alphaJ J₂ * sT J₁ A₁ c τ + 1 / √(2 * π) * |sT J₁ A₁ c τ - sO A₁ c τ| +
        |(A₂.mulVec (hT J₁ A₁ c τ - hO A₁ c τ)) j|) ∧
    nrm (bT J₁ J₂ A₁ A₂ c τ - bO A₁ A₂ c τ) ≤
      √(m : ℝ) * (alphaJ J₂ * sT J₁ A₁ c τ + 1 / √(2 * π) * |sT J₁ A₁ c τ - sO A₁ c τ|) +
        nrm (A₂.mulVec (hT J₁ A₁ c τ - hO A₁ c τ)) :=
  ⟨fun j => bT_sub_bO (alphaJ_spec hJ) psiS_lip_s_phi J₁ A₁ A₂ c τ j,
    bT_sub_bO_nrm (alphaJ_nonneg J₂) (by positivity) (alphaJ_spec hJ) psiS_lip_s_phi J₁ A₁ A₂ c τ⟩

end BstLean.Part150
