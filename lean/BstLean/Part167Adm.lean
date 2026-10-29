import BstLean.Part167Grad

/-!
# Part 167 (file `Adm`): admissibility of the centre and of the residual direction

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-07-mixture-fluctuation.tex`, the paragraph before Lemma `t7:p07:LJ`: "The vectors
`b, a₂(x), r(x)` are admissible: the first-layer centre depends only on the axial components and
lengths, and `b_j = B(a'_j·ĥ₁)` for a fixed scalar function `B` conditional on `A₁`."

For Lean's centre (Part 154's `bT`, `J₁ = J₂ = n`), with `h₁ = ReLU(A₁x)` and `h̃ = hT(A₁, ĉ, τ)`:

* **`bK_eq_core`**: `b_j = (1/ρ)·B(A₁)((A₂h̃)_j)`, `B(A₁)(t) = E relu(t + s̃(A₁)Z_n)`.
* **`hT_adm`**: `h̃` (and `s̃`) depend on `A₁` only through `A₁ĉ` and the row lengths of `A₁`
  (so they are measurable in the paper's `𝓕_x`, whose generators include `a_i·u` and `|a_i|`).
* **`adm_plane`**: if `A₂h₁ = A₂'h₁` and `A₂h̃ = A₂'h̃`, then `b̂`, `a₂(x)`, `r̂(x)` and the
  second-layer gates `D₂` at `x` coincide for `(A₁, A₂)` and `(A₁, A₂')`. So they depend on `A₂`
  only through its action on the plane `U_x = span(h₁, h̃)`: they are admissible.
-/

namespace BstLean.Part167

open MeasureTheory Matrix Real
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160
open BstLean.Part150 (hT sT bT rhoC binMean mRow sRow gT sT2)
open BstLean.Part151 (jac mask)
open BstLean.Part166 (bK bhat)

variable {n : ℕ}

/-- The scalar function of the centre, conditional on `A₁`: `t ↦ E relu(t + s̃ Z_n)` (Part 150's
`binMean` with `n` nodes), applied to each coordinate and divided by `ρ`. -/
noncomputable def bCore (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (t : Fin (mA n) → ℝ) : Fin (mA n) → ℝ :=
  (1 / rhoC c τ) • fun j => binMean n (fun z => relu (t j + sT n A₁ c τ * z))

/-- **The centre reads `A₂` only through `A₂h̃`.** -/
theorem bK_eq_core (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :
    bK ((c, τ), (A₁, A₂)) = bCore A₁ c τ (A₂ *ᵥ hT n A₁ c τ) := rfl

/-- **`h̃` and `s̃` read `A₁` only through `A₁ĉ` and the row lengths.** -/
theorem hT_adm (c : Fin n → ℝ) (τ : ℝ) {A₁ A₁' : Matrix (Fin (mA n)) (Fin n) ℝ}
    (hc : A₁ *ᵥ c = A₁' *ᵥ c) (hr : ∀ i, ∑ j, A₁ i j ^ 2 = ∑ j, A₁' i j ^ 2) :
    hT n A₁ c τ = hT n A₁' c τ ∧ sT n A₁ c τ = sT n A₁' c τ := by
  have hm : ∀ i, mRow A₁ c i = mRow A₁' c i := fun i => by unfold mRow; rw [hc]
  have hs : ∀ i, sRow A₁ τ i = sRow A₁' τ i := fun i => by unfold sRow; rw [hr i]
  have h1 : hT n A₁ c τ = hT n A₁' c τ := by
    funext i; unfold hT; rw [hm i, hs i]
  refine ⟨h1, ?_⟩
  unfold sT sT2 gT
  rw [h1]
  congr 3
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hm i, hs i]

/-- **Admissibility**: the centre direction, the hidden vector, the residual direction and the
second-layer gates at `x` depend on `A₂` only through `(A₂h₁, A₂h̃)`. -/
theorem adm_plane (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    {A₂ A₂' : Matrix (Fin (mA n)) (Fin (mA n)) ℝ} (x : Fin n → ℝ)
    (h1 : A₂ *ᵥ reluV (A₁ *ᵥ x) = A₂' *ᵥ reluV (A₁ *ᵥ x))
    (h2 : A₂ *ᵥ hT n A₁ c τ = A₂' *ᵥ hT n A₁ c τ) :
    bhat (bK ((c, τ), (A₁, A₂))) = bhat (bK ((c, τ), (A₁, A₂'))) ∧
    hid2 A₁ A₂ x = hid2 A₁ A₂' x ∧
    bhat (rK ((c, τ), (A₁, A₂)) x) = bhat (rK ((c, τ), (A₁, A₂')) x) ∧
    (∀ j, mask ((A₂ *ᵥ reluV (A₁ *ᵥ x)) j) = mask ((A₂' *ᵥ reluV (A₁ *ᵥ x)) j)) := by
  have hb : bK ((c, τ), (A₁, A₂)) = bK ((c, τ), (A₁, A₂')) := by
    rw [bK_eq_core, bK_eq_core, h2]
  have hh : hid2 A₁ A₂ x = hid2 A₁ A₂' x := by
    unfold hid2; rw [h1]
  refine ⟨by rw [hb], hh, ?_, fun j => by rw [h1]⟩
  have hr : rK ((c, τ), (A₁, A₂)) x = rK ((c, τ), (A₁, A₂')) x := by
    unfold rK
    simp only
    rw [hh, hb]
  rw [hr]

end BstLean.Part167
