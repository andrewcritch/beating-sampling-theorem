import BstLean.Part149Stage
import BstLean.Part149Frame
import BstLean.Part149Kern

/-!
# Part 149, definitions for the stage of the Agent network at the stand-in inputs

Do not use `sorry`, `native_decide` or `axiom`.

The stand-in inputs of the `W` stage are `x(γ) = sphPt (c + τ·γ)`, `γ` a standard Gaussian vector
of `ℝⁿ` (`c` the centre and `τ` the scalar that the pass over `W` gives). `θ = (A₁, A₂)` are the
two hidden matrices of the Agent network, with hidden width `m`.

* `hA c τ θ γ = a₂(x(γ)) = ReLU(A₂·ReLU(A₁ x(γ)))`: the last hidden vector of `A`.
* `bbar c τ θ = E_γ a₂(x(γ))`: the EXACT centre (an idealized program computes it; no
  arithmetic program is given for it here).
* `tauOut c τ θ = √(max 0 (2/n − (2/m)|b̄|²))`: the constant scalar of the stand-in of `A`.
* `errKc a c τ θ = E_{γ,γ'} (⟨a₂(x), a₂(x')⟩ − a)²`, `errDc c τ θ = E_γ (|a₂(x)|² − m/n)²`.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss hbar)

variable {n m : ℕ}

/-- The last hidden vector of `A` at the stand-in input `sphPt (c + τ·γ)`. -/
noncomputable def hA (c : Fin n → ℝ) (τ : ℝ) (θ : HidParam n m) (γ : Fin n → ℝ) : Fin m → ℝ :=
  hid2 θ.1 θ.2 (sphPt (c + τ • γ))

/-- The exact centre of `A` over the stand-in inputs: `E_γ a₂(x(γ))`. -/
noncomputable def bbar (c : Fin n → ℝ) (τ : ℝ) (θ : HidParam n m) : Fin m → ℝ :=
  hbar (stdGauss (Fin n)) (hA c τ θ)

/-- The constant scalar of the stand-in of `A`: `√(max 0 (2/n − (2/m)|b̄|²))`. -/
noncomputable def tauOut (c : Fin n → ℝ) (τ : ℝ) (θ : HidParam n m) : ℝ :=
  √(max 0 (2 / (n : ℝ) - 2 / (m : ℝ) * normSq (bbar c τ θ)))

/-- The integrated squared error of the Gram kernel of `a₂` against the constant `a`. -/
noncomputable def errKc (a : ℝ) (c : Fin n → ℝ) (τ : ℝ) (θ : HidParam n m) : ℝ :=
  ∫ p, (∑ k, hA c τ θ p.1 k * hA c τ θ p.2 k - a) ^ 2
    ∂((stdGauss (Fin n)).prod (stdGauss (Fin n)))

/-- The integrated squared error of `|a₂|²` against `m/n`. -/
noncomputable def errDc (c : Fin n → ℝ) (τ : ℝ) (θ : HidParam n m) : ℝ :=
  ∫ γ, (normSq (hA c τ θ γ) - (m : ℝ) / n) ^ 2 ∂stdGauss (Fin n)

lemma measurable_hA (c : Fin n → ℝ) (τ : ℝ) (θ : HidParam n m) : Measurable (hA c τ θ) :=
  (continuous_hid2 θ.1 θ.2).measurable.comp
    (measurable_sphPt.comp (measurable_const.add (measurable_id.const_smul τ)))

/-- The hidden map is bounded: the inputs are unit vectors. -/
lemma hA_bound (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (θ : HidParam n m) :
    ∃ H : ℝ, ∀ γ, normSq (hA c τ θ γ) ≤ H := by
  obtain ⟨C, hC⟩ := isCompact_unit.exists_bound_of_continuousOn
    (continuous_normSq.comp (continuous_hid2 θ.1 θ.2)).continuousOn
  refine ⟨C, fun γ => ?_⟩
  have := hC (sphPt (c + τ • γ)) (normSq_sphPt hn _)
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

lemma bm_hA (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (θ : HidParam n m) (j : Fin m) :
    BM (fun γ => hA c τ θ γ j) := by
  obtain ⟨C, hC⟩ := isCompact_unit.exists_bound_of_continuousOn
    ((continuous_apply j).comp (continuous_hid2 θ.1 θ.2)).continuousOn
  refine ⟨(measurable_pi_apply j).comp (measurable_hA c τ θ), C, fun γ => ?_⟩
  have := hC (sphPt (c + τ • γ)) (normSq_sphPt hn _)
  rwa [Real.norm_eq_abs] at this

end BstLean.Part149
