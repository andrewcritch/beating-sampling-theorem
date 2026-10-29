import BstLean.Part167Split
import BstLean.Part167Red

/-!
# Part 167 (file `Plane`): the conditional Gaussian structure of `𝒥ᵀy` (sub-lemma 3 for the Agent)

No proof is left open; no `native_decide` or `axiom` is used.

Fix the World value `(ĉ, τ)`, an input `x`, and `A₁`. Put `h₁ = ReLU(A₁x)`, `h̃ = hT(A₁, ĉ, τ)`,
`D₁A₁` the masked first matrix. For the two admissible directions
`y_f = b̂ = Y_F(A₂h₁, A₂h̃)` and `y_σ = r̂(x) = Y_S(A₂h₁, A₂h̃)` (file `Adm`):

* **`vecMul_jac`**: `𝒥ᵀy = (D₁A₁)ᵀ (A₂ᵀ (D₂y))`.
* **`gF_eq_gate`**, **`gS_eq_gate`**: `𝒥ᵀy = (D₁A₁)ᵀ A₂ᵀ W(A₂h₁, A₂h̃)` with `W = D₂·Y`.
* **`agent_plane`**: given `A₁`, `𝒥ᵀy` has the distribution of
  `(D₁A₁)ᵀ (p(ξ₁, ξ₂) + perp h₁ (perp r (s(ξ₁, ξ₂)·γ)))` (`transRep`), `s = √t_A·|D₂y|`, with the
  plane coordinates `ξ₁, ξ₂` and the transverse Gaussian `γ` independent.
* **`JM_rep_f`**, **`JM_rep_s`**: the moments of `JM_hyp` written over
  `A₁ ⊗ ξ₁ ⊗ ξ₂ ⊗ γ` (Tonelli over `nuA n = gaussMat ⊗ gaussMat`).
-/

namespace BstLean.Part167

open MeasureTheory ProbabilityTheory Matrix Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part160
open BstLean.Part157 (cOf)
open BstLean.Part150 (hT sT rhoC binMean)
open BstLean.Part151 (jac mask measurable_mask)
open BstLean.Part153 (nuA)
open BstLean.Part166 (bK bhat measurable_bK measurable_bhat)

variable {n : ℕ}

/-- The masked first matrix `D₁A₁` at `x`. -/
noncomputable def D1A1 {m k : ℕ} (A₁ : Matrix (Fin m) (Fin k) ℝ) (x : Fin k → ℝ) :
    Matrix (Fin m) (Fin k) ℝ :=
  Matrix.of fun i l => mask ((A₁ *ᵥ x) i) * A₁ i l

/-- **`𝒥ᵀy = (D₁A₁)ᵀ A₂ᵀ (D₂ y)`.** -/
lemma vecMul_jac {m₁ m₂ k : ℕ} (A₁ : Matrix (Fin m₁) (Fin k) ℝ) (A₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (x : Fin k → ℝ) (y : Fin m₂ → ℝ) :
    vecMul y (jac A₁ A₂ x) =
      vecMul (vecMul (fun j => mask ((A₂ *ᵥ reluV (A₁ *ᵥ x)) j) * y j) A₂) (D1A1 A₁ x) := by
  funext l
  simp only [vecMul, dotProduct, jac, D1A1, Matrix.of_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The gated direction `W = D₂·Y` as a function of the plane data `(A₂h₁, A₂h̃)`. -/
noncomputable def gate {m : ℕ} (Y : (Fin m → ℝ) × (Fin m → ℝ) → Fin m → ℝ)
    (p : (Fin m → ℝ) × (Fin m → ℝ)) : Fin m → ℝ :=
  fun j => mask (p.1 j) * Y p j

/-- `b̂` from the plane data. -/
noncomputable def YF (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) : Fin (mA n) → ℝ :=
  bhat (bCore A₁ c τ p.2)

/-- `r̂(x)` from the plane data. -/
noncomputable def YS (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) : Fin (mA n) → ℝ :=
  bhat (reluV p.1 - (∑ j, reluV p.1 j * YF A₁ c τ p j) • YF A₁ c τ p)

lemma measurable_gate {m : ℕ} {Y : (Fin m → ℝ) × (Fin m → ℝ) → Fin m → ℝ} (hY : Measurable Y) :
    Measurable (gate Y) := by
  refine measurable_pi_iff.mpr fun j => ?_
  exact (measurable_mask.comp ((measurable_pi_apply j).comp measurable_fst)).mul
    ((measurable_pi_apply j).comp hY)

lemma measurable_bCore (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (bCore A₁ c τ) := by
  unfold bCore
  have hrelu : Continuous relu := by unfold relu; fun_prop
  have h : Measurable (fun t : Fin (mA n) → ℝ =>
      fun j => binMean n (fun z => relu (t j + sT n A₁ c τ * z))) :=
    measurable_pi_iff.mpr fun j => BstLean.Part150.measurable_binMean_affine n
      hrelu.measurable (measurable_pi_apply j) measurable_const
  exact h.const_smul (1 / rhoC c τ)

lemma measurable_YF (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (YF A₁ c τ) :=
  measurable_bhat.comp ((measurable_bCore A₁ c τ).comp measurable_snd)

lemma measurable_YS (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (YS A₁ c τ) := by
  unfold YS
  have hr0 : Continuous (fun v : Fin (mA n) → ℝ => reluV v) := by
    unfold reluV relu; fun_prop
  have hr : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) => reluV p.1) :=
    hr0.measurable.comp measurable_fst
  have hy := measurable_YF A₁ c τ
  have hs : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) =>
      ∑ j, reluV p.1 j * YF A₁ c τ p j) :=
    Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp hr).mul ((measurable_pi_apply j).comp hy)
  exact measurable_bhat.comp (hr.sub (hs.smul hy))

theorem gF_eq_gate (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (x : Fin n → ℝ) :
    gF ((c, τ), (A₁, A₂)) x = vecMul (vecMul (gate (YF A₁ c τ)
      (A₂ *ᵥ reluV (A₁ *ᵥ x), A₂ *ᵥ hT n A₁ c τ)) A₂) (D1A1 A₁ x) := by
  unfold gF
  rw [vecMul_jac]
  rfl

theorem gS_eq_gate (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (x : Fin n → ℝ) :
    gS ((c, τ), (A₁, A₂)) x = vecMul (vecMul (gate (YS A₁ c τ)
      (A₂ *ᵥ reluV (A₁ *ᵥ x), A₂ *ᵥ hT n A₁ c τ)) A₂) (D1A1 A₁ x) := by
  unfold gS
  rw [vecMul_jac]
  rfl

/-- The representation `p + perp h (perp r (s·γ))` of `Mᵀw` (file `Split`). -/
noncomputable def transRep {q m : ℕ} (v : ℝ) (h g : Fin m → ℝ)
    (W : (Fin q → ℝ) × (Fin q → ℝ) → Fin q → ℝ) (ξ₁ ξ₂ : Fin q → ℝ) (γ : Fin m → ℝ) :
    Fin m → ℝ :=
  ((normSq h)⁻¹ * ∑ i, W (cOf v h ξ₁, lam h g • cOf v h ξ₁ + cOf v (res h g) ξ₂) i *
      cOf v h ξ₁ i) • h +
    perp h (((normSq (res h g))⁻¹ * ∑ i,
      W (cOf v h ξ₁, lam h g • cOf v h ξ₁ + cOf v (res h g) ξ₂) i * cOf v (res h g) ξ₂ i) •
        res h g +
      perp (res h g) ((√v * √(normSq
        (W (cOf v h ξ₁, lam h g • cOf v h ξ₁ + cOf v (res h g) ξ₂)))) • γ))

/-- **Sub-lemma 3 for the Agent (given `A₁`)**: for an admissible direction `Y` and every
measurable `F ≥ 0`, `E_{A₂} F((D₁A₁)ᵀA₂ᵀ D₂Y) = E_{ξ₁,ξ₂,γ} F((D₁A₁)ᵀ transRep)`. -/
theorem agent_plane {m k : ℕ} (v : ℝ) (A₁ : Matrix (Fin m) (Fin k) ℝ) (x : Fin k → ℝ)
    (g : Fin m → ℝ) {Y : (Fin m → ℝ) × (Fin m → ℝ) → Fin m → ℝ} (hY : Measurable Y)
    {F : (Fin k → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ A₂, F (vecMul (vecMul (gate Y (A₂ *ᵥ reluV (A₁ *ᵥ x), A₂ *ᵥ g)) A₂) (D1A1 A₁ x))
        ∂gaussMat m m v =
      ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ γ, F (vecMul (transRep v (reluV (A₁ *ᵥ x)) g (gate Y) ξ₁ ξ₂ γ)
        (D1A1 A₁ x)) ∂stdGauss (Fin m) ∂stdGauss (Fin m) ∂stdGauss (Fin m) := by
  have hF' : Measurable (fun t : (Fin m → ℝ) × (Fin m → ℝ) × (Fin m → ℝ) =>
      F (vecMul t.2.2 (D1A1 A₁ x))) :=
    hF.comp ((Continuous.matrix_vecMul continuous_id continuous_const).measurable.comp
      (measurable_snd.comp measurable_snd))
  exact plane_split_vecMul v (reluV (A₁ *ᵥ x)) g (measurable_gate hY) hF'

/-! ## The Jacobian moments over the four independent blocks -/

lemma measurable_jac_param (x : Fin n → ℝ) :
    Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      jac θ.1 θ.2 x) := by
  have hc1 : ∀ i, Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => (θ.1 *ᵥ x) i) := fun i =>
    (Continuous.measurable (by simp only [mulVec, dotProduct]; fun_prop))
  have hc2 : ∀ j, Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => (θ.2 *ᵥ reluV (θ.1 *ᵥ x)) j) := fun j =>
    (Continuous.measurable (by simp only [mulVec, dotProduct, reluV, relu]; fun_prop))
  refine measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun l => ?_
  simp only [jac, Matrix.of_apply]
  refine (measurable_mask.comp (hc2 j)).mul (Finset.measurable_sum _ fun i _ => ?_)
  refine ((Continuous.measurable (by fun_prop)).mul (measurable_mask.comp (hc1 i))).mul
    (Continuous.measurable (by fun_prop))

lemma measurable_gF_param (c : Fin n → ℝ) (τ : ℝ) (x : Fin n → ℝ) :
    Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      gF ((c, τ), θ) x) := by
  unfold gF
  have hb : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => bhat (bK ((c, τ), θ))) :=
    measurable_bhat.comp (measurable_bK.comp (measurable_const.prodMk measurable_id))
  exact measurable_vecMul_joint.comp (hb.prodMk (measurable_jac_param x))

lemma measurable_gS_param (c : Fin n → ℝ) (τ : ℝ) (x : Fin n → ℝ) :
    Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      gS ((c, τ), θ) x) := by
  unfold gS rK
  have hb : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => bhat (bK ((c, τ), θ))) :=
    measurable_bhat.comp (measurable_bK.comp (measurable_const.prodMk measurable_id))
  have hh : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => hid2 θ.1 θ.2 x) :=
    Continuous.measurable (by unfold hid2 reluV relu; simp only [mulVec, dotProduct]; fun_prop)
  have hr : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      hid2 θ.1 θ.2 x - (∑ j, hid2 θ.1 θ.2 x j * bhat (bK ((c, τ), θ)) j) •
        bhat (bK ((c, τ), θ))) :=
    hh.sub ((Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp hh).mul ((measurable_pi_apply j).comp hb)).smul hb)
  exact measurable_vecMul_joint.comp ((measurable_bhat.comp hr).prodMk (measurable_jac_param x))

/-- **The moment of `JM_hyp` for `y = b̂` over the four independent blocks.** -/
theorem JM_rep_f (c : Fin n → ℝ) (τ : ℝ) (x : Fin n → ℝ) {F : (Fin n → ℝ) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ θ, F (gF ((c, τ), θ) x) ∂nuA n =
      ∫⁻ A₁, ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ γ, F (vecMul (transRep (2 / ((mA n : ℕ) : ℝ))
        (reluV (A₁ *ᵥ x)) (hT n A₁ c τ) (gate (YF A₁ c τ)) ξ₁ ξ₂ γ) (D1A1 A₁ x))
        ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n))
        ∂gaussMat (mA n) n (2 / (n : ℝ)) := by
  rw [show nuA n = (gaussMat (mA n) n (2 / (n : ℝ))).prod
    (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) from rfl]
  rw [lintegral_prod (fun θ => F (gF ((c, τ), θ) x))
    (hF.comp (measurable_gF_param c τ x)).aemeasurable]
  refine lintegral_congr fun A₁ => ?_
  simp only [gF_eq_gate]
  exact agent_plane _ A₁ x _ (measurable_YF A₁ c τ) hF

/-- **The moment of `JM_hyp` for `y = r̂` over the four independent blocks.** -/
theorem JM_rep_s (c : Fin n → ℝ) (τ : ℝ) (x : Fin n → ℝ) {F : (Fin n → ℝ) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ θ, F (gS ((c, τ), θ) x) ∂nuA n =
      ∫⁻ A₁, ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ γ, F (vecMul (transRep (2 / ((mA n : ℕ) : ℝ))
        (reluV (A₁ *ᵥ x)) (hT n A₁ c τ) (gate (YS A₁ c τ)) ξ₁ ξ₂ γ) (D1A1 A₁ x))
        ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n))
        ∂gaussMat (mA n) n (2 / (n : ℝ)) := by
  rw [show nuA n = (gaussMat (mA n) n (2 / (n : ℝ))).prod
    (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) from rfl]
  rw [lintegral_prod (fun θ => F (gS ((c, τ), θ) x))
    (hF.comp (measurable_gS_param c τ x)).aemeasurable]
  refine lintegral_congr fun A₁ => ?_
  simp only [gS_eq_gate]
  exact agent_plane _ A₁ x _ (measurable_YS A₁ c τ) hF

end BstLean.Part167
