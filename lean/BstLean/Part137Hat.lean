import BstLean.Part137Smooth
import BstLean.Part137Tau

/-!
# Part 137, item 4: Lemma H2(b), the computed centre `ψ_s(M₂ h̄₁)`

Role: `delegations/statements/p137-spec.md` (item 4). Paper source: `onW16c-cx.md` §2,
`onW16-opus-prover.md` §1 (H2(b)).

`N` inputs, hidden width `m`, `t = 2/m`, `γ = 2/N`, `θ = (M₁, M₂)`, `h₁(u) = ReLU(M₁ u)`,
`h(u) = hid2 M₁ M₂ u`.

* `h1bar M₁ = E_u h₁(u)` (the paper's `h̄₁ = c_N(|row_j(M₁)|)_j`);
  `GamS M₁ = t·E_u|h₁(u)|²` (the paper's `Γ* = S₁/N`);
  `sS M₁ = √(Γ* − t|h̄₁|²)` (the paper's `s`); `GamS_ge`: `t|h̄₁|² ≤ Γ*`.
* `bhat θ = ψ_s(M₂ h̄₁)` coordinatewise (the computed centre); `That N m u θ = t⟨h(u), b̂⟩`.
* `That_cond`: given `M₁`, `T̂(u)` has mean `Ψ = t·Φ((0, h₁(u)), (s/√t, h̄₁))` over `M₂` and
  `E_{M₂}(T̂(u) − Ψ)² ≤ (6/m)·t|h₁(u)|²·Γ*`.
* `hatFluct_pt`: for a unit vector `u₀` there is a constant `a` with
  `E_θ (T̂(u₀) − a)² ≤ (γ·cHat m)²`, `cHat m² = (6(1 + 5/m) + (2√5·κ(0) + √6)²)/m`.
* `innerFluct137_hat_gen`, `innerFluct137_hat`: `E_θ Var_u T̂ ≤ (γ·cHat m)²`, and `≤ 21.01·γ²/m`
  for `N = 2n`, `m = mW n`, `n ≥ 4096`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part137

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part73 (IsOrth uniformSphere_orth)
open BstLean.Part105 (sphere_cont_integrable)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136

variable {N m : ℕ}

/-! ## Definitions -/

/-- **`h̄₁ = E_u ReLU(M₁ u)`**: the mean of the first hidden vector over the sphere. -/
noncomputable def h1bar (M₁ : Matrix (Fin m) (Fin N) ℝ) : Fin m → ℝ :=
  hbar (uniformSphere N) (fun u => reluV (M₁.mulVec u))

/-- `α(u) = t|h₁(u)|²`, `t = 2/m`. -/
noncomputable def alphaU (M₁ : Matrix (Fin m) (Fin N) ℝ) (u : Fin N → ℝ) : ℝ :=
  2 / (m : ℝ) * normSq (reluV (M₁.mulVec u))

/-- **`Γ* = t·E_u|h₁(u)|²`** (the paper's `S₁/N`). -/
noncomputable def GamS (M₁ : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  ∫ u, alphaU M₁ u ∂uniformSphere N

/-- **`s = √(Γ* − t|h̄₁|²)`**: the width of the smoothing. -/
noncomputable def sS (M₁ : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  √(GamS M₁ - 2 / (m : ℝ) * normSq (h1bar M₁))

/-- **The computed centre `b̂ = ψ_s(M₂ h̄₁)`**, coordinatewise. -/
noncomputable def bhat (θ : HidParam N m) : Fin m → ℝ :=
  fun i => psiS (sS θ.1) ((θ.2.mulVec (h1bar θ.1)) i)

/-- **`T̂(u) = t⟨h(u), b̂⟩`**. -/
noncomputable def That (N m : ℕ) (u : Fin N → ℝ) (θ : HidParam N m) : ℝ :=
  2 / (m : ℝ) * dotp (hid2 θ.1 θ.2 u) (bhat θ)

/-- The constant of H2(b) in this part: `cHat m² = (6(1 + 5/m) + (2√5·κ(0) + √6)²)/m`. -/
noncomputable def cHat (m : ℕ) : ℝ :=
  √(6 * (1 + 5 / (m : ℝ)) / (m : ℝ) + (2 * √5 * kappa 0 + √6) ^ 2 / (m : ℝ))

/-! ## Continuity, measurability, rotations -/

lemma continuous_h1 :
    Continuous (fun p : Matrix (Fin m) (Fin N) ℝ × (Fin N → ℝ) => reluV (p.1.mulVec p.2)) :=
  continuous_reluV.comp (Continuous.matrix_mulVec continuous_fst continuous_snd)

lemma continuous_h1_u (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    Continuous (fun u : Fin N → ℝ => reluV (M₁.mulVec u)) :=
  continuous_h1.comp (continuous_const.prodMk continuous_id)

lemma continuous_h1_M (u : Fin N → ℝ) :
    Continuous (fun M₁ : Matrix (Fin m) (Fin N) ℝ => reluV (M₁.mulVec u)) :=
  continuous_h1.comp (continuous_id.prodMk continuous_const)

lemma continuous_alphaU :
    Continuous (fun p : Matrix (Fin m) (Fin N) ℝ × (Fin N → ℝ) => alphaU p.1 p.2) := by
  unfold alphaU
  exact continuous_const.mul (continuous_normSq.comp continuous_h1)

lemma continuous_alphaU_u (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    Continuous (fun u : Fin N → ℝ => alphaU M₁ u) := by
  unfold alphaU
  exact continuous_const.mul (continuous_normSq.comp (continuous_h1_u M₁))

lemma measurable_h1bar (hN : 1 ≤ N) :
    Measurable (h1bar : Matrix (Fin m) (Fin N) ℝ → Fin m → ℝ) := by
  have := uniformSphere_isProbability N hN
  refine measurable_pi_iff.mpr fun j => ?_
  have hc : Continuous (fun p : Matrix (Fin m) (Fin N) ℝ × (Fin N → ℝ) =>
      reluV (p.1.mulVec p.2) j) := (continuous_apply j).comp continuous_h1
  exact (hc.measurable.stronglyMeasurable.integral_prod_right').measurable

lemma measurable_GamS (hN : 1 ≤ N) : Measurable (GamS : Matrix (Fin m) (Fin N) ℝ → ℝ) := by
  have := uniformSphere_isProbability N hN
  exact (continuous_alphaU.measurable.stronglyMeasurable.integral_prod_right').measurable

lemma measurable_sS (hN : 1 ≤ N) : Measurable (sS : Matrix (Fin m) (Fin N) ℝ → ℝ) :=
  ((measurable_GamS hN).sub ((measurable_normSq.comp (measurable_h1bar hN)).const_mul _)).sqrt

lemma measurable_bhat (hN : 1 ≤ N) : Measurable (bhat : HidParam N m → Fin m → ℝ) := by
  refine measurable_pi_iff.mpr fun i => ?_
  have hmv : Measurable (fun θ : HidParam N m => θ.2.mulVec (h1bar θ.1)) := by
    have hc : Continuous (fun p : Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) => p.1.mulVec p.2) :=
      Continuous.matrix_mulVec continuous_fst continuous_snd
    exact hc.measurable.comp (measurable_snd.prodMk ((measurable_h1bar hN).comp measurable_fst))
  exact measurable_psiS.comp (((measurable_sS hN).comp measurable_fst).prodMk
    ((measurable_pi_apply i).comp hmv))

lemma measurable_That (hN : 1 ≤ N) : Measurable (Function.uncurry (That N m)) := by
  have h1 : Measurable (fun z : (Fin N → ℝ) × HidParam N m => hid2 z.2.1 z.2.2 z.1) :=
    (continuous_hid2_joint.comp (continuous_snd.prodMk continuous_fst)).measurable
  have h2 : Measurable (fun z : (Fin N → ℝ) × HidParam N m => bhat z.2) :=
    (measurable_bhat hN).comp measurable_snd
  have : Function.uncurry (That N m) = fun z : (Fin N → ℝ) × HidParam N m =>
      2 / (m : ℝ) * dotp (hid2 z.2.1 z.2.2 z.1) (bhat z.2) := by
    funext z
    rfl
  rw [this]
  exact (continuous_dotp.measurable.comp (h1.prodMk h2)).const_mul _

/-- An integral over the sphere of a continuous function of `M₁ u` does not change under
`M₁ ↦ M₁ O`, `O` orthogonal. -/
lemma sphere_rot_integral (O : Matrix (Fin N) (Fin N) ℝ) (hO : IsOrth O)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) {F : (Fin m → ℝ) → ℝ} (hF : Continuous F) :
    ∫ u, F ((M₁ * O).mulVec u) ∂uniformSphere N = ∫ u, F (M₁.mulVec u) ∂uniformSphere N := by
  have hmO : Measurable (fun u : Fin N → ℝ => O.mulVec u) := by fun_prop
  have hc : Continuous (fun u : Fin N → ℝ => F (M₁.mulVec u)) :=
    hF.comp (Continuous.matrix_mulVec continuous_const continuous_id)
  have h := integral_map (μ := uniformSphere N) hmO.aemeasurable
    (f := fun u => F (M₁.mulVec u)) hc.aestronglyMeasurable
  rw [uniformSphere_orth O hO] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  change F ((M₁ * O).mulVec u) = F (M₁.mulVec (O.mulVec u))
  rw [Matrix.mulVec_mulVec]

lemma h1bar_rot (O : Matrix (Fin N) (Fin N) ℝ) (hO : IsOrth O) (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    h1bar (M₁ * O) = h1bar M₁ := by
  funext j
  exact sphere_rot_integral O hO M₁ (F := fun y => reluV y j)
    ((continuous_apply j).comp continuous_reluV)

lemma GamS_rot (O : Matrix (Fin N) (Fin N) ℝ) (hO : IsOrth O) (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    GamS (M₁ * O) = GamS M₁ :=
  sphere_rot_integral O hO M₁ (F := fun y => 2 / (m : ℝ) * normSq (reluV y))
    (continuous_const.mul (continuous_normSq.comp continuous_reluV))

/-- The computed centre does not change under `M₁ ↦ M₁ O`, `O` orthogonal. -/
theorem bhat_rot (O : Matrix (Fin N) (Fin N) ℝ) (hO : IsOrth O) (θ : HidParam N m) :
    bhat (rotP O θ) = bhat θ := by
  unfold bhat sS
  simp only [rotP]
  rw [h1bar_rot O hO, GamS_rot O hO]

/-- `T̂` is exchangeable. -/
theorem exch_That : Exch (That N m) := fun O hO u θ => by
  change 2 / (m : ℝ) * dotp (hid2 θ.1 θ.2 (O.mulVec u)) (bhat θ) =
    2 / (m : ℝ) * dotp (hid2 (rotP O θ).1 (rotP O θ).2 u) (bhat (rotP O θ))
  rw [bhat_rot O hO, hid2_exchange]

/-! ## The width of the smoothing -/

/-- `⟨g, h̄₁⟩ = E_u⟨g, h₁(u)⟩`. -/
lemma dotp_h1bar (hN : 1 ≤ N) (g : Fin m → ℝ) (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    dotp g (h1bar M₁) = ∫ u, dotp g (reluV (M₁.mulVec u)) ∂uniformSphere N := by
  unfold dotp
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      Integrable (fun u : Fin N → ℝ => g j * reluV (M₁.mulVec u) j) (uniformSphere N) :=
    fun j _ => (sphere_cont_integrable hN
      ((continuous_apply j).comp (continuous_h1_u M₁))).const_mul _
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  rfl

/-- `t|h̄₁|² ≤ Γ*` (Jensen). -/
theorem GamS_ge (hN : 1 ≤ N) (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    2 / (m : ℝ) * normSq (h1bar M₁) ≤ GamS M₁ := by
  have := uniformSphere_isProbability N hN
  have hint : ∀ j : Fin m, Integrable (fun u : Fin N → ℝ => reluV (M₁.mulVec u) j ^ 2)
      (uniformSphere N) := fun j =>
    sphere_cont_integrable hN (((continuous_apply j).comp (continuous_h1_u M₁)).pow 2)
  have h1 : normSq (h1bar M₁) ≤ ∫ u, normSq (reluV (M₁.mulVec u)) ∂uniformSphere N := by
    unfold normSq
    rw [integral_finsetSum _ fun j _ => hint j]
    refine Finset.sum_le_sum fun j _ => ?_
    exact sq_integral_le (hint j)
  unfold GamS alphaU
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

lemma sS_sq (hN : 1 ≤ N) (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    sS M₁ ^ 2 = GamS M₁ - 2 / (m : ℝ) * normSq (h1bar M₁) := by
  unfold sS
  rw [Real.sq_sqrt (by linarith [GamS_ge hN M₁])]

lemma alphaU_nonneg (M₁ : Matrix (Fin m) (Fin N) ℝ) (u : Fin N → ℝ) : 0 ≤ alphaU M₁ u :=
  mul_nonneg (by positivity) (normSq_nonneg _)

lemma GamS_nonneg (M₁ : Matrix (Fin m) (Fin N) ℝ) : 0 ≤ GamS M₁ :=
  integral_nonneg fun u => alphaU_nonneg M₁ u

/-! ## Given `M₁`: the mean and the variance over `M₂` -/

/-- The conditional mean of `T̂(u)` given `M₁`: `Ψ = t·Φ((0, h₁(u)), (s/√t, h̄₁))`. -/
noncomputable def PsiM (M₁ : Matrix (Fin m) (Fin N) ℝ) (u : Fin N → ℝ) : ℝ :=
  2 / (m : ℝ) * kernelPhi (Fin.cons 0 (reluV (M₁.mulVec u)) : Fin (m + 1) → ℝ)
    (Fin.cons (sS M₁ / √(2 / (m : ℝ))) (h1bar M₁) : Fin (m + 1) → ℝ)

/-- **Given `M₁`** (conditional row independence, `onW16c-cx.md` §1): `T̂(u)` has mean `Ψ` over
`M₂`, and `E_{M₂}(T̂(u) − Ψ)² ≤ (6/m)·α(u)·Γ*`. -/
theorem That_cond (hN : 1 ≤ N) (hm : 1 ≤ m) (M₁ : Matrix (Fin m) (Fin N) ℝ) (u : Fin N → ℝ) :
    Integrable (fun M₂ : Matrix (Fin m) (Fin m) ℝ => That N m u (M₁, M₂) - PsiM M₁ u)
      (gaussMat m m (2 / (m : ℝ))) ∧
    ∫ M₂ : Matrix (Fin m) (Fin m) ℝ, (That N m u (M₁, M₂) - PsiM M₁ u)
      ∂gaussMat m m (2 / (m : ℝ)) = 0 ∧
    Integrable (fun M₂ : Matrix (Fin m) (Fin m) ℝ => (That N m u (M₁, M₂) - PsiM M₁ u) ^ 2)
      (gaussMat m m (2 / (m : ℝ))) ∧
    ∫ M₂ : Matrix (Fin m) (Fin m) ℝ, (That N m u (M₁, M₂) - PsiM M₁ u) ^ 2
      ∂gaussMat m m (2 / (m : ℝ)) ≤ 6 / (m : ℝ) * alphaU M₁ u * GamS M₁ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hv : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  set v : ℝ := 2 / (m : ℝ) with hvdef
  set g : Fin m → ℝ := reluV (M₁.mulVec u) with hg
  set gb : Fin m → ℝ := h1bar M₁ with hgb
  set s : ℝ := sS M₁ with hs
  obtain ⟨i1, e1, i2, u2⟩ := smooth_layer (m := m) hv s g gb
  have hT : ∀ M₂ : Matrix (Fin m) (Fin m) ℝ, That N m u (M₁, M₂) - PsiM M₁ u =
      v * (dotp (reluV (M₂.mulVec g)) (fun i => psiS s ((M₂.mulVec gb) i)) -
        (m : ℝ) * cS v s g gb) := by
    intro M₂
    have e : That N m u (M₁, M₂) =
        v * dotp (reluV (M₂.mulVec g)) (fun i => psiS s ((M₂.mulVec gb) i)) := rfl
    have e' : PsiM M₁ u = v * ((m : ℝ) * cS v s g gb) := by
      unfold PsiM cS
      rw [← hvdef, ← hg, ← hgb, ← hs]
      rw [hvdef]
      field_simp
    rw [e, e']
    ring
  simp_rw [hT]
  have iR : Integrable (fun M₂ : Matrix (Fin m) (Fin m) ℝ =>
      dotp (reluV (M₂.mulVec g)) (fun i => psiS s ((M₂.mulVec gb) i)) - (m : ℝ) * cS v s g gb)
      (gaussMat m m v) := i1.sub (integrable_const _)
  refine ⟨iR.const_mul v, ?_, ?_, ?_⟩
  · rw [integral_const_mul, integral_sub i1 (integrable_const _), e1]
    simp
  · simp_rw [mul_pow]
    exact i2.const_mul _
  · simp_rw [mul_pow]
    rw [integral_const_mul]
    refine (mul_le_mul_of_nonneg_left u2 (sq_nonneg v)).trans (le_of_eq ?_)
    have hG : s ^ 2 / v + normSq gb = GamS M₁ / v := by
      rw [hs, sS_sq hN, ← hvdef, ← hgb]
      field_simp
      ring
    rw [hG]
    unfold alphaU
    rw [← hvdef, ← hg, hvdef]
    field_simp
    ring

/-! ## Over `M₁` -/

section first

/-- Second moment about a constant from the first two moments. -/
lemma integral_sq_sub_const {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (h1 : Integrable X μ)
    (h2 : Integrable (fun ω => X ω ^ 2) μ) (c : ℝ) :
    Integrable (fun ω => (X ω - c) ^ 2) μ ∧
      ∫ ω, (X ω - c) ^ 2 ∂μ = ∫ ω, X ω ^ 2 ∂μ - 2 * c * ∫ ω, X ω ∂μ + c ^ 2 := by
  have e : (fun ω => (X ω - c) ^ 2) = fun ω => X ω ^ 2 - 2 * c * X ω + c ^ 2 := by
    funext ω
    ring
  have iB : Integrable (fun ω => 2 * c * X ω) μ := h1.const_mul _
  have iAB : Integrable (fun ω => X ω ^ 2 - 2 * c * X ω) μ := h2.sub iB
  rw [e]
  refine ⟨iAB.add (integrable_const _), ?_⟩
  rw [integral_add iAB (integrable_const _), integral_sub h2 iB, integral_const_mul]
  simp

/-- `‖α(u) − γ‖₂ = γ√(5/m)` and `‖α(u)‖₂ = γ√(1 + 5/m)` over `M₁`, for a unit vector `u`. -/
lemma alpha_L2 (hN : 1 ≤ N) (hm : 1 ≤ m) {u : Fin N → ℝ} (hu : normSq u = 1) :
    L2le (gaussMat m N (2 / (N : ℝ))) (fun M₁ => alphaU M₁ u - 2 / (N : ℝ))
        (2 / (N : ℝ) * √(5 / (m : ℝ))) ∧
      L2le (gaussMat m N (2 / (N : ℝ))) (fun M₁ => alphaU M₁ u)
        (2 / (N : ℝ) * √(1 + 5 / (m : ℝ))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
  obtain ⟨i2, e2⟩ := layer_relu_sq (m := m) hv u
  obtain ⟨i4, e4⟩ := layer_relu_four (m := m) hv u
  rw [hu] at e2 e4
  have hmeas : Measurable (fun M₁ : Matrix (Fin m) (Fin N) ℝ => alphaU M₁ u) :=
    (continuous_const.mul (continuous_normSq.comp (continuous_h1_M u))).measurable
  have iA : Integrable (fun M₁ : Matrix (Fin m) (Fin N) ℝ => alphaU M₁ u)
      (gaussMat m N (2 / (N : ℝ))) := i2.const_mul _
  have eA : ∫ M₁ : Matrix (Fin m) (Fin N) ℝ, alphaU M₁ u ∂gaussMat m N (2 / (N : ℝ)) =
      2 / (N : ℝ) := by
    unfold alphaU
    rw [integral_const_mul, e2]
    field_simp
  have hsq : (fun M₁ : Matrix (Fin m) (Fin N) ℝ => alphaU M₁ u ^ 2) = fun M₁ =>
      (2 / (m : ℝ)) ^ 2 * normSq (reluV (M₁.mulVec u)) ^ 2 := by
    funext M₁
    unfold alphaU
    ring
  have iA2 : Integrable (fun M₁ : Matrix (Fin m) (Fin N) ℝ => alphaU M₁ u ^ 2)
      (gaussMat m N (2 / (N : ℝ))) := by
    rw [hsq]
    exact i4.const_mul _
  have eA2 : ∫ M₁ : Matrix (Fin m) (Fin N) ℝ, alphaU M₁ u ^ 2 ∂gaussMat m N (2 / (N : ℝ)) =
      (2 / (N : ℝ)) ^ 2 * (1 + 5 / (m : ℝ)) := by
    rw [hsq, integral_const_mul, e4]
    field_simp
    ring
  obtain ⟨iC, eC⟩ := integral_sq_sub_const iA iA2 (2 / (N : ℝ))
  constructor
  · refine ⟨(hmeas.sub_const _).aestronglyMeasurable, iC, ?_⟩
    rw [eC, eA2, eA, mul_pow, Real.sq_sqrt (by positivity)]
    refine le_of_eq ?_
    ring
  · refine ⟨hmeas.aestronglyMeasurable, iA2, ?_⟩
    rw [eA2, mul_pow, Real.sq_sqrt (by positivity)]

/-- `‖Γ* − γ‖₂ ≤ γ√(5/m)` and `‖Γ*‖₂ ≤ γ√(1 + 5/m)` over `M₁` (Jensen over the input). -/
lemma GamS_L2 (hN : 1 ≤ N) (hm : 1 ≤ m) :
    L2le (gaussMat m N (2 / (N : ℝ))) (fun M₁ : Matrix (Fin m) (Fin N) ℝ => GamS M₁ - 2 / (N : ℝ))
        (2 / (N : ℝ) * √(5 / (m : ℝ))) ∧
      L2le (gaussMat m N (2 / (N : ℝ))) (fun M₁ : Matrix (Fin m) (Fin N) ℝ => GamS M₁)
        (2 / (N : ℝ) * √(1 + 5 / (m : ℝ))) := by
  have := uniformSphere_isProbability N hN
  have hc := continuous_alphaU (N := N) (m := m)
  have h1 : L2le ((gaussMat m N (2 / (N : ℝ))).prod (uniformSphere N))
      (fun p : Matrix (Fin m) (Fin N) ℝ × (Fin N → ℝ) => alphaU p.1 p.2 - 2 / (N : ℝ))
      (2 / (N : ℝ) * √(5 / (m : ℝ))) := by
    refine L2le.prod_const_left (hc.measurable.sub_const _).aestronglyMeasurable ?_
    filter_upwards [uniformSphere_ae_sphere N] with u hu
    exact (alpha_L2 hN hm hu).1
  have h2 : L2le ((gaussMat m N (2 / (N : ℝ))).prod (uniformSphere N))
      (fun p : Matrix (Fin m) (Fin N) ℝ × (Fin N → ℝ) => alphaU p.1 p.2)
      (2 / (N : ℝ) * √(1 + 5 / (m : ℝ))) := by
    refine L2le.prod_const_left hc.measurable.aestronglyMeasurable ?_
    filter_upwards [uniformSphere_ae_sphere N] with u hu
    exact (alpha_L2 hN hm hu).2
  constructor
  · refine h1.integral_right.congr_fun fun M₁ => ?_
    change ∫ u, (alphaU M₁ u - 2 / (N : ℝ)) ∂uniformSphere N = GamS M₁ - 2 / (N : ℝ)
    rw [integral_sub (sphere_cont_integrable hN (continuous_alphaU_u M₁)) (integrable_const _)]
    simp [GamS]
  · exact h2.integral_right

/-- `q₁(u₀) = E_u κ(⟨u₀, u⟩)`. -/
noncomputable def q1 (u0 : Fin N → ℝ) : ℝ := ∫ u, kappa (dotp u0 u) ∂uniformSphere N

lemma continuous_kappa_dot (u0 : Fin N → ℝ) :
    Continuous (fun u : Fin N → ℝ => kappa (dotp u0 u)) :=
  continuous_kappa.comp (continuous_dotp.comp (continuous_const.prodMk continuous_id))

lemma q1_mem (hN : 1 ≤ N) {u0 : Fin N → ℝ} (hu0 : normSq u0 = 1) : 0 ≤ q1 u0 ∧ q1 u0 ≤ 1 := by
  have := uniformSphere_isProbability N hN
  have hmem : ∀ᵐ u ∂uniformSphere N, 0 ≤ kappa (dotp u0 u) ∧ kappa (dotp u0 u) ≤ 1 := by
    filter_upwards [uniformSphere_ae_sphere N] with u hu
    have hd := dotp_unit_mem' hu0 (show normSq u = 1 from hu)
    exact kappa_mem hd.1 hd.2
  constructor
  · exact integral_nonneg_of_ae (hmem.mono fun u h => h.1)
  · have h := integral_mono_ae (sphere_cont_integrable hN (continuous_kappa_dot u0))
      (integrable_const (1 : ℝ)) (hmem.mono fun u h => h.2)
    simpa [q1] using h

/-- The covariance term `c = t⟨h₁(u₀), h̄₁⟩`: `‖c − γ q₁‖₂ ≤ γ√(6/m)` over `M₁`. -/
lemma cov_L2 (hN : 1 ≤ N) (hm : 1 ≤ m) {u0 : Fin N → ℝ} (hu0 : normSq u0 = 1) :
    L2le (gaussMat m N (2 / (N : ℝ)))
      (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
        2 / (m : ℝ) * dotp (reluV (M₁.mulVec u0)) (h1bar M₁) - 2 / (N : ℝ) * q1 u0)
      (2 / (N : ℝ) * √(6 / (m : ℝ))) := by
  have := uniformSphere_isProbability N hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
  let f : Matrix (Fin m) (Fin N) ℝ × (Fin N → ℝ) → ℝ := fun p =>
    2 / (m : ℝ) * dotp (reluV (p.1.mulVec u0)) (reluV (p.1.mulVec p.2)) -
      2 / (N : ℝ) * kappa (dotp u0 p.2)
  have hfc : Continuous f := by
    have h1 : Continuous (fun p : Matrix (Fin m) (Fin N) ℝ × (Fin N → ℝ) =>
        reluV (p.1.mulVec u0)) := (continuous_h1_M u0).comp continuous_fst
    exact (continuous_const.mul (continuous_dotp.comp (h1.prodMk continuous_h1))).sub
      (continuous_const.mul ((continuous_kappa_dot u0).comp continuous_snd))
  have h1 : L2le ((gaussMat m N (2 / (N : ℝ))).prod (uniformSphere N)) f
      (2 / (N : ℝ) * √(6 / (m : ℝ))) := by
    refine L2le.prod_const_left hfc.measurable.aestronglyMeasurable ?_
    filter_upwards [uniformSphere_ae_sphere N] with u hu
    have hu' : normSq u = 1 := hu
    obtain ⟨iV, uV⟩ := layer_dot_relu_var (m := m) hv u0 u
    have ek : kernelPhi u0 u = kappa (dotp u0 u) := by
      rw [kernelPhi_eq_psi, psi_unit _ hu0 hu']
    rw [ek, hu0, hu'] at uV
    rw [ek] at iV
    have e : (fun M₁ : Matrix (Fin m) (Fin N) ℝ => f (M₁, u) ^ 2) = fun M₁ =>
        (2 / (m : ℝ)) ^ 2 * (dotp (reluV (M₁.mulVec u0)) (reluV (M₁.mulVec u)) -
          (m : ℝ) / 2 * (2 / (N : ℝ) * kappa (dotp u0 u))) ^ 2 := by
      funext M₁
      simp only [f]
      field_simp
    refine ⟨(hfc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable, ?_, ?_⟩
    · rw [e]
      exact iV.const_mul _
    · rw [e, integral_const_mul, mul_pow, Real.sq_sqrt (by positivity)]
      refine (mul_le_mul_of_nonneg_left uV (sq_nonneg _)).trans (le_of_eq ?_)
      field_simp
      ring
  refine h1.integral_right.congr_fun fun M₁ => ?_
  change ∫ u, (2 / (m : ℝ) * dotp (reluV (M₁.mulVec u0)) (reluV (M₁.mulVec u)) -
      2 / (N : ℝ) * kappa (dotp u0 u)) ∂uniformSphere N = _
  have iA : Integrable (fun u : Fin N → ℝ =>
      2 / (m : ℝ) * dotp (reluV (M₁.mulVec u0)) (reluV (M₁.mulVec u))) (uniformSphere N) :=
    sphere_cont_integrable hN (continuous_const.mul
      (continuous_dotp.comp (continuous_const.prodMk (continuous_h1_u M₁))))
  have iB : Integrable (fun u : Fin N → ℝ => 2 / (N : ℝ) * kappa (dotp u0 u))
      (uniformSphere N) :=
    sphere_cont_integrable hN (continuous_const.mul (continuous_kappa_dot u0))
  rw [integral_sub iA iB, integral_const_mul, integral_const_mul, ← dotp_h1bar hN]
  rfl

/-- `|√a·√b − g| ≤ |a − g| + |b − g|` for `a, b ≥ 0`. -/
lemma sqrt_mul_sub {a b g : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |√a * √b - g| ≤ |a - g| + |b - g| := by
  have hx := Real.sqrt_nonneg a
  have hy := Real.sqrt_nonneg b
  have hxa := Real.sq_sqrt ha
  have hyb := Real.sq_sqrt hb
  have h1 := le_abs_self (a - g)
  have h2 := le_abs_self (b - g)
  have h3 := neg_abs_le (a - g)
  have h4 := neg_abs_le (b - g)
  rw [abs_le]
  constructor
  · rcases le_total (√a) (√b) with h | h
    · nlinarith
    · nlinarith
  · nlinarith [sq_nonneg (√a - √b)]

end first

/-! ## The pointwise bound -/

/-- **The assembly of H2(b)** (total variance over `M₁` and `M₂`), from `L²` bounds `aG`, `aC`
of `Γ* − γ` and of the covariance term `c − γ q₁` over `M₁`: for a unit vector `u₀`,
`‖T̂(u₀) − γ·κ(q₁)‖²_{L²(θ)} ≤ 6γ²(1 + 5/m)/m + (κ(0)·(γ√(5/m) + aG) + aC)²`. -/
theorem hatFluct_core (hN : 1 ≤ N) (hm : 1 ≤ m) {u0 : Fin N → ℝ} (hu0 : normSq u0 = 1)
    {aG aC : ℝ} (haG : 0 ≤ aG) (haC : 0 ≤ aC)
    (hG1 : L2le (gaussMat m N (2 / (N : ℝ)))
      (fun M₁ : Matrix (Fin m) (Fin N) ℝ => GamS M₁ - 2 / (N : ℝ)) aG)
    (hC : L2le (gaussMat m N (2 / (N : ℝ)))
      (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
        2 / (m : ℝ) * dotp (reluV (M₁.mulVec u0)) (h1bar M₁) - 2 / (N : ℝ) * q1 u0) aC) :
    L2le (hidGauss N m)
      (fun θ => That N m u0 θ - 2 / (N : ℝ) * kappa (q1 u0))
      (√((2 / (N : ℝ) * √(6 * (1 + 5 / (m : ℝ)) / (m : ℝ))) ^ 2 +
        (kappa 0 * (2 / (N : ℝ) * √(5 / (m : ℝ)) + aG) + aC) ^ 2)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  have hγ : (0 : ℝ) < 2 / (N : ℝ) := by positivity
  have hk0 : 0 ≤ kappa 0 := by rw [kappa_zero]; positivity
  obtain ⟨hq0, hq1⟩ := q1_mem hN hu0
  obtain ⟨hA1, hA2⟩ := alpha_L2 (m := m) hN hm hu0
  obtain ⟨-, hG2⟩ := GamS_L2 (N := N) (m := m) hN hm
  have hTm : Measurable (That N m u0) := (measurable_That hN).of_uncurry_left
  -- the conditional mean is measurable
  have hPm : Measurable (fun M₁ : Matrix (Fin m) (Fin N) ℝ => PsiM M₁ u0) := by
    have e : (fun M₁ : Matrix (Fin m) (Fin N) ℝ => PsiM M₁ u0) = fun M₁ =>
        ∫ M₂ : Matrix (Fin m) (Fin m) ℝ, That N m u0 (M₁, M₂) ∂gaussMat m m (2 / (m : ℝ)) := by
      funext M₁
      obtain ⟨i1, e1, -, -⟩ := That_cond hN hm M₁ u0
      have i0 : Integrable (fun M₂ : Matrix (Fin m) (Fin m) ℝ => That N m u0 (M₁, M₂))
          (gaussMat m m (2 / (m : ℝ))) := by
        have := i1.add (integrable_const (PsiM M₁ u0))
        refine this.congr (Filter.Eventually.of_forall fun M₂ => ?_)
        simp
      rw [integral_sub i0 (integrable_const _)] at e1
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at e1
      linarith
    rw [e]
    exact (hTm.stronglyMeasurable.integral_prod_right').measurable
  -- `B`: the conditional mean minus the constant
  have hB : L2le (gaussMat m N (2 / (N : ℝ)))
      (fun M₁ : Matrix (Fin m) (Fin N) ℝ => PsiM M₁ u0 - 2 / (N : ℝ) * kappa (q1 u0))
      (kappa 0 * (2 / (N : ℝ) * √(5 / (m : ℝ)) + aG) + aC) := by
    have habs : ∀ {f : Matrix (Fin m) (Fin N) ℝ → ℝ} {a : ℝ},
        L2le (gaussMat m N (2 / (N : ℝ))) f a →
        L2le (gaussMat m N (2 / (N : ℝ))) (fun M₁ => |f M₁|) a := fun {f a} h =>
      L2le.of_abs_le (continuous_abs.comp_aestronglyMeasurable h.aesm) h
        (fun ω => le_of_eq (abs_abs _))
    have hsum := (((habs hA1).add' (habs hG1) (by positivity) haG).const_mul_nonneg
      hk0).add' (habs hC) (mul_nonneg hk0 (add_nonneg (by positivity) haG)) haC
    refine L2le.of_abs_le (hPm.sub_const _).aestronglyMeasurable hsum fun M₁ => ?_
    rw [abs_of_nonneg (add_nonneg (mul_nonneg hk0 (add_nonneg (abs_nonneg _) (abs_nonneg _)))
      (abs_nonneg _))]
    -- the perspective bound
    set gP : Fin (m + 1) → ℝ := Fin.cons 0 (reluV (M₁.mulVec u0)) with hgP
    set gbP : Fin (m + 1) → ℝ := Fin.cons (sS M₁ / √(2 / (m : ℝ))) (h1bar M₁) with hgbP
    have hpb : (0 : ℝ) ≤ 2 / (N : ℝ) / (2 / (m : ℝ)) := by positivity
    have hp := psi_abs_sub kGood_kappa gP gbP hpb
      (show |q1 u0| ≤ 1 by rw [abs_of_nonneg hq0]; exact hq1)
    have hn1 : normSq gP = normSq (reluV (M₁.mulVec u0)) := by
      rw [hgP, normSq_cons]
      simp
    have hn2 : normSq gbP = GamS M₁ / (2 / (m : ℝ)) := by
      rw [hgbP, normSq_cons, div_pow, Real.sq_sqrt hv.le, sS_sq hN]
      field_simp
      ring
    have hd : dotp gP gbP = dotp (reluV (M₁.mulVec u0)) (h1bar M₁) := by
      rw [hgP, hgbP, dotp_cons]
      simp
    have hnr : 2 / (m : ℝ) * (nrm gP * nrm gbP) = √(alphaU M₁ u0) * √(GamS M₁) := by
      unfold nrm
      rw [hn1, hn2]
      have e1 : alphaU M₁ u0 = 2 / (m : ℝ) * normSq (reluV (M₁.mulVec u0)) := rfl
      have e2 : GamS M₁ = 2 / (m : ℝ) * (GamS M₁ / (2 / (m : ℝ))) := by
        field_simp
      rw [e1]
      conv_rhs => rw [e2]
      rw [Real.sqrt_mul hv.le, Real.sqrt_mul hv.le]
      have := Real.mul_self_sqrt hv.le
      calc 2 / (m : ℝ) * (√(normSq (reluV (M₁.mulVec u0))) * √(GamS M₁ / (2 / (m : ℝ))))
          = (√(2 / (m : ℝ)) * √(2 / (m : ℝ))) * (√(normSq (reluV (M₁.mulVec u0))) *
              √(GamS M₁ / (2 / (m : ℝ)))) := by rw [this]
        _ = _ := by ring
    have hPsi : PsiM M₁ u0 = 2 / (m : ℝ) * psi kappa gP gbP := rfl
    have hsq := sqrt_mul_sub (g := 2 / (N : ℝ)) (alphaU_nonneg M₁ u0) (GamS_nonneg M₁)
    have e3 : PsiM M₁ u0 - 2 / (N : ℝ) * kappa (q1 u0) =
        2 / (m : ℝ) * (psi kappa gP gbP - 2 / (N : ℝ) / (2 / (m : ℝ)) * kappa (q1 u0)) := by
      rw [hPsi]
      field_simp
    have e4 : √(alphaU M₁ u0) * √(GamS M₁) - 2 / (N : ℝ) =
        2 / (m : ℝ) * (nrm gP * nrm gbP - 2 / (N : ℝ) / (2 / (m : ℝ))) := by
      rw [← hnr]
      field_simp
    have e5 : 2 / (m : ℝ) * dotp (reluV (M₁.mulVec u0)) (h1bar M₁) - 2 / (N : ℝ) * q1 u0 =
        2 / (m : ℝ) * (dotp gP gbP - 2 / (N : ℝ) / (2 / (m : ℝ)) * q1 u0) := by
      rw [hd]
      field_simp
    rw [e3, abs_mul, abs_of_pos hv, e5, abs_mul, abs_of_pos hv]
    have h6 : |√(alphaU M₁ u0) * √(GamS M₁) - 2 / (N : ℝ)| =
        2 / (m : ℝ) * |nrm gP * nrm gbP - 2 / (N : ℝ) / (2 / (m : ℝ))| := by
      rw [e4, abs_mul, abs_of_pos hv]
    have h7 := mul_le_mul_of_nonneg_left hp hv.le
    have h8 : kappa 0 * (2 / (m : ℝ) * |nrm gP * nrm gbP - 2 / (N : ℝ) / (2 / (m : ℝ))|) ≤
        kappa 0 * (|alphaU M₁ u0 - 2 / (N : ℝ)| + |GamS M₁ - 2 / (N : ℝ)|) := by
      rw [← h6]
      exact mul_le_mul_of_nonneg_left hsq hk0
    nlinarith [h7, h8]
  -- `g`: the conditional standard deviation
  have hg : L2le (gaussMat m N (2 / (N : ℝ)))
      (fun M₁ : Matrix (Fin m) (Fin N) ℝ => √(6 / (m : ℝ) * alphaU M₁ u0 * GamS M₁))
      (2 / (N : ℝ) * √(6 * (1 + 5 / (m : ℝ)) / (m : ℝ))) := by
    have hmα : Measurable (fun M₁ : Matrix (Fin m) (Fin N) ℝ => alphaU M₁ u0) :=
      (continuous_const.mul (continuous_normSq.comp (continuous_h1_M u0))).measurable
    refine L2le.of_sq_le
      (G := fun M₁ => 6 / (m : ℝ) * ((alphaU M₁ u0 ^ 2 + GamS M₁ ^ 2) / 2))
      ((((hmα.const_mul _).mul (measurable_GamS hN)).sqrt).aestronglyMeasurable)
      (((hA2.int_sq.add hG2.int_sq).div_const 2).const_mul _) (fun M₁ => ?_) ?_
    · rw [Real.sq_sqrt (mul_nonneg (mul_nonneg (by positivity) (alphaU_nonneg M₁ u0))
        (GamS_nonneg M₁))]
      have : alphaU M₁ u0 * GamS M₁ ≤ (alphaU M₁ u0 ^ 2 + GamS M₁ ^ 2) / 2 := by
        nlinarith [sq_nonneg (alphaU M₁ u0 - GamS M₁)]
      calc 6 / (m : ℝ) * alphaU M₁ u0 * GamS M₁ = 6 / (m : ℝ) * (alphaU M₁ u0 * GamS M₁) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
    · have i1 : Integrable (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
          (alphaU M₁ u0 ^ 2 + GamS M₁ ^ 2) / 2) (gaussMat m N (2 / (N : ℝ))) :=
        (hA2.int_sq.add hG2.int_sq).div_const 2
      rw [integral_const_mul, integral_div, integral_add hA2.int_sq hG2.int_sq]
      have a1 := hA2.le
      have a2 := hG2.le
      rw [mul_pow, Real.sq_sqrt (by positivity)] at a1 a2
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have h9 : (∫ M₁ : Matrix (Fin m) (Fin N) ℝ, alphaU M₁ u0 ^ 2 ∂gaussMat m N (2 / (N : ℝ)) +
          ∫ M₁ : Matrix (Fin m) (Fin N) ℝ, GamS M₁ ^ 2 ∂gaussMat m N (2 / (N : ℝ))) / 2 ≤
          (2 / (N : ℝ)) ^ 2 * (1 + 5 / (m : ℝ)) := by linarith
      calc 6 / (m : ℝ) * ((∫ M₁ : Matrix (Fin m) (Fin N) ℝ, alphaU M₁ u0 ^ 2
            ∂gaussMat m N (2 / (N : ℝ)) + ∫ M₁ : Matrix (Fin m) (Fin N) ℝ, GamS M₁ ^ 2
            ∂gaussMat m N (2 / (N : ℝ))) / 2)
          ≤ 6 / (m : ℝ) * ((2 / (N : ℝ)) ^ 2 * (1 + 5 / (m : ℝ))) :=
            mul_le_mul_of_nonneg_left h9 (by positivity)
        _ = _ := by ring
  -- the sum of squares
  have hRm : Measurable (fun z : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      That N m u0 z - PsiM z.1 u0) := hTm.sub (hPm.comp measurable_fst)
  have key := L2le.prod_orth (μ := gaussMat m N (2 / (N : ℝ))) (ν := gaussMat m m (2 / (m : ℝ)))
    hRm.aestronglyMeasurable hB hg (fun M₁ => by
      obtain ⟨i1, e1, i2, u2⟩ := That_cond hN hm M₁ u0
      refine ⟨i1, e1, i2, u2.trans (le_of_eq ?_)⟩
      rw [Real.sq_sqrt (mul_nonneg (mul_nonneg (by positivity) (alphaU_nonneg M₁ u0))
        (GamS_nonneg M₁))])
  have key' : L2le (hidGauss N m) (fun z : HidParam N m => That N m u0 z - PsiM z.1 u0 +
      (PsiM z.1 u0 - 2 / (N : ℝ) * kappa (q1 u0))) _ := key
  exact key'.congr_fun fun θ => by ring

/-- **Lemma H2(b), with the first constant of this part**, every `N, m ≥ 1`: for a unit vector
`u₀`, `‖T̂(u₀) − γ·κ(q₁)‖_{L²(θ)} ≤ γ·cHat m`. -/
theorem hatFluct_pt (hN : 1 ≤ N) (hm : 1 ≤ m) {u0 : Fin N → ℝ} (hu0 : normSq u0 = 1) :
    L2le (hidGauss N m)
      (fun θ => That N m u0 θ - 2 / (N : ℝ) * kappa (q1 u0)) (2 / (N : ℝ) * cHat m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hγ : (0 : ℝ) < 2 / (N : ℝ) := by positivity
  have key := hatFluct_core hN hm hu0 (aG := 2 / (N : ℝ) * √(5 / (m : ℝ)))
    (aC := 2 / (N : ℝ) * √(6 / (m : ℝ))) (by positivity) (by positivity)
    (GamS_L2 (N := N) (m := m) hN hm).1 (cov_L2 (m := m) hN hm hu0)
  refine key.congr_bound ?_
  unfold cHat
  have e5 : (kappa 0 * (2 / (N : ℝ) * √(5 / (m : ℝ)) + 2 / (N : ℝ) * √(5 / (m : ℝ))) +
      2 / (N : ℝ) * √(6 / (m : ℝ))) =
      2 / (N : ℝ) * ((2 * √5 * kappa 0 + √6) / √(m : ℝ)) := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_div (by norm_num)]
    ring
  have e6 : (2 / (N : ℝ) * √(6 * (1 + 5 / (m : ℝ)) / (m : ℝ))) ^ 2 +
      (kappa 0 * (2 / (N : ℝ) * √(5 / (m : ℝ)) + 2 / (N : ℝ) * √(5 / (m : ℝ))) +
        2 / (N : ℝ) * √(6 / (m : ℝ))) ^ 2 =
      (2 / (N : ℝ)) ^ 2 * (6 * (1 + 5 / (m : ℝ)) / (m : ℝ) +
        (2 * √5 * kappa 0 + √6) ^ 2 / (m : ℝ)) := by
    have hs1 := Real.sq_sqrt (show (0 : ℝ) ≤ 6 * (1 + 5 / (m : ℝ)) / (m : ℝ) by positivity)
    have hs2 := Real.sq_sqrt hm'.le
    rw [e5]
    calc (2 / (N : ℝ) * √(6 * (1 + 5 / (m : ℝ)) / (m : ℝ))) ^ 2 +
          (2 / (N : ℝ) * ((2 * √5 * kappa 0 + √6) / √(m : ℝ))) ^ 2
        = (2 / (N : ℝ)) ^ 2 * (√(6 * (1 + 5 / (m : ℝ)) / (m : ℝ)) ^ 2 +
            (2 * √5 * kappa 0 + √6) ^ 2 / √(m : ℝ) ^ 2) := by ring
      _ = _ := by rw [hs1, hs2]
  rw [e6, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hγ.le]

/-! ## Headlines -/

/-- `Var_θ T̂(u₀) ≤ (γ·cHat m)²` for a unit vector `u₀`. -/
theorem hatFluct_var (hN : 1 ≤ N) (hm : 1 ≤ m) {u0 : Fin N → ℝ} (hu0 : normSq u0 = 1) :
    Var[That N m u0; hidGauss N m] ≤ (2 / (N : ℝ) * cHat m) ^ 2 :=
  variance_le_of_L2le (hatFluct_pt hN hm hu0)

/-- **Lemma H2(b), the consequence**, every `N, m ≥ 1`: `E_θ Var_u T̂ ≤ (γ·cHat m)²`. -/
theorem innerFluct137_hat_gen (hN : 1 ≤ N) (hm : 1 ≤ m) :
    ∫ θ, Var[fun u => That N m u θ; uniformSphere N] ∂hidGauss N m ≤
      (2 / (N : ℝ) * cHat m) ^ 2 := by
  have h := hatFluct_pt (m := m) hN hm (normSq_e0 hN)
  exact (exchange137 hN (measurable_That hN) exch_That (normSq_e0 hN) h.int_sq).trans h.le

/-- `θ ↦ Var_u T̂(u; θ)` is integrable. -/
theorem hatFluct_integrable (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (fun θ => Var[fun u => That N m u θ; uniformSphere N]) (hidGauss N m) :=
  exchange137_integrable hN (measurable_That hN) exch_That (normSq_e0 hN)
    (hatFluct_pt (m := m) hN hm (normSq_e0 hN)).int_sq

/-- `cHat m² ≤ 21.01/m` for `m ≥ 10⁶`. -/
lemma cHat_sq_le {m : ℕ} (hm : 1000000 ≤ m) : cHat m ^ 2 ≤ 2101 / 100 / (m : ℝ) := by
  have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have k1 := kappa_zero_le
  have k0 : 0 ≤ kappa 0 := by rw [kappa_zero]; positivity
  have s6 := sqrt6_le
  have s60 : 0 ≤ √6 := Real.sqrt_nonneg _
  have s5 : √(5 : ℝ) ≤ 22361 / 10000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have s50 : 0 ≤ √(5 : ℝ) := Real.sqrt_nonneg _
  unfold cHat
  rw [Real.sq_sqrt (by positivity)]
  have h1 : 5 / (m : ℝ) ≤ 5 / 1000000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm'
  have h3 : 2 * √5 * kappa 0 ≤ 2 * (22361 / 10000) * (31831 / 100000) := by
    have : √5 * kappa 0 ≤ 22361 / 10000 * (31831 / 100000) :=
      mul_le_mul s5 k1 k0 (by norm_num)
    linarith
  have h2 : (2 * √5 * kappa 0 + √6) ^ 2 ≤
      (2 * (22361 / 10000) * (31831 / 100000) + 24495 / 10000) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ hm0.le
  nlinarith

lemma gamma_cHat_le {n : ℕ} (hn : 4096 ≤ n) :
    (2 / ((2 * n : ℕ) : ℝ) * cHat (mW n)) ^ 2 ≤
      2101 / 100 * (2 / ((2 * n : ℕ) : ℝ)) ^ 2 / (mW n : ℝ) := by
  have h := cHat_sq_le (mW_ge_million hn)
  have e : 2101 / 100 * (2 / ((2 * n : ℕ) : ℝ)) ^ 2 / (mW n : ℝ) =
      (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * (2101 / 100 / (mW n : ℝ)) := by ring
  rw [mul_pow, e]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- **Lemma H2(b) for the World network of the Focus** (`N = 2n`, `m = mW n`, `n ≥ 4096`), with
the constant `21.01` of this part: `Var_θ T̂(u₀) ≤ 21.01·γ²/m` for a unit vector `u₀`. -/
theorem hatFluct137_var {n : ℕ} (hn : 4096 ≤ n) {u0 : Fin (2 * n) → ℝ} (hu0 : normSq u0 = 1) :
    Var[That (2 * n) (mW n) u0; hidGauss (2 * n) (mW n)] ≤
      2101 / 100 * (2 / ((2 * n : ℕ) : ℝ)) ^ 2 / (mW n : ℝ) :=
  (hatFluct_var (by omega) (one_le_mW (by omega)) hu0).trans (gamma_cHat_le hn)

/-- **`innerFluct137_hat`** (Lemma H2(b), the consequence, for the computed centre
`b̂ = ψ_s(M₂ h̄₁)`): `N = 2n`, `m = mW n`, every `n ≥ 4096`: `E_θ Var_u T̂ ≤ 21.01·γ²/m`. -/
theorem innerFluct137_hat {n : ℕ} (hn : 4096 ≤ n) :
    ∫ θ, Var[fun u => That (2 * n) (mW n) u θ; uniformSphere (2 * n)]
        ∂hidGauss (2 * n) (mW n) ≤
      2101 / 100 * (2 / ((2 * n : ℕ) : ℝ)) ^ 2 / (mW n : ℝ) :=
  (innerFluct137_hat_gen (by omega) (one_le_mW (by omega))).trans (gamma_cHat_le hn)

end BstLean.Part137
