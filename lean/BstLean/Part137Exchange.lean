import BstLean.Part136Joint
import BstLean.Part80SphSymm

/-!
# Part 137, item 1: Lemma E (the exchange of the input rotation and the first matrix)

Role: `delegations/statements/p137-spec.md`. Paper source: `onW16c-cx.md` §1.

`θ = (M₁, M₂)` are the two hidden matrices of the World network (`HidParam N m`, distribution
`hidGauss N m`, Part 136); `h(u) = hid2 M₁ M₂ u`.

* `hid2_exchange`: `h(O u; M₁, M₂) = h(u; M₁ O, M₂)` (every matrix `O`).
* `hidGauss_rot`: for an orthogonal `O`, `(M₁ O, M₂)` has the distribution of `(M₁, M₂)`.
* `Exch X`: the function `X(u; θ)` satisfies `X(O u; M₁, M₂) = X(u; M₁ O, M₂)` for every
  orthogonal `O`.
* `exch_map`: for an exchangeable `X`, the distribution of `X(u; ·)` over `θ` is the same for
  every unit vector `u`.
* `exchange137`: `E_θ Var_u X ≤ E_θ (X(u₀) − c)²` for every constant `c`;
  `exchange137_var`: `E_θ Var_u X ≤ Var_θ X(u₀)`.
* `exch_avg`: `E_θ X(u₀) = E_θ E_u X(u)` for an integrable exchangeable `X`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part137

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part73 (IsOrth uniformSphere_orth)
open BstLean.Part80 (exists_orth_col)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136

variable {N m : ℕ}

/-- The change of the first matrix: `(M₁, M₂) ↦ (M₁ O, M₂)`. -/
def rotP (O : Matrix (Fin N) (Fin N) ℝ) (θ : HidParam N m) : HidParam N m := (θ.1 * O, θ.2)

/-- **Lemma E, the identity**: `h(O u; M₁, M₂) = h(u; M₁ O, M₂)`. -/
theorem hid2_exchange (O : Matrix (Fin N) (Fin N) ℝ) (θ : HidParam N m) (u : Fin N → ℝ) :
    hid2 θ.1 θ.2 (O.mulVec u) = hid2 (rotP O θ).1 (rotP O θ).2 u := by
  simp only [hid2, rotP, Matrix.mulVec_mulVec]

lemma measurable_rotP (O : Matrix (Fin N) (Fin N) ℝ) :
    Measurable (rotP O : HidParam N m → HidParam N m) := by
  have hmeas : Measurable (fun M : Matrix (Fin m) (Fin N) ℝ => M * O) :=
    (Continuous.matrix_mul continuous_id continuous_const).measurable
  exact (hmeas.comp measurable_fst).prodMk measurable_snd

/-- **Lemma E, the invariance of the distribution**: for an orthogonal `O`, `(M₁ O, M₂)` has the
distribution of `(M₁, M₂)`. -/
theorem hidGauss_rot (O : Matrix (Fin N) (Fin N) ℝ) (hO : IsOrth O) :
    (hidGauss N m).map (rotP O) = hidGauss N m := by
  have hmeas : Measurable (fun M : Matrix (Fin m) (Fin N) ℝ => M * O) :=
    (Continuous.matrix_mul continuous_id continuous_const).measurable
  have h := Measure.map_prod_map (gaussMat m N (2 / (N : ℝ))) (gaussMat m m (2 / (m : ℝ)))
    hmeas measurable_id
  rw [gaussMat_mul_orth _ O hO, Measure.map_id] at h
  unfold hidGauss
  conv_rhs => rw [h]
  rfl

/-- For two unit vectors there is an orthogonal matrix that maps the first to the second. -/
lemma exists_orth_map (hN : 1 ≤ N) {u u0 : Fin N → ℝ} (hu : normSq u = 1)
    (hu0 : normSq u0 = 1) :
    ∃ O : Matrix (Fin N) (Fin N) ℝ, IsOrth O ∧ O.mulVec u0 = u := by
  classical
  let a : Fin N := ⟨0, hN⟩
  obtain ⟨P, hP, hPc⟩ := exists_orth_col a u hu
  obtain ⟨Q, hQ, hQc⟩ := exists_orth_col a u0 hu0
  have e1 : ∀ R : Matrix (Fin N) (Fin N) ℝ, R.mulVec (Pi.single a 1) = fun i => R i a := by
    intro R
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  refine ⟨P * Q.transpose, ?_, ?_⟩
  · unfold IsOrth
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc P.transpose, show P.transpose * P = 1 from hP, Matrix.one_mul, hQ.mul_t]
  · have hQ0 : Q.mulVec (Pi.single a 1) = u0 := by
      rw [e1]
      funext i
      exact hQc i
    have h2 : Q.transpose.mulVec u0 = Pi.single a 1 := by
      rw [← hQ0, Matrix.mulVec_mulVec, show Q.transpose * Q = 1 from hQ, Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, h2, e1]
    funext i
    exact hPc i

/-- **Exchangeable**: `X(O u; M₁, M₂) = X(u; M₁ O, M₂)` for every orthogonal `O`. -/
def Exch (X : (Fin N → ℝ) → HidParam N m → ℝ) : Prop :=
  ∀ O : Matrix (Fin N) (Fin N) ℝ, IsOrth O → ∀ u θ, X (O.mulVec u) θ = X u (rotP O θ)

lemma Exch.comp {X : (Fin N → ℝ) → HidParam N m → ℝ} (hX : Exch X) (g : ℝ → ℝ) :
    Exch (fun u θ => g (X u θ)) := fun O hO u θ => by
  change g (X (O.mulVec u) θ) = g (X u (rotP O θ))
  rw [hX O hO u θ]

/-- A function of `|h(u)|²` is exchangeable. -/
lemma exch_normSq (g : ℝ → ℝ) :
    Exch (fun (u : Fin N → ℝ) (θ : HidParam N m) => g (normSq (hid2 θ.1 θ.2 u))) :=
  fun O _ u θ => by
    change g (normSq (hid2 θ.1 θ.2 (O.mulVec u))) = _
    rw [hid2_exchange]

/-- **Lemma E, the distribution**: for an exchangeable `X`, the distribution of `X(u; ·)` over
`θ` is the same for every unit vector `u`. -/
theorem exch_map (hN : 1 ≤ N) {X : (Fin N → ℝ) → HidParam N m → ℝ} (hX : Exch X)
    {u u0 : Fin N → ℝ} (hu : normSq u = 1) (hu0 : normSq u0 = 1) (hm : Measurable (X u0)) :
    (hidGauss N m).map (X u) = (hidGauss N m).map (X u0) := by
  obtain ⟨O, hO, hOu⟩ := exists_orth_map hN hu hu0
  have e : X u = X u0 ∘ rotP O := by
    funext θ
    rw [← hOu]
    exact hX O hO u0 θ
  rw [e, ← Measure.map_map hm (measurable_rotP O), hidGauss_rot O hO]

/-- The mean over `θ` of an exchangeable `X` is the same at every unit vector. -/
theorem exch_integral (hN : 1 ≤ N) {X : (Fin N → ℝ) → HidParam N m → ℝ} (hX : Exch X)
    {u u0 : Fin N → ℝ} (hu : normSq u = 1) (hu0 : normSq u0 = 1) (hm : Measurable (X u0)) :
    ∫ θ, X u θ ∂hidGauss N m = ∫ θ, X u0 θ ∂hidGauss N m := by
  obtain ⟨O, hO, hOu⟩ := exists_orth_map hN hu hu0
  have e : X u = fun θ => X u0 (rotP O θ) := by
    funext θ
    rw [← hOu]
    exact hX O hO u0 θ
  have h := integral_map (μ := hidGauss N m) (measurable_rotP O).aemeasurable
    (f := X u0) hm.aestronglyMeasurable
  rw [hidGauss_rot O hO] at h
  rw [e, h]

/-- Integrability over `θ` of an exchangeable `X` is the same at every unit vector. -/
theorem exch_integrable (hN : 1 ≤ N) {X : (Fin N → ℝ) → HidParam N m → ℝ} (hX : Exch X)
    {u u0 : Fin N → ℝ} (hu : normSq u = 1) (hu0 : normSq u0 = 1) (hm : Measurable (X u0))
    (hi : Integrable (X u0) (hidGauss N m)) : Integrable (X u) (hidGauss N m) := by
  obtain ⟨O, hO, hOu⟩ := exists_orth_map hN hu hu0
  have e : X u = X u0 ∘ rotP O := by
    funext θ
    rw [← hOu]
    exact hX O hO u0 θ
  rw [e]
  have h := (integrable_map_measure (μ := hidGauss N m) (f := rotP O) (g := X u0)
    (by rw [hidGauss_rot O hO]; exact hm.aestronglyMeasurable)
    (measurable_rotP O).aemeasurable)
  rw [hidGauss_rot O hO] at h
  exact h.1 hi

/-- For an exchangeable `X` such that `X(u₀; ·)` is integrable: `X` is integrable over
`(u, θ)`, and its mean over `(u, θ)` is its mean over `θ` at `u₀`. -/
theorem exch_avg (hN : 1 ≤ N) {X : (Fin N → ℝ) → HidParam N m → ℝ}
    (hXm : Measurable (Function.uncurry X)) (hX : Exch X) {u0 : Fin N → ℝ}
    (hu0 : normSq u0 = 1) (hi : Integrable (X u0) (hidGauss N m)) :
    Integrable (Function.uncurry X) ((uniformSphere N).prod (hidGauss N m)) ∧
      ∫ p, X p.1 p.2 ∂((uniformSphere N).prod (hidGauss N m)) = ∫ θ, X u0 θ ∂hidGauss N m := by
  have := uniformSphere_isProbability N hN
  have hm0 : Measurable (X u0) := hXm.of_uncurry_left
  -- the absolute value is exchangeable too
  have hXa : Exch (fun u θ => ‖X u θ‖) := hX.comp fun x => ‖x‖
  have hma : Measurable (fun θ => ‖X u0 θ‖) := hm0.norm
  have hint : Integrable (Function.uncurry X) ((uniformSphere N).prod (hidGauss N m)) := by
    rw [integrable_prod_iff hXm.aestronglyMeasurable]
    constructor
    · filter_upwards [uniformSphere_ae_sphere N] with u hu
      exact exch_integrable hN hX hu hu0 hm0 hi
    · refine (integrable_const (∫ θ, ‖X u0 θ‖ ∂hidGauss N m)).congr ?_
      filter_upwards [uniformSphere_ae_sphere N] with u hu
      exact (exch_integral hN hXa hu hu0 hma).symm
  refine ⟨hint, ?_⟩
  have h1 : ∫ p, X p.1 p.2 ∂((uniformSphere N).prod (hidGauss N m)) =
      ∫ u, (∫ θ, X u θ ∂hidGauss N m) ∂uniformSphere N := integral_prod _ hint
  rw [h1]
  have h2 : (fun u => ∫ θ, X u θ ∂hidGauss N m) =ᵐ[uniformSphere N]
      fun _ => ∫ θ, X u0 θ ∂hidGauss N m := by
    filter_upwards [uniformSphere_ae_sphere N] with u hu
    exact exch_integral hN hX hu hu0 hm0
  rw [integral_congr_ae h2, integral_const]
  simp

/-- The converse direction: for an exchangeable `X` that is integrable over `(u, θ)`, `X(u₀; ·)`
is integrable at every unit vector `u₀`, with the same mean. -/
theorem exch_pt (hN : 1 ≤ N) {X : (Fin N → ℝ) → HidParam N m → ℝ}
    (hXm : Measurable (Function.uncurry X)) (hX : Exch X) {u0 : Fin N → ℝ}
    (hu0 : normSq u0 = 1)
    (hint : Integrable (Function.uncurry X) ((uniformSphere N).prod (hidGauss N m))) :
    Integrable (X u0) (hidGauss N m) ∧
      ∫ θ, X u0 θ ∂hidGauss N m = ∫ p, X p.1 p.2 ∂((uniformSphere N).prod (hidGauss N m)) := by
  have := uniformSphere_isProbability N hN
  obtain ⟨u1, hi1, hu1⟩ := (hint.prod_right_ae.and (uniformSphere_ae_sphere N)).exists
  have hi0 : Integrable (X u0) (hidGauss N m) :=
    exch_integrable hN hX hu0 hu1 hXm.of_uncurry_left hi1
  exact ⟨hi0, (exch_avg hN hXm hX hu0 hi0).2.symm⟩

/-- `Var f ≤ E (f − c)²` for every constant `c`. -/
lemma variance_le_sq_sub {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {c : ℝ} (hf : AEStronglyMeasurable f μ)
    (hi : Integrable (fun ω => (f ω - c) ^ 2) μ) : Var[f; μ] ≤ ∫ ω, (f ω - c) ^ 2 ∂μ := by
  have h0 : 0 ≤ ∫ ω, (f ω - c) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hL : L2le μ (fun ω => f ω - c) (√(∫ ω, (f ω - c) ^ 2 ∂μ)) :=
    ⟨hf.sub aestronglyMeasurable_const, hi, by rw [Real.sq_sqrt h0]⟩
  have := variance_le_of_L2le hL
  rwa [Real.sq_sqrt h0] at this

/-- **Lemma E, the inequality, with a free centre**: for an exchangeable `X`, a unit vector `u₀`
and every constant `c`: `E_θ Var_u X(u; θ) ≤ E_θ (X(u₀; θ) − c)²`, `u` uniform on the sphere. -/
theorem exchange137 (hN : 1 ≤ N) {X : (Fin N → ℝ) → HidParam N m → ℝ}
    (hXm : Measurable (Function.uncurry X)) (hX : Exch X) {u0 : Fin N → ℝ}
    (hu0 : normSq u0 = 1) {c : ℝ}
    (hi : Integrable (fun θ => (X u0 θ - c) ^ 2) (hidGauss N m)) :
    ∫ θ, Var[fun u => X u θ; uniformSphere N] ∂hidGauss N m ≤
      ∫ θ, (X u0 θ - c) ^ 2 ∂hidGauss N m := by
  have := uniformSphere_isProbability N hN
  have hYm : Measurable (Function.uncurry fun u θ => (X u θ - c) ^ 2) :=
    (hXm.sub_const c).pow_const 2
  have hY : Exch (fun u θ => (X u θ - c) ^ 2) := hX.comp fun x => (x - c) ^ 2
  obtain ⟨hint, hval⟩ := exch_avg hN hYm hY hu0 hi
  have hsw : ∫ p, (X p.1 p.2 - c) ^ 2 ∂((uniformSphere N).prod (hidGauss N m)) =
      ∫ θ, (∫ u, (X u θ - c) ^ 2 ∂uniformSphere N) ∂hidGauss N m := integral_prod_symm _ hint
  rw [← hval, hsw]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => variance_nonneg _ _)
    hint.integral_prod_right ?_
  filter_upwards [hint.prod_left_ae] with θ hθ
  exact variance_le_sq_sub (hXm.of_uncurry_right (y := θ)).aestronglyMeasurable hθ

/-- The variance over the input is a measurable function of `θ`. -/
lemma measurable_var_u (hN : 1 ≤ N) {X : (Fin N → ℝ) → HidParam N m → ℝ}
    (hXm : Measurable (Function.uncurry X)) :
    Measurable (fun θ : HidParam N m => Var[fun u => X u θ; uniformSphere N]) := by
  have := uniformSphere_isProbability N hN
  have hmean : Measurable (fun θ : HidParam N m => ∫ u, X u θ ∂uniformSphere N) :=
    (hXm.stronglyMeasurable.integral_prod_left').measurable
  have hF : Measurable (fun p : (Fin N → ℝ) × HidParam N m =>
      ‖X p.1 p.2 - ∫ u, X u p.2 ∂uniformSphere N‖ₑ ^ 2) :=
    ((hXm.sub (hmean.comp measurable_snd)).enorm).pow_const 2
  have h := hF.lintegral_prod_left' (μ := uniformSphere N)
  unfold variance evariance
  exact h.ennreal_toReal

/-- **Lemma E, integrability**: under the hypotheses of `exchange137`, `θ ↦ Var_u X(u; θ)` is
integrable (so `E_θ Var_u X` in `exchange137` is the integral of an integrable function). -/
theorem exchange137_integrable (hN : 1 ≤ N) {X : (Fin N → ℝ) → HidParam N m → ℝ}
    (hXm : Measurable (Function.uncurry X)) (hX : Exch X) {u0 : Fin N → ℝ}
    (hu0 : normSq u0 = 1) {c : ℝ}
    (hi : Integrable (fun θ => (X u0 θ - c) ^ 2) (hidGauss N m)) :
    Integrable (fun θ => Var[fun u => X u θ; uniformSphere N]) (hidGauss N m) := by
  have := uniformSphere_isProbability N hN
  have hYm : Measurable (Function.uncurry fun u θ => (X u θ - c) ^ 2) :=
    (hXm.sub_const c).pow_const 2
  have hY : Exch (fun u θ => (X u θ - c) ^ 2) := hX.comp fun x => (x - c) ^ 2
  obtain ⟨hint, -⟩ := exch_avg hN hYm hY hu0 hi
  refine Integrable.mono' hint.integral_prod_right
    (measurable_var_u hN hXm).aestronglyMeasurable ?_
  filter_upwards [hint.prod_left_ae] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (variance_nonneg _ _)]
  exact variance_le_sq_sub (hXm.of_uncurry_right (y := θ)).aestronglyMeasurable hθ

/-- **Lemma E, the inequality** (`onW16c-cx.md` §1): for an exchangeable `X` with
`E_θ X(u₀)² < ∞`: `E_θ Var_u X(u; θ) ≤ Var_θ X(u₀; θ)`. -/
theorem exchange137_var (hN : 1 ≤ N) {X : (Fin N → ℝ) → HidParam N m → ℝ}
    (hXm : Measurable (Function.uncurry X)) (hX : Exch X) {u0 : Fin N → ℝ}
    (hu0 : normSq u0 = 1) (h2 : MemLp (X u0) 2 (hidGauss N m)) :
    ∫ θ, Var[fun u => X u θ; uniformSphere N] ∂hidGauss N m ≤ Var[X u0; hidGauss N m] := by
  have hm0 : Measurable (X u0) := hXm.of_uncurry_left
  rw [variance_eq_integral hm0.aemeasurable]
  exact exchange137 hN hXm hX hu0 (h2.sub (memLp_const _)).integrable_sq

end BstLean.Part137
