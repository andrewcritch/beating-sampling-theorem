import BstLean.Part137Exchange

/-!
# Part 137, item 2: Lemma H2(a), the fluctuation of the squared length of the hidden vector

Role: `delegations/statements/p137-spec.md`. Paper source: `onW16c-cx.md` §2 (H2(a)).

`N` inputs, hidden width `m`, `t = 2/m`, `γ = 2/N`, `θ = (M₁, M₂)` with distribution
`hidGauss N m`, `h(u) = hid2 M₁ M₂ u`.

* `hid2_sq_moment`: `E_θ |h(u)|² = (m/N)|u|²`; `hid2_four_moment`:
  `E_θ |h(u)|⁴ = (m/N)²(1 + 5/m)²|u|⁴`.
* `Dn N m u θ = t|h(u)|²/γ`.
* `normFluct137_pt`: for a unit vector `u₀`: `E_θ (D(u₀) − 1)² = 10/m + 25/m²`.
* `normFluct137_var`: `Var_θ D(u₀) = 10/m + 25/m²`; `Dn_mean`: `E_θ D(u₀) = 1`.
* `normFluct137_joint`: `E_θ E_u (D(u) − 1)² = 10/m + 25/m²`.
* `normFluct137`: `E_θ Var_u D ≤ 10/m + 25/m²`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part137

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part73 (IsOrth uniformSphere_orth)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136

variable {N m : ℕ}

lemma continuous_normSq_hid2 (u : Fin N → ℝ) :
    Continuous (fun θ : HidParam N m => normSq (hid2 θ.1 θ.2 u)) :=
  continuous_normSq.comp (continuous_hid2_joint.comp (continuous_id.prodMk continuous_const))

/-- `E_θ |h(u)|² = (m/N)|u|²`. -/
theorem hid2_sq_moment (hN : 1 ≤ N) (hm : 1 ≤ m) (u : Fin N → ℝ) :
    Integrable (fun θ : HidParam N m => normSq (hid2 θ.1 θ.2 u)) (hidGauss N m) ∧
      ∫ θ, normSq (hid2 θ.1 θ.2 u) ∂hidGauss N m = (m : ℝ) / N * normSq u := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  have step := prod_step (μ := gaussMat m N (2 / (N : ℝ))) (ν := gaussMat m m (2 / (m : ℝ)))
    (f := fun θ : HidParam N m => normSq (hid2 θ.1 θ.2 u)) (continuous_normSq_hid2 u).measurable
    (fun p => normSq_nonneg _)
    (fun M₁ => (m : ℝ) / 2 * (2 / (m : ℝ) * normSq (reluV (M₁.mulVec u))))
    (fun M₁ => layer_relu_sq (m := m) h2 (reluV (M₁.mulVec u)))
    (((layer_relu_sq (m := m) h1 u).1.const_mul _).const_mul _)
  refine ⟨step.1, ?_⟩
  have e := step.2
  rw [integral_const_mul, integral_const_mul, (layer_relu_sq (m := m) h1 u).2] at e
  unfold hidGauss
  rw [e]
  field_simp

/-- `E_θ |h(u)|⁴ = (m/N)²(1 + 5/m)²|u|⁴`. -/
theorem hid2_four_moment (hN : 1 ≤ N) (hm : 1 ≤ m) (u : Fin N → ℝ) :
    Integrable (fun θ : HidParam N m => normSq (hid2 θ.1 θ.2 u) ^ 2) (hidGauss N m) ∧
      ∫ θ, normSq (hid2 θ.1 θ.2 u) ^ 2 ∂hidGauss N m =
        ((m : ℝ) / N) ^ 2 * (1 + 5 / (m : ℝ)) ^ 2 * normSq u ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  have step := prod_step (μ := gaussMat m N (2 / (N : ℝ))) (ν := gaussMat m m (2 / (m : ℝ)))
    (f := fun θ : HidParam N m => normSq (hid2 θ.1 θ.2 u) ^ 2)
    ((continuous_normSq_hid2 u).pow 2).measurable
    (fun p => sq_nonneg _)
    (fun M₁ => ((m : ℝ) ^ 2 / 4 + 5 * m / 4) *
      (2 / (m : ℝ) * normSq (reluV (M₁.mulVec u))) ^ 2)
    (fun M₁ => layer_relu_four (m := m) h2 (reluV (M₁.mulVec u)))
    (by
      have := ((layer_relu_four (m := m) h1 u).1.const_mul ((2 / (m : ℝ)) ^ 2)).const_mul
        ((m : ℝ) ^ 2 / 4 + 5 * m / 4)
      refine this.congr (Filter.Eventually.of_forall fun M₁ => ?_)
      simp only [mul_pow])
  refine ⟨step.1, ?_⟩
  have e := step.2
  have e2 : (fun M₁ : Matrix (Fin m) (Fin N) ℝ => ((m : ℝ) ^ 2 / 4 + 5 * m / 4) *
      (2 / (m : ℝ) * normSq (reluV (M₁.mulVec u))) ^ 2) =
      fun M₁ => ((m : ℝ) ^ 2 / 4 + 5 * m / 4) * ((2 / (m : ℝ)) ^ 2 *
        normSq (reluV (M₁.mulVec u)) ^ 2) := by
    funext M₁
    rw [mul_pow]
  rw [e2, integral_const_mul, integral_const_mul, (layer_relu_four (m := m) h1 u).2] at e
  unfold hidGauss
  rw [e]
  field_simp
  ring

/-- **`D(u) = t|h(u)|²/γ`**, `t = 2/m`, `γ = 2/N`: the squared length of the hidden vector
relative to its mean. -/
noncomputable def Dn (N m : ℕ) (u : Fin N → ℝ) (θ : HidParam N m) : ℝ :=
  2 / (m : ℝ) * normSq (hid2 θ.1 θ.2 u) / (2 / (N : ℝ))

lemma Dn_eq (N m : ℕ) (u : Fin N → ℝ) (θ : HidParam N m) :
    Dn N m u θ = (N : ℝ) / m * normSq (hid2 θ.1 θ.2 u) := by
  unfold Dn
  rw [div_div_eq_mul_div]
  ring

lemma continuous_Dn : Continuous (Function.uncurry (Dn N m)) := by
  have h1 : Continuous (fun z : (Fin N → ℝ) × HidParam N m => hid2 z.2.1 z.2.2 z.1) :=
    continuous_hid2_joint.comp (continuous_snd.prodMk continuous_fst)
  have : Function.uncurry (Dn N m) = fun z : (Fin N → ℝ) × HidParam N m =>
      2 / (m : ℝ) * normSq (hid2 z.2.1 z.2.2 z.1) / (2 / (N : ℝ)) := by
    funext z
    rfl
  rw [this]
  exact (continuous_const.mul (continuous_normSq.comp h1)).div_const _

lemma exch_Dn : Exch (Dn N m) :=
  exch_normSq fun x => 2 / (m : ℝ) * x / (2 / (N : ℝ))

/-- `E_θ D(u₀) = 1` for a unit vector `u₀`. -/
theorem Dn_mean (hN : 1 ≤ N) (hm : 1 ≤ m) {u0 : Fin N → ℝ} (hu0 : normSq u0 = 1) :
    Integrable (Dn N m u0) (hidGauss N m) ∧ ∫ θ, Dn N m u0 θ ∂hidGauss N m = 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hi, hv⟩ := hid2_sq_moment (m := m) hN hm u0
  have e : Dn N m u0 = fun θ => (N : ℝ) / m * normSq (hid2 θ.1 θ.2 u0) := funext (Dn_eq N m u0)
  rw [e]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul, hv, hu0]
  field_simp

/-- **Lemma H2(a)** (`onW16c-cx.md` §2): for a unit vector `u₀`,
`E_θ (D(u₀) − 1)² = 10/m + 25/m²`. -/
theorem normFluct137_pt (hN : 1 ≤ N) (hm : 1 ≤ m) {u0 : Fin N → ℝ} (hu0 : normSq u0 = 1) :
    Integrable (fun θ => (Dn N m u0 θ - 1) ^ 2) (hidGauss N m) ∧
      ∫ θ, (Dn N m u0 θ - 1) ^ 2 ∂hidGauss N m = 10 / (m : ℝ) + 25 / (m : ℝ) ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hi2, hv2⟩ := hid2_sq_moment (m := m) hN hm u0
  obtain ⟨hi4, hv4⟩ := hid2_four_moment (m := m) hN hm u0
  have e : (fun θ : HidParam N m => (Dn N m u0 θ - 1) ^ 2) = fun θ =>
      ((N : ℝ) / m) ^ 2 * normSq (hid2 θ.1 θ.2 u0) ^ 2 -
        2 * ((N : ℝ) / m) * normSq (hid2 θ.1 θ.2 u0) + 1 := by
    funext θ
    rw [Dn_eq]
    ring
  have iA : Integrable (fun θ : HidParam N m => ((N : ℝ) / m) ^ 2 *
      normSq (hid2 θ.1 θ.2 u0) ^ 2) (hidGauss N m) := hi4.const_mul _
  have iB : Integrable (fun θ : HidParam N m => 2 * ((N : ℝ) / m) *
      normSq (hid2 θ.1 θ.2 u0)) (hidGauss N m) := hi2.const_mul _
  rw [e]
  refine ⟨(iA.sub iB).add (integrable_const _), ?_⟩
  have s1 : ∫ θ : HidParam N m, (((N : ℝ) / m) ^ 2 * normSq (hid2 θ.1 θ.2 u0) ^ 2 -
      2 * ((N : ℝ) / m) * normSq (hid2 θ.1 θ.2 u0) + 1) ∂hidGauss N m =
      ∫ θ : HidParam N m, (((N : ℝ) / m) ^ 2 * normSq (hid2 θ.1 θ.2 u0) ^ 2 -
      2 * ((N : ℝ) / m) * normSq (hid2 θ.1 θ.2 u0)) ∂hidGauss N m + ∫ _θ : HidParam N m, (1 : ℝ)
        ∂hidGauss N m := integral_add (iA.sub iB) (integrable_const _)
  have s2 : ∫ θ : HidParam N m, (((N : ℝ) / m) ^ 2 * normSq (hid2 θ.1 θ.2 u0) ^ 2 -
      2 * ((N : ℝ) / m) * normSq (hid2 θ.1 θ.2 u0)) ∂hidGauss N m =
      ∫ θ : HidParam N m, ((N : ℝ) / m) ^ 2 * normSq (hid2 θ.1 θ.2 u0) ^ 2 ∂hidGauss N m -
      ∫ θ : HidParam N m, 2 * ((N : ℝ) / m) * normSq (hid2 θ.1 θ.2 u0) ∂hidGauss N m :=
    integral_sub iA iB
  rw [s1, s2, integral_const_mul, integral_const_mul, hv2, hv4, hu0]
  simp only [integral_const, probReal_univ, smul_eq_mul]
  field_simp
  ring

/-- **Lemma H2(a), the variance**: `Var_θ D(u₀) = 10/m + 25/m²`. -/
theorem normFluct137_var (hN : 1 ≤ N) (hm : 1 ≤ m) {u0 : Fin N → ℝ} (hu0 : normSq u0 = 1) :
    Var[Dn N m u0; hidGauss N m] = 10 / (m : ℝ) + 25 / (m : ℝ) ^ 2 := by
  have hmeas : Measurable (Dn N m u0) := continuous_Dn.measurable.of_uncurry_left
  rw [variance_eq_integral hmeas.aemeasurable, (Dn_mean hN hm hu0).2]
  exact (normFluct137_pt hN hm hu0).2

/-- **Lemma H2(a), over the input and `θ`**: `E_θ E_u (D(u) − 1)² = 10/m + 25/m²`. -/
theorem normFluct137_joint (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (fun p : (Fin N → ℝ) × HidParam N m => (Dn N m p.1 p.2 - 1) ^ 2)
        ((uniformSphere N).prod (hidGauss N m)) ∧
      ∫ p, (Dn N m p.1 p.2 - 1) ^ 2 ∂((uniformSphere N).prod (hidGauss N m)) =
        10 / (m : ℝ) + 25 / (m : ℝ) ^ 2 := by
  have h0 : normSq (e0 N) = 1 := by
    have := normSq_sphPt hN (0 : Fin N → ℝ)
    simpa [sphPt, normSq] using this
  have hYm : Measurable (Function.uncurry fun u θ => (Dn N m u θ - 1) ^ 2) :=
    ((continuous_Dn.measurable).sub_const 1).pow_const 2
  have hY : Exch (fun u θ => (Dn N m u θ - 1) ^ 2) := exch_Dn.comp fun x => (x - 1) ^ 2
  obtain ⟨h1, h2⟩ := exch_avg hN hYm hY h0 (normFluct137_pt hN hm h0).1
  exact ⟨h1, h2.trans (normFluct137_pt hN hm h0).2⟩

/-- **Lemma H2(a), the consequence** (`onW16c-cx.md` §§1, 2): `E_θ Var_u D ≤ 10/m + 25/m²`,
`u` uniform on the unit sphere of `ℝ^N`. -/
theorem normFluct137 (hN : 1 ≤ N) (hm : 1 ≤ m) :
    ∫ θ, Var[fun u => Dn N m u θ; uniformSphere N] ∂hidGauss N m ≤
      10 / (m : ℝ) + 25 / (m : ℝ) ^ 2 := by
  have h0 : normSq (e0 N) = 1 := by
    have := normSq_sphPt hN (0 : Fin N → ℝ)
    simpa [sphPt, normSq] using this
  have h := exchange137 hN continuous_Dn.measurable exch_Dn h0 (c := 1)
    (normFluct137_pt hN hm h0).1
  rwa [(normFluct137_pt hN hm h0).2] at h

/-- `θ ↦ Var_u D(u; θ)` is integrable. -/
theorem normFluct137_integrable (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (fun θ => Var[fun u => Dn N m u θ; uniformSphere N]) (hidGauss N m) := by
  have h0 : normSq (e0 N) = 1 := by
    have := normSq_sphPt hN (0 : Fin N → ℝ)
    simpa [sphPt, normSq] using this
  exact exchange137_integrable hN continuous_Dn.measurable exch_Dn h0 (c := 1)
    (normFluct137_pt hN hm h0).1

/-- `normFluct137` for the World network of the Focus: `N = 2n`, `m = mW n = ⌈n^{7/2}⌉`. -/
theorem normFluct137_focus {n : ℕ} (hn : 1 ≤ n) :
    ∫ θ, Var[fun u => Dn (2 * n) (mW n) u θ; uniformSphere (2 * n)] ∂hidGauss (2 * n) (mW n) ≤
      10 / (mW n : ℝ) + 25 / (mW n : ℝ) ^ 2 :=
  normFluct137 (by omega) (one_le_mW hn)

end BstLean.Part137
