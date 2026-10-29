import BstLean.Part137Norm

/-!
# Part 137, item 3: Lemma H2(d), the fluctuation of the inner product with the centre `h̄`

Role: `delegations/statements/p137-spec.md`. Paper source: `onW16c-cx.md` §2 (H2(d)).

`N` inputs, hidden width `m`, `t = 2/m`, `γ = 2/N`, `θ = (M₁, M₂)` with distribution
`hidGauss N m`, `h(u) = hid2 M₁ M₂ u`, `h̄ = hbarW θ = E_u h(u)` (the centre of Parts 134, 136).

* `Tn N m u θ = t⟨h(u), h̄⟩`.
* `qN N = E_{u′} κ(κ(⟨e₀, u′⟩))`; `qN_eq`: the same value at every unit vector.
* `hbarW_rot`: `h̄(M₁ O, M₂) = h̄(M₁, M₂)` for an orthogonal `O`; `exch_Tn`: `T` is exchangeable.
* `Tn_sub`: `T(u) − γ q_N = t E_{u′}(G_θ(u, u′) − (m/N) κ(κ(⟨u, u′⟩)))`.
* `innerFluct137_pt`: for a unit vector `u₀`: `E_θ (T(u₀) − γ q_N)² ≤ (γ·cF2o m)²`.
* `innerFluct137_gen`: `E_θ Var_u T ≤ (γ·cF2o m)²`, every `N, m ≥ 1`.
* `innerFluct137`, `innerFluct137_pt_focus`: `N = 2n`, `m = mW n`, `n ≥ 4096`: the bound
  `22.35·γ²/m`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part137

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part73 (IsOrth uniformSphere_orth)
open BstLean.Part80 (dot_mulVec')
open BstLean.Part105 (sphere_cont_integrable)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136

variable {N m : ℕ}

/-- **`T(u) = t⟨h(u), h̄⟩`**, `t = 2/m`, `h̄ = E_u h(u)`. -/
noncomputable def Tn (N m : ℕ) (u : Fin N → ℝ) (θ : HidParam N m) : ℝ :=
  2 / (m : ℝ) * dotp (hid2 θ.1 θ.2 u) (hbarW θ)

/-- **`q_N = E_{u′} κ(κ(⟨u₀, u′⟩))`**, written at the fixed unit vector `e₀`. -/
noncomputable def qN (N : ℕ) : ℝ := ∫ u', kappa (kappa (dotp (e0 N) u')) ∂uniformSphere N

lemma normSq_e0 (hN : 1 ≤ N) : normSq (e0 N) = 1 := by
  have := normSq_sphPt hN (0 : Fin N → ℝ)
  simpa [sphPt, normSq] using this

lemma continuous_hid2_u (θ : HidParam N m) : Continuous (fun u => hid2 θ.1 θ.2 u) :=
  continuous_hid2_joint.comp (continuous_const.prodMk continuous_id)

lemma continuous_hid2_coord (θ : HidParam N m) (j : Fin m) :
    Continuous (fun u => hid2 θ.1 θ.2 u j) :=
  (continuous_apply j).comp (continuous_hid2_u θ)

/-- The centre `h̄` does not change under `M₁ ↦ M₁ O`, `O` orthogonal. -/
theorem hbarW_rot (O : Matrix (Fin N) (Fin N) ℝ) (hO : IsOrth O) (θ : HidParam N m) :
    hbarW (rotP O θ) = hbarW θ := by
  funext j
  unfold hbarW hbar
  have hc := continuous_hid2_coord θ j
  have hmO : Measurable (fun u : Fin N → ℝ => O.mulVec u) := by fun_prop
  have h := integral_map (μ := uniformSphere N) hmO.aemeasurable
    (f := fun u => hid2 θ.1 θ.2 u j) hc.aestronglyMeasurable
  rw [uniformSphere_orth O hO] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  change hid2 (rotP O θ).1 (rotP O θ).2 u j = hid2 θ.1 θ.2 (O.mulVec u) j
  rw [hid2_exchange]

/-- `T` is exchangeable. -/
theorem exch_Tn : Exch (Tn N m) := fun O hO u θ => by
  change 2 / (m : ℝ) * dotp (hid2 θ.1 θ.2 (O.mulVec u)) (hbarW θ) =
    2 / (m : ℝ) * dotp (hid2 (rotP O θ).1 (rotP O θ).2 u) (hbarW (rotP O θ))
  rw [hbarW_rot O hO, hid2_exchange]

lemma measurable_Tn (hN : 1 ≤ N) : Measurable (Function.uncurry (Tn N m)) := by
  have h1 : Measurable (fun z : (Fin N → ℝ) × HidParam N m => hid2 z.2.1 z.2.2 z.1) :=
    (continuous_hid2_joint.comp (continuous_snd.prodMk continuous_fst)).measurable
  have h2 : Measurable (fun z : (Fin N → ℝ) × HidParam N m => hbarW z.2) :=
    (measurable_hbarW hN).comp measurable_snd
  have : Function.uncurry (Tn N m) = fun z : (Fin N → ℝ) × HidParam N m =>
      2 / (m : ℝ) * dotp (hid2 z.2.1 z.2.2 z.1) (hbarW z.2) := by
    funext z
    rfl
  rw [this]
  exact (continuous_dotp.measurable.comp (h1.prodMk h2)).const_mul _

lemma continuous_Tn_u (θ : HidParam N m) : Continuous (fun u => Tn N m u θ) :=
  continuous_const.mul (continuous_dotp.comp ((continuous_hid2_u θ).prodMk continuous_const))

lemma dotp_comm' {ι : Type*} [Fintype ι] (a b : ι → ℝ) : dotp a b = dotp b a := by
  unfold dotp
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- `E_{u′} κ(κ(⟨u, u′⟩)) = q_N` at every unit vector `u`. -/
theorem qN_eq (hN : 1 ≤ N) {u : Fin N → ℝ} (hu : normSq u = 1) :
    ∫ u', kappa (kappa (dotp u u')) ∂uniformSphere N = qN N := by
  obtain ⟨O, hO, hOu⟩ := exists_orth_map hN hu (normSq_e0 hN)
  have hmO : Measurable (fun u : Fin N → ℝ => O.transpose.mulVec u) := by fun_prop
  have hc : Continuous (fun y : Fin N → ℝ => kappa (kappa (dotp (e0 N) y))) :=
    continuous_kappa.comp (continuous_kappa.comp
      (continuous_dotp.comp (continuous_const.prodMk continuous_id)))
  have h := integral_map (μ := uniformSphere N) hmO.aemeasurable
    (f := fun y => kappa (kappa (dotp (e0 N) y))) hc.aestronglyMeasurable
  rw [uniformSphere_orth O.transpose hO.t] at h
  unfold qN
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u' => ?_)
  have e : dotp u u' = dotp (e0 N) (O.transpose.mulVec u') := by
    rw [← hOu, dotp_comm' (O.mulVec (e0 N)) u', dotp_comm' (e0 N)]
    exact dot_mulVec' O u' (e0 N)
  change kappa (kappa (dotp u u')) = kappa (kappa (dotp (e0 N) (O.transpose.mulVec u')))
  rw [e]

lemma continuous_fK_u (u : Fin N → ℝ) (θ : HidParam N m) :
    Continuous (fun u' : Fin N → ℝ => fK N m ((u, u'), θ)) :=
  continuous_fK.comp ((continuous_const.prodMk continuous_id).prodMk continuous_const)

/-- `⟨h(u), h̄⟩ = E_{u′}⟨h(u), h(u′)⟩`. -/
lemma dotp_hbar (hN : 1 ≤ N) (u : Fin N → ℝ) (θ : HidParam N m) :
    dotp (hid2 θ.1 θ.2 u) (hbarW θ) =
      ∫ u', dotp (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') ∂uniformSphere N := by
  unfold dotp
  rw [integral_finsetSum _ fun j _ =>
    (sphere_cont_integrable hN (continuous_hid2_coord θ j)).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  rfl

/-- **The inner product as a mean of the Gram kernel error**: for a unit vector `u`,
`T(u) − γ q_N = t·E_{u′}(⟨h(u), h(u′)⟩ − (m/N)·κ(κ(⟨u, u′⟩)))`. -/
theorem Tn_sub (hN : 1 ≤ N) (hm : 1 ≤ m) {u : Fin N → ℝ} (hu : normSq u = 1)
    (θ : HidParam N m) :
    Tn N m u θ - 2 / (N : ℝ) * qN N =
      2 / (m : ℝ) * ∫ u', fK N m ((u, u'), θ) ∂uniformSphere N := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have := uniformSphere_isProbability N hN
  have i1 : Integrable (fun u' => dotp (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')) (uniformSphere N) :=
    sphere_cont_integrable hN
      (continuous_dotp.comp (continuous_const.prodMk (continuous_hid2_u θ)))
  have i2 : Integrable (fun u' => (m : ℝ) / N * kappa (kappa (dotp u u'))) (uniformSphere N) :=
    sphere_cont_integrable hN (continuous_const.mul (continuous_kappa.comp
      (continuous_kappa.comp (continuous_dotp.comp (continuous_const.prodMk continuous_id)))))
  have e : ∫ u', fK N m ((u, u'), θ) ∂uniformSphere N =
      dotp (hid2 θ.1 θ.2 u) (hbarW θ) - (m : ℝ) / N * qN N := by
    have : (fun u' => fK N m ((u, u'), θ)) = fun u' =>
        dotp (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') - (m : ℝ) / N * kappa (kappa (dotp u u')) := by
      funext u'
      rfl
    rw [this, integral_sub i1 i2, integral_const_mul, qN_eq hN hu, dotp_hbar hN]
  rw [e]
  unfold Tn
  field_simp

/-- For every `θ`: `E_u (T(u) − γ q_N)² ≤ t²·errK θ`. -/
theorem Tn_err (hN : 1 ≤ N) (hm : 1 ≤ m) (θ : HidParam N m) :
    ∫ u, (Tn N m u θ - 2 / (N : ℝ) * qN N) ^ 2 ∂uniformSphere N ≤
      (2 / (m : ℝ)) ^ 2 * errK θ := by
  have := uniformSphere_isProbability N hN
  have hK2 : Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => fK N m (uu, θ) ^ 2) (lawU2 N) :=
    lawU2_cont_integrable hN ((continuous_fK.comp (continuous_id.prodMk continuous_const)).pow 2)
  have hK2' : Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => fK N m (uu, θ) ^ 2)
      ((uniformSphere N).prod (uniformSphere N)) := hK2
  have hE : errK θ = ∫ u, (∫ u', fK N m ((u, u'), θ) ^ 2 ∂uniformSphere N) ∂uniformSphere N := by
    unfold errK lawU2
    exact integral_prod _ hK2'
  rw [hE, ← integral_const_mul]
  refine integral_mono_ae
    (sphere_cont_integrable hN (((continuous_Tn_u θ).sub continuous_const).pow 2))
    (hK2'.integral_prod_left.const_mul _) ?_
  filter_upwards [uniformSphere_ae_sphere N] with u hu
  have hu' : normSq u = 1 := hu
  have h1 := sq_integral_le (ρ := uniformSphere N) (f := fun u' => fK N m ((u, u'), θ))
    (sphere_cont_integrable hN ((continuous_fK_u u θ).pow 2))
  change (Tn N m u θ - 2 / (N : ℝ) * qN N) ^ 2 ≤
    (2 / (m : ℝ)) ^ 2 * ∫ u', fK N m ((u, u'), θ) ^ 2 ∂uniformSphere N
  rw [Tn_sub hN hm hu', mul_pow]
  exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)

/-- **Lemma H2(d), over the input and `θ`**: `E_θ E_u (T(u) − γ q_N)² ≤ (γ·cF2o m)²`. -/
theorem innerFluct137_joint (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (fun p : (Fin N → ℝ) × HidParam N m => (Tn N m p.1 p.2 - 2 / (N : ℝ) * qN N) ^ 2)
        ((uniformSphere N).prod (hidGauss N m)) ∧
      ∫ p, (Tn N m p.1 p.2 - 2 / (N : ℝ) * qN N) ^ 2 ∂((uniformSphere N).prod (hidGauss N m)) ≤
        (2 / (N : ℝ) * cF2o m) ^ 2 := by
  have := uniformSphere_isProbability N hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hYm : Measurable (fun p : (Fin N → ℝ) × HidParam N m =>
      (Tn N m p.1 p.2 - 2 / (N : ℝ) * qN N) ^ 2) :=
    (((measurable_Tn hN).sub_const _).pow_const 2 :)
  obtain ⟨hEi, hEv⟩ := errK_mean (m := m) hN hm
  have hsec : ∀ θ : HidParam N m, Integrable (fun u => (Tn N m u θ - 2 / (N : ℝ) * qN N) ^ 2)
      (uniformSphere N) := fun θ =>
    sphere_cont_integrable hN (((continuous_Tn_u θ).sub continuous_const).pow 2)
  have hint : Integrable (fun p : (Fin N → ℝ) × HidParam N m =>
      (Tn N m p.1 p.2 - 2 / (N : ℝ) * qN N) ^ 2) ((uniformSphere N).prod (hidGauss N m)) := by
    rw [integrable_prod_iff' hYm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall hsec, ?_⟩
    refine Integrable.mono' (hEi.const_mul ((2 / (m : ℝ)) ^ 2))
      (hYm.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun θ => ?_
    have e : (fun u => ‖(Tn N m u θ - 2 / (N : ℝ) * qN N) ^ 2‖) =
        fun u => (Tn N m u θ - 2 / (N : ℝ) * qN N) ^ 2 := by
      funext u
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), e]
    exact Tn_err hN hm θ
  refine ⟨hint, ?_⟩
  rw [integral_prod_symm _ hint]
  calc ∫ θ, (∫ u, (Tn N m u θ - 2 / (N : ℝ) * qN N) ^ 2 ∂uniformSphere N) ∂hidGauss N m
      ≤ ∫ θ, (2 / (m : ℝ)) ^ 2 * errK θ ∂hidGauss N m :=
        integral_mono hint.integral_prod_right (hEi.const_mul _) fun θ => Tn_err hN hm θ
    _ = (2 / (m : ℝ)) ^ 2 * ∫ θ, errK θ ∂hidGauss N m := integral_const_mul _ _
    _ ≤ (2 / (m : ℝ)) ^ 2 * ((m : ℝ) / N * cF2o m) ^ 2 :=
        mul_le_mul_of_nonneg_left hEv (sq_nonneg _)
    _ = (2 / (N : ℝ) * cF2o m) ^ 2 := by
        field_simp

/-- **Lemma H2(d)** (`onW16c-cx.md` §2), every `N, m ≥ 1`: for a unit vector `u₀`,
`E_θ (T(u₀) − γ q_N)² ≤ (γ·cF2o m)²`. -/
theorem innerFluct137_pt (hN : 1 ≤ N) (hm : 1 ≤ m) {u0 : Fin N → ℝ} (hu0 : normSq u0 = 1) :
    Integrable (fun θ => (Tn N m u0 θ - 2 / (N : ℝ) * qN N) ^ 2) (hidGauss N m) ∧
      ∫ θ, (Tn N m u0 θ - 2 / (N : ℝ) * qN N) ^ 2 ∂hidGauss N m ≤
        (2 / (N : ℝ) * cF2o m) ^ 2 := by
  have hYm : Measurable (Function.uncurry fun (u : Fin N → ℝ) (θ : HidParam N m) =>
      (Tn N m u θ - 2 / (N : ℝ) * qN N) ^ 2) :=
    ((measurable_Tn hN).sub_const _).pow_const 2
  have hY : Exch (fun (u : Fin N → ℝ) (θ : HidParam N m) =>
      (Tn N m u θ - 2 / (N : ℝ) * qN N) ^ 2) :=
    exch_Tn.comp fun x => (x - 2 / (N : ℝ) * qN N) ^ 2
  obtain ⟨hint, hle⟩ := innerFluct137_joint (m := m) hN hm
  obtain ⟨h1, h2⟩ := exch_pt hN hYm hY hu0 hint
  exact ⟨h1, h2.trans_le hle⟩

/-- **Lemma H2(d), the consequence**, every `N, m ≥ 1`: `E_θ Var_u T ≤ (γ·cF2o m)²`. -/
theorem innerFluct137_gen (hN : 1 ≤ N) (hm : 1 ≤ m) :
    ∫ θ, Var[fun u => Tn N m u θ; uniformSphere N] ∂hidGauss N m ≤
      (2 / (N : ℝ) * cF2o m) ^ 2 := by
  obtain ⟨h1, h2⟩ := innerFluct137_pt (m := m) hN hm (normSq_e0 hN)
  exact (exchange137 hN (measurable_Tn hN) exch_Tn (normSq_e0 hN) h1).trans h2

/-- `θ ↦ Var_u T(u; θ)` is integrable. -/
theorem innerFluct137_integrable (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (fun θ => Var[fun u => Tn N m u θ; uniformSphere N]) (hidGauss N m) :=
  exchange137_integrable hN (measurable_Tn hN) exch_Tn (normSq_e0 hN)
    (innerFluct137_pt (m := m) hN hm (normSq_e0 hN)).1

/-- `Var_θ T(u₀) ≤ (γ·cF2o m)²`. -/
theorem innerFluct137_var (hN : 1 ≤ N) (hm : 1 ≤ m) {u0 : Fin N → ℝ} (hu0 : normSq u0 = 1) :
    Var[Tn N m u0; hidGauss N m] ≤ (2 / (N : ℝ) * cF2o m) ^ 2 := by
  obtain ⟨h1, h2⟩ := innerFluct137_pt (m := m) hN hm hu0
  exact (variance_le_sq_sub
    (measurable_Tn hN).of_uncurry_left.aestronglyMeasurable h1).trans h2

lemma gamma_cF2o_le {n : ℕ} (hn : 4096 ≤ n) :
    (2 / ((2 * n : ℕ) : ℝ) * cF2o (mW n)) ^ 2 ≤
      2235 / 100 * (2 / ((2 * n : ℕ) : ℝ)) ^ 2 / (mW n : ℝ) := by
  have h := cF2o_sq_le (mW_ge_million hn)
  have e : 2235 / 100 * (2 / ((2 * n : ℕ) : ℝ)) ^ 2 / (mW n : ℝ) =
      (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * (2235 / 100 / (mW n : ℝ)) := by ring
  rw [mul_pow, e]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- **Lemma H2(d) for the World network of the Focus** (`N = 2n`, `m = mW n`, `n ≥ 4096`):
for a unit vector `u₀`, `E_θ (T(u₀) − γ q_N)² ≤ 22.35·γ²/m`. -/
theorem innerFluct137_pt_focus {n : ℕ} (hn : 4096 ≤ n) {u0 : Fin (2 * n) → ℝ}
    (hu0 : normSq u0 = 1) :
    ∫ θ, (Tn (2 * n) (mW n) u0 θ - 2 / ((2 * n : ℕ) : ℝ) * qN (2 * n)) ^ 2
        ∂hidGauss (2 * n) (mW n) ≤
      2235 / 100 * (2 / ((2 * n : ℕ) : ℝ)) ^ 2 / (mW n : ℝ) :=
  (innerFluct137_pt (by omega) (one_le_mW (by omega)) hu0).2.trans (gamma_cF2o_le hn)

/-- **`innerFluct137`** (Lemma H2(d), the consequence, for the World network of the Focus):
`N = 2n`, `m = mW n`, every `n ≥ 4096`: `E_θ Var_u T ≤ 22.35·γ²/m`, `γ = 2/N`. -/
theorem innerFluct137 {n : ℕ} (hn : 4096 ≤ n) :
    ∫ θ, Var[fun u => Tn (2 * n) (mW n) u θ; uniformSphere (2 * n)] ∂hidGauss (2 * n) (mW n) ≤
      2235 / 100 * (2 / ((2 * n : ℕ) : ℝ)) ^ 2 / (mW n : ℝ) :=
  (innerFluct137_gen (by omega) (one_le_mW (by omega))).trans (gamma_cF2o_le hn)

end BstLean.Part137
