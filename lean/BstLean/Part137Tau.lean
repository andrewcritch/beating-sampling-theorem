import BstLean.Part137Inner

/-!
# Part 137, item 5: the restricted Corollary (the scalar `w = D/ℓ² − 1` of the stand-in)

Role: `delegations/statements/p137-spec.md`. Paper source: `onW16c-cx.md` §4, with the centre
`b = h̄` of Parts 134, 136.

`N` inputs, hidden width `m`, `t = 2/m`, `γ = 2/N`, `θ = (M₁, M₂)`, `h(u) = hid2 M₁ M₂ u`,
`h̄ = hbarW θ`.

* `Bn N m θ = t|h̄|²/γ` (the paper's `ℓ̄²`); `lamn N m u θ = ⟨h(u), h̄⟩/|h̄|²` (the `λ(u)` of
  Part 134; the paper's `ℓ(u)/ℓ̄`).
* `wn N m u θ = D(u)/(ℓ̄² λ(u)²) − 1` (the paper's `w = D/ℓ² − 1`: `wn_eq_ell`);
  `wbar N m θ = 1/ℓ̄² − 1`.
* `tau_sq_eq`: `σ(u)²/λ(u)² = t|h̄|²·w(u)` for the `σ`, `λ` of Part 134.
* `goodU N m ζ`: the good set of inputs `|D − 1| ≤ ζ`, `|λ − 1| ≤ ζ`
  (the paper's `G_ζ`: `|ℓ − ℓ̄| ≤ ζ ℓ̄`).
* `Bn_near`: on `goodHid N m p₁ p₂`: `(ℓ̄² − q_N)² ≤ (cF2o m)²/p₁`; `qN_ge`, `qN_le`.
* `Bn136`: on `good136 n`, `n ≥ 4096`: `0.4936 ≤ ℓ̄² ≤ 0.494`.
* `w_diff`: on the good set, `|w − w̄| ≤ (|D − 1| + (2 + ζ)|λ − 1|)/(L(1 − ζ)²)`.
* `tauFluct_gen`, `tauFluct137`: the second moment of `w − w̄` on the good event and the good
  set of inputs; `tauBad_gen`, `tauBad137`: the probability of the bad inputs on the good event.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part137

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere
  uniformSphere_moments)
open BstLean.Part73 (IsOrth uniformSphere_orth)
open BstLean.Part105 (sphere_cont_integrable)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136

variable {N m : ℕ}

/-- **`ℓ̄² = t|h̄|²/γ`**: the squared length of the centre relative to `γ`. -/
noncomputable def Bn (N m : ℕ) (θ : HidParam N m) : ℝ :=
  2 / (m : ℝ) * normSq (hbarW θ) / (2 / (N : ℝ))

/-- **`λ(u) = ⟨h(u), h̄⟩/|h̄|²`** (Part 134, with `b = h̄`). -/
noncomputable def lamn (N m : ℕ) (u : Fin N → ℝ) (θ : HidParam N m) : ℝ :=
  lam (hbarW θ) (hid2 θ.1 θ.2 u)

/-- **`w(u) = D(u)/ℓ(u)² − 1`**, with `ℓ(u)² = ℓ̄²·λ(u)²`. -/
noncomputable def wn (N m : ℕ) (u : Fin N → ℝ) (θ : HidParam N m) : ℝ :=
  Dn N m u θ / (Bn N m θ * lamn N m u θ ^ 2) - 1

/-- **`w̄ = 1/ℓ̄² − 1`**. -/
noncomputable def wbar (N m : ℕ) (θ : HidParam N m) : ℝ := 1 / Bn N m θ - 1

/-- **The good set of inputs `G_ζ`**: `|D − 1| ≤ ζ` and `|λ − 1| ≤ ζ`. -/
def goodU (N m : ℕ) (ζ : ℝ) : Set ((Fin N → ℝ) × HidParam N m) :=
  {p | |Dn N m p.1 p.2 - 1| ≤ ζ ∧ |lamn N m p.1 p.2 - 1| ≤ ζ}

/-- The hidden event `E` and the good set of inputs together. -/
def goodS (E : Set (HidParam N m)) (ζ : ℝ) : Set ((Fin N → ℝ) × HidParam N m) :=
  {p | p.2 ∈ E ∧ p ∈ goodU N m ζ}

/-! ## The algebra -/

lemma Bn_eq (N m : ℕ) (θ : HidParam N m) : Bn N m θ = (N : ℝ) / m * normSq (hbarW θ) := by
  unfold Bn
  rw [div_div_eq_mul_div]
  ring

lemma lamn_eq (u : Fin N → ℝ) (θ : HidParam N m) :
    lamn N m u θ = dotp (hid2 θ.1 θ.2 u) (hbarW θ) / normSq (hbarW θ) := rfl

/-- `T(u) = γ·ℓ̄²·λ(u)`. -/
lemma Tn_eq_lam (hN : 1 ≤ N) (hm : 1 ≤ m) (u : Fin N → ℝ) {θ : HidParam N m}
    (hb : normSq (hbarW θ) ≠ 0) :
    Tn N m u θ = 2 / (N : ℝ) * Bn N m θ * lamn N m u θ := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hN' : (N : ℝ) ≠ 0 := by positivity
  rw [Bn_eq, lamn_eq]
  unfold Tn
  field_simp

/-- **The paper's form of `w`**: `w = D/ℓ² − 1` with `ℓ = T/(√γ·√(t|h̄|²))`. -/
theorem wn_eq_ell (hN : 1 ≤ N) (hm : 1 ≤ m) (u : Fin N → ℝ) {θ : HidParam N m}
    (hb : normSq (hbarW θ) ≠ 0) :
    Dn N m u θ / (Tn N m u θ / (√(2 / (N : ℝ)) * √(2 / (m : ℝ) * normSq (hbarW θ)))) ^ 2 - 1 =
      wn N m u θ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hb0 : 0 ≤ normSq (hbarW θ) := normSq_nonneg _
  have hB : Bn N m θ ≠ 0 := by
    rw [Bn_eq]
    positivity
  unfold wn
  congr 2
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    Tn_eq_lam hN hm u hb]
  have e : 2 / (m : ℝ) * normSq (hbarW θ) = 2 / (N : ℝ) * Bn N m θ := by
    rw [Bn_eq]
    field_simp
  rw [e]
  field_simp

/-- **The ratio of the two scalars of the stand-in**: `σ(u)²/λ(u)² = t|h̄|²·w(u)`. -/
theorem tau_sq_eq (hN : 1 ≤ N) (hm : 1 ≤ m) (u : Fin N → ℝ) {θ : HidParam N m}
    (hb : normSq (hbarW θ) ≠ 0) (hl : lamn N m u θ ≠ 0) :
    sig (2 / (m : ℝ)) (hbarW θ) (hid2 θ.1 θ.2 u) ^ 2 / lamn N m u θ ^ 2 =
      2 / (m : ℝ) * normSq (hbarW θ) * wn N m u θ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hX : dotp (hid2 θ.1 θ.2 u) (hbarW θ) ≠ 0 := by
    intro h0
    apply hl
    rw [lamn_eq, h0, zero_div]
  have hs : sig (2 / (m : ℝ)) (hbarW θ) (hid2 θ.1 θ.2 u) ^ 2 =
      2 / (m : ℝ) * (normSq (hid2 θ.1 θ.2 u) -
        dotp (hid2 θ.1 θ.2 u) (hbarW θ) ^ 2 / normSq (hbarW θ)) := by
    unfold sig
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (normSq_nonneg _), normSq_res hb]
    rfl
  rw [hs]
  unfold wn
  rw [Dn_eq, Bn_eq, lamn_eq]
  field_simp

/-- **The pointwise comparison on the good set** (`onW16c-cx.md` §4). -/
lemma w_diff {D B l ζ L : ℝ} (hL : 0 < L) (hB : L ≤ B) (hζ1 : ζ < 1)
    (hD : |D - 1| ≤ ζ) (hl : |l - 1| ≤ ζ) :
    |(D / (B * l ^ 2) - 1) - (1 / B - 1)| ≤
      1 / (L * (1 - ζ) ^ 2) * (|D - 1| + (2 + ζ) * |l - 1|) := by
  have hζ0 : 0 ≤ ζ := (abs_nonneg _).trans hD
  have hl1 := abs_le.mp hl
  have hlpos : 0 < l := by linarith
  have hB0 : 0 < B := lt_of_lt_of_le hL hB
  have h1ζ : 0 < 1 - ζ := by linarith
  have e : (D / (B * l ^ 2) - 1) - (1 / B - 1) = (D - l ^ 2) / (B * l ^ 2) := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos (by positivity : 0 < B * l ^ 2), one_div_mul_eq_div]
  have hnum : |D - l ^ 2| ≤ |D - 1| + (2 + ζ) * |l - 1| := by
    have e2 : D - l ^ 2 = (D - 1) - (l - 1) * (l + 1) := by ring
    rw [e2]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    have h3 : |l + 1| ≤ 2 + ζ := by
      rw [abs_of_pos (by linarith)]
      linarith
    nlinarith [abs_nonneg (l - 1), abs_nonneg (l + 1)]
  have hden : L * (1 - ζ) ^ 2 ≤ B * l ^ 2 := by
    have h4 : (1 - ζ) ^ 2 ≤ l ^ 2 := pow_le_pow_left₀ h1ζ.le (by linarith) 2
    exact mul_le_mul hB h4 (sq_nonneg _) hB0.le
  exact div_le_div₀ (by positivity) hnum (by positivity) hden

/-! ## The mean of `T` over the input, and the size of `ℓ̄²` -/

/-- `E_u T(u) = t|h̄|²`. -/
lemma Tn_mean (hN : 1 ≤ N) (θ : HidParam N m) :
    ∫ u, Tn N m u θ ∂uniformSphere N = 2 / (m : ℝ) * normSq (hbarW θ) := by
  unfold Tn
  rw [integral_const_mul]
  congr 1
  unfold dotp normSq
  rw [integral_finsetSum _ fun j _ =>
    (sphere_cont_integrable hN (continuous_hid2_coord θ j)).mul_const _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const, sq]
  rfl

/-- **`ℓ̄ = E_u ℓ(u)`** for `ℓ = T/(√γ·√(t|h̄|²))`: `E_u ℓ(u) = √(t|h̄|²/γ)`. -/
theorem ell_mean (hN : 1 ≤ N) (θ : HidParam N m) :
    ∫ u, Tn N m u θ / (√(2 / (N : ℝ)) * √(2 / (m : ℝ) * normSq (hbarW θ))) ∂uniformSphere N =
      √(Bn N m θ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hA : 0 ≤ 2 / (m : ℝ) * normSq (hbarW θ) := mul_nonneg (by positivity) (normSq_nonneg _)
  rw [integral_div, Tn_mean hN]
  unfold Bn
  rw [Real.sqrt_div hA]
  have hg : 0 < √(2 / (N : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  by_cases h0 : 2 / (m : ℝ) * normSq (hbarW θ) = 0
  · rw [h0]
    simp
  · have hs : 0 < √(2 / (m : ℝ) * normSq (hbarW θ)) :=
      Real.sqrt_pos.mpr (lt_of_le_of_ne hA (Ne.symm h0))
    have e := Real.mul_self_sqrt hA
    rw [div_eq_div_iff (mul_pos hg hs).ne' hg.ne']
    calc 2 / (m : ℝ) * normSq (hbarW θ) * √(2 / (N : ℝ))
        = √(2 / (m : ℝ) * normSq (hbarW θ)) * √(2 / (m : ℝ) * normSq (hbarW θ)) *
            √(2 / (N : ℝ)) := by rw [e]
      _ = _ := by ring

/-- `(ℓ̄² − q_N)² ≤ (N/m)²·errK θ`. -/
lemma Bn_sub_sq_le (hN : 1 ≤ N) (hm : 1 ≤ m) (θ : HidParam N m) :
    (Bn N m θ - qN N) ^ 2 ≤ ((N : ℝ) / m) ^ 2 * errK θ := by
  have := uniformSphere_isProbability N hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : Continuous (fun u => Tn N m u θ - 2 / (N : ℝ) * qN N) :=
    (continuous_Tn_u θ).sub continuous_const
  have e : Bn N m θ - qN N = (N : ℝ) / 2 * ∫ u, (Tn N m u θ - 2 / (N : ℝ) * qN N)
      ∂uniformSphere N := by
    rw [integral_sub (sphere_cont_integrable hN (continuous_Tn_u θ)) (integrable_const _),
      Tn_mean hN, Bn_eq]
    simp only [integral_const, probReal_univ, smul_eq_mul]
    field_simp
  have h1 := sq_integral_le (ρ := uniformSphere N)
    (f := fun u => Tn N m u θ - 2 / (N : ℝ) * qN N) (sphere_cont_integrable hN (hc.pow 2))
  have h2 := Tn_err hN hm θ
  rw [e, mul_pow]
  calc ((N : ℝ) / 2) ^ 2 * (∫ u, (Tn N m u θ - 2 / (N : ℝ) * qN N) ∂uniformSphere N) ^ 2
      ≤ ((N : ℝ) / 2) ^ 2 * ((2 / (m : ℝ)) ^ 2 * errK θ) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (sq_nonneg _)
    _ = ((N : ℝ) / m) ^ 2 * errK θ := by
        field_simp

/-- **On the good hidden event**: `(ℓ̄² − q_N)² ≤ (cF2o m)²/p₁`. -/
theorem Bn_near (hN : 1 ≤ N) (hm : 1 ≤ m) {p₁ p₂ : ℝ} {θ : HidParam N m}
    (hθ : θ ∈ goodHid N m p₁ p₂) :
    (Bn N m θ - qN N) ^ 2 ≤ cF2o m ^ 2 / p₁ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := Bn_sub_sq_le hN hm θ
  have h2 : errK θ ≤ ((m : ℝ) / N * cF2o m) ^ 2 / p₁ := hθ.1.le
  calc (Bn N m θ - qN N) ^ 2 ≤ ((N : ℝ) / m) ^ 2 * errK θ := h1
    _ ≤ ((N : ℝ) / m) ^ 2 * (((m : ℝ) / N * cF2o m) ^ 2 / p₁) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = cF2o m ^ 2 / p₁ := by
        field_simp

lemma dotp_unit_mem' {ι : Type*} [Fintype ι] {u u' : ι → ℝ} (hu : normSq u = 1)
    (hu' : normSq u' = 1) : dotp u u' ∈ Icc (-1 : ℝ) 1 := by
  have h := abs_dotp_le_nrm u u'
  rw [nrm_of_normSq_one hu, nrm_of_normSq_one hu', mul_one] at h
  exact abs_le.mp h

lemma continuous_kk_e0 (N : ℕ) :
    Continuous (fun u' : Fin N → ℝ => kappa (kappa (dotp (e0 N) u'))) :=
  continuous_kappa.comp (continuous_kappa.comp
    (continuous_dotp.comp (continuous_const.prodMk continuous_id)))

lemma continuous_dotp_e0 (N : ℕ) : Continuous (fun u' : Fin N → ℝ => dotp (e0 N) u') :=
  continuous_dotp.comp (continuous_const.prodMk continuous_id)

lemma int_dotp_e0 (hN : 1 ≤ N) : ∫ u', dotp (e0 N) u' ∂uniformSphere N = 0 := by
  have hmom := uniformSphere_moments N hN
  unfold dotp
  rw [integral_finsetSum _ fun i _ => (hmom.int1 i).const_mul _]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_const_mul, hmom.m1, mul_zero]

lemma int_dotp_e0_sq (hN : 1 ≤ N) :
    ∫ u', dotp (e0 N) u' ^ 2 ∂uniformSphere N = 1 / (N : ℝ) := by
  have h := sphere_lin hN (e0 N)
  have e : (∑ i, e0 N i ^ 2) = 1 := normSq_e0 hN
  rw [e, mul_one] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u' => ?_)
  change dotp (e0 N) u' ^ 2 = (dotp u' (e0 N)) ^ 2
  rw [dotp_comm']

/-- `κ(κ(0)) ≤ q_N`. -/
theorem qN_ge (hN : 1 ≤ N) : kappa (kappa 0) ≤ qN N := by
  have := uniformSphere_isProbability N hN
  obtain ⟨b, _, _, hb⟩ := kk_two
  have i1 : Integrable (fun u' : Fin N → ℝ => kappa (kappa 0) + b * dotp (e0 N) u')
      (uniformSphere N) :=
    sphere_cont_integrable hN (continuous_const.add (continuous_const.mul (continuous_dotp_e0 N)))
  have h : ∫ u', (kappa (kappa 0) + b * dotp (e0 N) u') ∂uniformSphere N ≤ qN N := by
    refine integral_mono_ae i1 (sphere_cont_integrable hN (continuous_kk_e0 N)) ?_
    filter_upwards [uniformSphere_ae_sphere N] with u' hu'
    have := (hb _ (dotp_unit_mem' (normSq_e0 hN) hu')).1
    change kappa (kappa 0) + b * dotp (e0 N) u' ≤ kappa (kappa (dotp (e0 N) u'))
    linarith
  rw [integral_add (integrable_const _)
    ((sphere_cont_integrable hN (continuous_dotp_e0 N)).const_mul _), integral_const_mul,
    int_dotp_e0 hN] at h
  simpa using h

/-- `q_N ≤ κ(κ(0)) + (8/25)/N`. -/
theorem qN_le (hN : 1 ≤ N) : qN N ≤ kappa (kappa 0) + 8 / 25 / (N : ℝ) := by
  have := uniformSphere_isProbability N hN
  obtain ⟨b, _, _, hb⟩ := kk_two
  have iA : Integrable (fun u' : Fin N → ℝ => kappa (kappa 0) + b * dotp (e0 N) u')
      (uniformSphere N) :=
    sphere_cont_integrable hN (continuous_const.add (continuous_const.mul (continuous_dotp_e0 N)))
  have iB : Integrable (fun u' : Fin N → ℝ => 8 / 25 * dotp (e0 N) u' ^ 2) (uniformSphere N) :=
    sphere_cont_integrable hN (continuous_const.mul ((continuous_dotp_e0 N).pow 2))
  have h : qN N ≤ ∫ u', ((kappa (kappa 0) + b * dotp (e0 N) u') +
      8 / 25 * dotp (e0 N) u' ^ 2) ∂uniformSphere N := by
    refine integral_mono_ae (sphere_cont_integrable hN (continuous_kk_e0 N)) (iA.add iB) ?_
    filter_upwards [uniformSphere_ae_sphere N] with u' hu'
    have := (hb _ (dotp_unit_mem' (normSq_e0 hN) hu')).2
    change kappa (kappa (dotp (e0 N) u')) ≤ kappa (kappa 0) + b * dotp (e0 N) u' +
      8 / 25 * dotp (e0 N) u' ^ 2
    linarith
  rw [integral_add iA iB, integral_add (integrable_const _)
    ((sphere_cont_integrable hN (continuous_dotp_e0 N)).const_mul _), integral_const_mul,
    integral_const_mul, int_dotp_e0 hN, int_dotp_e0_sq hN] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero] at h
  linarith [show (8 : ℝ) / 25 * (1 / (N : ℝ)) = 8 / 25 / (N : ℝ) by ring]

/-! ## Measurability -/

lemma measurable_Bn (hN : 1 ≤ N) : Measurable (Bn N m) := by
  unfold Bn
  exact ((measurable_normSq.comp (measurable_hbarW hN)).const_mul _).div_const _

lemma measurable_lamn (hN : 1 ≤ N) : Measurable (Function.uncurry (lamn N m)) := by
  have h1 : Measurable (fun z : (Fin N → ℝ) × HidParam N m => hid2 z.2.1 z.2.2 z.1) :=
    (continuous_hid2_joint.comp (continuous_snd.prodMk continuous_fst)).measurable
  have h2 : Measurable (fun z : (Fin N → ℝ) × HidParam N m => hbarW z.2) :=
    (measurable_hbarW hN).comp measurable_snd
  exact measurable_lam2.comp (h2.prodMk h1)

lemma measurable_wn (hN : 1 ≤ N) : Measurable (Function.uncurry (wn N m)) := by
  have h1 : Measurable (fun z : (Fin N → ℝ) × HidParam N m => Bn N m z.2) :=
    (measurable_Bn hN).comp measurable_snd
  exact ((continuous_Dn.measurable).div (h1.mul ((measurable_lamn hN).pow_const 2))).sub_const 1

lemma measurable_wbar (hN : 1 ≤ N) : Measurable (wbar N m) :=
  ((measurable_Bn hN).const_div 1).sub_const 1

lemma goodU_meas (hN : 1 ≤ N) (ζ : ℝ) : MeasurableSet (goodU N m ζ) := by
  have h1 : Measurable (fun p : (Fin N → ℝ) × HidParam N m => |Dn N m p.1 p.2 - 1|) :=
    (continuous_Dn.measurable.sub_const 1).abs
  have h2 : Measurable (fun p : (Fin N → ℝ) × HidParam N m => |lamn N m p.1 p.2 - 1|) :=
    ((measurable_lamn hN).sub_const 1).abs
  exact (measurableSet_le h1 measurable_const).inter (measurableSet_le h2 measurable_const)

lemma goodS_meas (hN : 1 ≤ N) {E : Set (HidParam N m)} (hE : MeasurableSet E) (ζ : ℝ) :
    MeasurableSet (goodS E ζ) :=
  (measurable_snd hE).inter (goodU_meas hN ζ)

lemma continuous_lamn_u (θ : HidParam N m) : Continuous (fun u => lamn N m u θ) :=
  (continuous_dotp.comp ((continuous_hid2_u θ).prodMk continuous_const)).div_const _

/-! ## The second moment of `λ − 1` on the hidden event -/

/-- For every `θ` with `h̄ ≠ 0`: `E_u (λ(u) − 1)² ≤ t²·errK θ/(γ·ℓ̄²)²`. -/
lemma lam_err (hN : 1 ≤ N) (hm : 1 ≤ m) {θ : HidParam N m} (hb : normSq (hbarW θ) ≠ 0) :
    ∫ u, (lamn N m u θ - 1) ^ 2 ∂uniformSphere N ≤
      (2 / (m : ℝ)) ^ 2 * errK θ / (2 / (N : ℝ) * Bn N m θ) ^ 2 := by
  have := uniformSphere_isProbability N hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hb0 : 0 < normSq (hbarW θ) := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hb)
  have hB : 0 < Bn N m θ := by
    rw [Bn_eq]
    positivity
  set c : ℝ := 2 / (N : ℝ) * Bn N m θ with hc
  have hc0 : 0 < c := by positivity
  have hmean : ∫ u, Tn N m u θ ∂uniformSphere N = c := by
    rw [Tn_mean hN, hc, Bn_eq]
    field_simp
  have e : ∀ u, (lamn N m u θ - 1) ^ 2 = (Tn N m u θ - c) ^ 2 / c ^ 2 := by
    intro u
    rw [Tn_eq_lam hN hm u hb, ← hc]
    field_simp
  simp_rw [e]
  rw [integral_div]
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  have hv := variance_eq_integral (μ := uniformSphere N) (X := fun u => Tn N m u θ)
    (continuous_Tn_u θ).measurable.aemeasurable
  rw [hmean] at hv
  rw [← hv]
  exact (variance_le_sq_sub (continuous_Tn_u θ).aestronglyMeasurable
    (sphere_cont_integrable hN (((continuous_Tn_u θ).sub continuous_const).pow 2))).trans
    (Tn_err hN hm θ)

/-- **`‖1_E·(λ − 1)‖_{L²(u, θ)} ≤ cF2o m/L`** if `ℓ̄² ≥ L > 0` on the hidden event `E`. -/
theorem lam_L2 (hN : 1 ≤ N) (hm : 1 ≤ m) {E : Set (HidParam N m)} (hE : MeasurableSet E)
    {L : ℝ} (hL : 0 < L) (hB : ∀ θ ∈ E, L ≤ Bn N m θ) :
    L2le ((uniformSphere N).prod (hidGauss N m))
      (fun p => E.indicator (fun _ => (1 : ℝ)) p.2 * |lamn N m p.1 p.2 - 1|) (cF2o m / L) := by
  have := uniformSphere_isProbability N hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hEi, hEv⟩ := errK_mean (m := m) hN hm
  set K : ℝ := (2 / (m : ℝ)) ^ 2 / (2 / (N : ℝ) * L) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hind : Measurable (fun p : (Fin N → ℝ) × HidParam N m =>
      E.indicator (fun _ => (1 : ℝ)) p.2) :=
    (measurable_const.indicator hE).comp measurable_snd
  have hfm : Measurable (fun p : (Fin N → ℝ) × HidParam N m =>
      E.indicator (fun _ => (1 : ℝ)) p.2 * |lamn N m p.1 p.2 - 1|) :=
    hind.mul ((measurable_lamn hN).sub_const 1).abs
  -- the dominating function
  let G : (Fin N → ℝ) × HidParam N m → ℝ := fun p =>
    E.indicator (fun _ => (1 : ℝ)) p.2 * (lamn N m p.1 p.2 - 1) ^ 2
  have hGm : Measurable G := hind.mul (((measurable_lamn hN).sub_const 1).pow_const 2)
  have hG0 : ∀ p, 0 ≤ G p := fun p =>
    mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (sq_nonneg _)
  have hsec : ∀ θ : HidParam N m, Integrable (fun u => G (u, θ)) (uniformSphere N) := fun θ =>
    ((sphere_cont_integrable hN (((continuous_lamn_u θ).sub continuous_const).pow 2)).const_mul
      (E.indicator (fun _ => (1 : ℝ)) θ) :)
  have hbd : ∀ θ : HidParam N m, ∫ u, G (u, θ) ∂uniformSphere N ≤ K * errK θ := by
    intro θ
    by_cases hθ : θ ∈ E
    · have hBθ := hB θ hθ
      have hb : normSq (hbarW θ) ≠ 0 := by
        intro h0
        have : Bn N m θ = 0 := by rw [Bn_eq, h0, mul_zero]
        linarith
      have e : (fun u => G (u, θ)) = fun u => (lamn N m u θ - 1) ^ 2 := by
        funext u
        simp [G, hθ]
      rw [e]
      refine (lam_err hN hm hb).trans ?_
      have e2 : K * errK θ = (2 / (m : ℝ)) ^ 2 * errK θ / (2 / (N : ℝ) * L) ^ 2 := by
        rw [hK]
        ring
      rw [e2]
      refine div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (errK_nonneg θ))
        (by positivity) ?_
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hBθ (by positivity)) 2
    · have e : (fun u => G (u, θ)) = fun _ => (0 : ℝ) := by
        funext u
        simp [G, hθ]
      rw [e]
      simpa using mul_nonneg hK0 (errK_nonneg θ)
  have hGi : Integrable G ((uniformSphere N).prod (hidGauss N m)) := by
    rw [integrable_prod_iff' hGm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall hsec, ?_⟩
    refine Integrable.mono' (hEi.const_mul K)
      (hGm.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun θ => ?_
    have e : (fun u => ‖G (u, θ)‖) = fun u => G (u, θ) := by
      funext u
      rw [Real.norm_eq_abs, abs_of_nonneg (hG0 _)]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), e]
    exact hbd θ
  refine L2le.of_sq_le hfm.aestronglyMeasurable hGi (fun p => ?_) ?_
  · by_cases hθ : p.2 ∈ E
    · simp [G, hθ]
    · simp [G, hθ]
  · rw [integral_prod_symm _ hGi]
    calc ∫ θ, (∫ u, G (u, θ) ∂uniformSphere N) ∂hidGauss N m
        ≤ ∫ θ, K * errK θ ∂hidGauss N m :=
          integral_mono hGi.integral_prod_right (hEi.const_mul _) hbd
      _ = K * ∫ θ, errK θ ∂hidGauss N m := integral_const_mul _ _
      _ ≤ K * ((m : ℝ) / N * cF2o m) ^ 2 := mul_le_mul_of_nonneg_left hEv hK0
      _ = (cF2o m / L) ^ 2 := by
          rw [hK]
          field_simp

/-- `‖D − 1‖_{L²(u, θ)} ≤ √(10/m + 25/m²)`. -/
theorem Dn_L2 (hN : 1 ≤ N) (hm : 1 ≤ m) :
    L2le ((uniformSphere N).prod (hidGauss N m))
      (fun p => |Dn N m p.1 p.2 - 1|) (√(10 / (m : ℝ) + 25 / (m : ℝ) ^ 2)) := by
  obtain ⟨h1, h2⟩ := normFluct137_joint (m := m) hN hm
  have e : (fun p : (Fin N → ℝ) × HidParam N m => |Dn N m p.1 p.2 - 1| ^ 2) =
      fun p => (Dn N m p.1 p.2 - 1) ^ 2 := by
    funext p
    rw [sq_abs]
  refine ⟨(continuous_Dn.measurable.sub_const 1).abs.aestronglyMeasurable, ?_, ?_⟩
  · rw [e]
    exact h1
  · rw [e, h2, Real.sq_sqrt (by positivity)]

/-! ## The restricted Corollary -/

/-- **The restricted Corollary, general form** (`onW16c-cx.md` §4): if `ℓ̄² ≥ L > 0` on a
measurable hidden event `E`, then on `E` and the good set of inputs `G_ζ`:
`‖w − w̄‖_{L²(u, θ)} ≤ (√(10/m + 25/m²) + (2 + ζ)·cF2o m/L)/(L(1 − ζ)²)`. -/
theorem tauFluct_gen (hN : 1 ≤ N) (hm : 1 ≤ m) {E : Set (HidParam N m)} (hE : MeasurableSet E)
    {L ζ : ℝ} (hL : 0 < L) (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) (hB : ∀ θ ∈ E, L ≤ Bn N m θ) :
    L2le ((uniformSphere N).prod (hidGauss N m))
      ((goodS E ζ).indicator fun p => wn N m p.1 p.2 - wbar N m p.2)
      (1 / (L * (1 - ζ) ^ 2) *
        (√(10 / (m : ℝ) + 25 / (m : ℝ) ^ 2) + (2 + ζ) * (cF2o m / L))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1ζ : 0 < 1 - ζ := by linarith
  have hc0 : 0 ≤ cF2o m / L := div_nonneg (cF2o_pos hm).le hL.le
  have hsum := (Dn_L2 (m := m) hN hm).add'
    ((lam_L2 hN hm hE hL hB).const_mul_nonneg (by linarith : (0 : ℝ) ≤ 2 + ζ))
    (Real.sqrt_nonneg _) (mul_nonneg (by linarith) hc0)
  have hall := hsum.const_mul_nonneg (c := 1 / (L * (1 - ζ) ^ 2)) (by positivity)
  have hFm : Measurable ((goodS E ζ).indicator fun p : (Fin N → ℝ) × HidParam N m =>
      wn N m p.1 p.2 - wbar N m p.2) :=
    ((measurable_wn hN).sub ((measurable_wbar hN).comp measurable_snd)).indicator
      (goodS_meas hN hE ζ)
  refine L2le.of_abs_le hFm.aestronglyMeasurable hall fun p => ?_
  by_cases hp : p ∈ goodS E ζ
  · obtain ⟨hpE, hpD, hpl⟩ := hp
    have hw := w_diff hL (hB p.2 hpE) hζ1 hpD hpl
    rw [Set.indicator_of_mem (show p ∈ goodS E ζ from ⟨hpE, hpD, hpl⟩)]
    have e : E.indicator (fun _ => (1 : ℝ)) p.2 = 1 := Set.indicator_of_mem hpE _
    rw [e, one_mul]
    refine le_trans ?_ (le_abs_self _)
    exact hw
  · rw [Set.indicator_of_notMem hp, abs_zero]
    exact abs_nonneg _

/-- The same as a second moment: the integral of `(w − w̄)²` over the good event and the good
set of inputs. -/
theorem tauFluct_gen_int (hN : 1 ≤ N) (hm : 1 ≤ m) {E : Set (HidParam N m)}
    (hE : MeasurableSet E) {L ζ : ℝ} (hL : 0 < L) (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1)
    (hB : ∀ θ ∈ E, L ≤ Bn N m θ) :
    ∫ p, (goodS E ζ).indicator (fun p => (wn N m p.1 p.2 - wbar N m p.2) ^ 2) p
        ∂((uniformSphere N).prod (hidGauss N m)) ≤
      (1 / (L * (1 - ζ) ^ 2) *
        (√(10 / (m : ℝ) + 25 / (m : ℝ) ^ 2) + (2 + ζ) * (cF2o m / L))) ^ 2 := by
  have h := (tauFluct_gen hN hm hE hL hζ0 hζ1 hB).le
  refine le_trans (le_of_eq ?_) h
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  by_cases hp : p ∈ goodS E ζ
  · simp [Set.indicator_of_mem hp]
  · simp [Set.indicator_of_notMem hp]

/-- **The bad inputs on the hidden event** (Chebyshev, `onW16c-cx.md` §4):
`Pr(θ ∈ E, u ∉ G_ζ) ≤ (10/m + 25/m² + (cF2o m)²/L²)/ζ²`. -/
theorem tauBad_gen (hN : 1 ≤ N) (hm : 1 ≤ m) {E : Set (HidParam N m)} (hE : MeasurableSet E)
    {L ζ : ℝ} (hL : 0 < L) (hζ : 0 < ζ) (hB : ∀ θ ∈ E, L ≤ Bn N m θ) :
    ((uniformSphere N).prod (hidGauss N m)).real {p | p.2 ∈ E ∧ p ∉ goodU N m ζ} ≤
      (10 / (m : ℝ) + 25 / (m : ℝ) ^ 2 + (cF2o m / L) ^ 2) / ζ ^ 2 := by
  have := uniformSphere_isProbability N hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 := Dn_L2 (m := m) hN hm
  have h2 := lam_L2 hN hm hE hL hB
  set g : (Fin N → ℝ) × HidParam N m → ℝ := fun p =>
    |Dn N m p.1 p.2 - 1| ^ 2 + (E.indicator (fun _ => (1 : ℝ)) p.2 * |lamn N m p.1 p.2 - 1|) ^ 2
    with hg
  have hgi : Integrable g ((uniformSphere N).prod (hidGauss N m)) := h1.int_sq.add h2.int_sq
  have hg0 : 0 ≤ᵐ[(uniformSphere N).prod (hidGauss N m)] g :=
    Filter.Eventually.of_forall fun p => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmk := mul_meas_ge_le_integral_of_nonneg hg0 hgi (ζ ^ 2)
  have hsub : {p : (Fin N → ℝ) × HidParam N m | p.2 ∈ E ∧ p ∉ goodU N m ζ} ⊆
      {p | ζ ^ 2 ≤ g p} := by
    rintro p ⟨hpE, hpb⟩
    have e : E.indicator (fun _ => (1 : ℝ)) p.2 = 1 := Set.indicator_of_mem hpE _
    change ζ ^ 2 ≤ g p
    simp only [hg, e, one_mul]
    by_contra hlt
    push Not at hlt
    apply hpb
    have a1 : |Dn N m p.1 p.2 - 1| ^ 2 < ζ ^ 2 := by
      nlinarith [sq_nonneg (|lamn N m p.1 p.2 - 1|)]
    have a2 : |lamn N m p.1 p.2 - 1| ^ 2 < ζ ^ 2 := by
      nlinarith [sq_nonneg (|Dn N m p.1 p.2 - 1|)]
    exact ⟨(abs_lt_of_sq_lt_sq a1 hζ.le |>.le.trans' (by rw [abs_abs])),
      (abs_lt_of_sq_lt_sq a2 hζ.le |>.le.trans' (by rw [abs_abs]))⟩
  have hint : ∫ p, g p ∂((uniformSphere N).prod (hidGauss N m)) ≤
      10 / (m : ℝ) + 25 / (m : ℝ) ^ 2 + (cF2o m / L) ^ 2 := by
    rw [hg, integral_add h1.int_sq h2.int_sq]
    have := h1.le
    rw [Real.sq_sqrt (by positivity)] at this
    exact add_le_add this h2.le
  have hmono := measureReal_mono (μ := (uniformSphere N).prod (hidGauss N m)) hsub
    (measure_ne_top _ _)
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact (mul_le_mul_of_nonneg_left hmono (sq_nonneg _)).trans (hmk.trans hint)

/-! ## The World network of the Focus -/

lemma mW_ge_pow42 {n : ℕ} (hn : 4096 ≤ n) : 4398046511104 ≤ mW n := by
  by_contra h
  have h1 : mW n < 4398046511104 := by omega
  have h2 : mW n ^ 2 < 4398046511104 ^ 2 := Nat.pow_lt_pow_left h1 (by norm_num)
  have h3 : 4096 ^ 7 ≤ n ^ 7 := Nat.pow_le_pow_left hn 7
  have h4 := mW_sq_ge n
  have h5 : (4398046511104 : ℕ) ^ 2 ≤ 4096 ^ 7 := by norm_num
  omega

/-- **The size of `ℓ̄²` on the good event of Part 136**: for `n ≥ 4096` and `θ ∈ good136 n`:
`0.4936 ≤ t|h̄|²/γ ≤ 0.494`. -/
theorem Bn136 {n : ℕ} (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ good136 n) :
    4936 / 10000 ≤ Bn (2 * n) (mW n) θ ∧ Bn (2 * n) (mW n) θ ≤ 494 / 1000 := by
  have hN : 1 ≤ 2 * n := by omega
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hm42 : (4398046511104 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_pow42 hn
  have hm0 : (0 : ℝ) < mW n := by linarith
  have h1 := Bn_near hN hm hθ
  have h2 := cF2o_sq_le hmM
  have h3 : cF2o (mW n) ^ 2 / (4 / 100) ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by norm_num)]
    refine h2.trans ?_
    rw [div_le_iff₀ hm0]
    nlinarith
  have h4 : |Bn (2 * n) (mW n) θ - qN (2 * n)| ≤ 1 / 10000 :=
    abs_le_of_sq_le_sq' (h1.trans h3) (by norm_num) |> abs_le.mpr
  have h4' := abs_le.mp h4
  have q1 := qN_ge hN
  have q2 := qN_le hN
  have k1 := kappa2_zero_ge
  have k2 := kappa2_zero_le
  have hNr : (8192 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
    have : 8192 ≤ 2 * n := by omega
    exact_mod_cast this
  have h5 : 8 / 25 / ((2 * n : ℕ) : ℝ) ≤ 8 / 25 / 8192 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hNr
  constructor
  · linarith
  · have : (8 : ℝ) / 25 / 8192 ≤ 4 / 100000 := by norm_num
    linarith

/-- **`tauFluct137`** (the restricted Corollary of `onW16c-cx.md` §4, with the centre `h̄`):
`N = 2n`, `m = mW n`, `n ≥ 4096`, `0 ≤ ζ < 1`. On the good event `good136 n` of Part 136 and
the good set of inputs `G_ζ`, the second moment of `w − w̄` over `(u, θ)` is at most
`((√(10/m + 25/m²) + (2 + ζ)·√(22.35/m)/L)/(L(1 − ζ)²))²` with `L = 0.4936`. -/
theorem tauFluct137 {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) :
    ∫ p, (goodS (good136 n) ζ).indicator
        (fun p => (wn (2 * n) (mW n) p.1 p.2 - wbar (2 * n) (mW n) p.2) ^ 2) p
        ∂((uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n))) ≤
      (1 / (4936 / 10000 * (1 - ζ) ^ 2) *
        (√(10 / (mW n : ℝ) + 25 / (mW n : ℝ) ^ 2) +
          (2 + ζ) * (√(2235 / 100 / (mW n : ℝ)) / (4936 / 10000)))) ^ 2 := by
  have hN : 1 ≤ 2 * n := by omega
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hm0 : (0 : ℝ) < mW n := by exact_mod_cast hm
  have h := tauFluct_gen_int hN hm (good136_meas (by omega : 1 ≤ n))
    (by norm_num : (0 : ℝ) < 4936 / 10000) hζ0 hζ1 (fun θ hθ => (Bn136 hn hθ).1)
  refine h.trans ?_
  have hc : cF2o (mW n) ≤ √(2235 / 100 / (mW n : ℝ)) :=
    (le_abs_self _).trans (Real.abs_le_sqrt (cF2o_sq_le hmM))
  have h1ζ : 0 < 1 - ζ := by linarith
  have hc0 := (cF2o_pos hm).le
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by linarith))
  exact div_le_div_of_nonneg_right hc (by norm_num)

/-- **The bad inputs on the good event of Part 136**: `n ≥ 4096`, `ζ > 0`:
`Pr(θ ∈ good136 n, u ∉ G_ζ) ≤ (10/m + 25/m² + 22.35/(m L²))/ζ²`, `L = 0.4936`. -/
theorem tauBad137 {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ : 0 < ζ) :
    ((uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n))).real
        {p | p.2 ∈ good136 n ∧ p ∉ goodU (2 * n) (mW n) ζ} ≤
      (10 / (mW n : ℝ) + 25 / (mW n : ℝ) ^ 2 +
        2235 / 100 / (mW n : ℝ) / (4936 / 10000) ^ 2) / ζ ^ 2 := by
  have hN : 1 ≤ 2 * n := by omega
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have h := tauBad_gen hN hm (good136_meas (by omega : 1 ≤ n))
    (by norm_num : (0 : ℝ) < 4936 / 10000) hζ (fun θ hθ => (Bn136 hn hθ).1)
  refine h.trans ?_
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  rw [div_pow]
  exact add_le_add le_rfl (div_le_div_of_nonneg_right (cF2o_sq_le hmM) (by norm_num))

/-- **The pointwise bound on the good set** (`onW16c-cx.md` §4): for `n ≥ 4096`,
`θ ∈ good136 n` and `u ∈ G_ζ`: `|w − w̄| ≤ ζ(3 + ζ)/(L(1 − ζ)²)`, `L = 0.4936`; and
`1/0.494 − 1 ≤ w̄ ≤ 1/0.4936 − 1`. -/
theorem wClose137 {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ1 : ζ < 1)
    {p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)} (hp : p ∈ goodS (good136 n) ζ) :
    |wn (2 * n) (mW n) p.1 p.2 - wbar (2 * n) (mW n) p.2| ≤
        ζ * (3 + ζ) / (4936 / 10000 * (1 - ζ) ^ 2) ∧
      1 / (494 / 1000) - 1 ≤ wbar (2 * n) (mW n) p.2 ∧
      wbar (2 * n) (mW n) p.2 ≤ 1 / (4936 / 10000) - 1 := by
  obtain ⟨hpE, hpD, hpl⟩ := hp
  obtain ⟨hB1, hB2⟩ := Bn136 hn hpE
  have hζ0 : 0 ≤ ζ := (abs_nonneg _).trans hpD
  have h1ζ : 0 < 1 - ζ := by linarith
  have hw := w_diff (by norm_num : (0 : ℝ) < 4936 / 10000) hB1 hζ1 hpD hpl
  have hB0 : 0 < Bn (2 * n) (mW n) p.2 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · refine hw.trans ?_
    rw [one_div_mul_eq_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    nlinarith
  · unfold wbar
    have := one_div_le_one_div_of_le hB0 hB2
    linarith
  · unfold wbar
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4936 / 10000) hB1
    linarith

end BstLean.Part137
