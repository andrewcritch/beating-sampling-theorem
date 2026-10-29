import BstLean.Part154Defs
import BstLean.Part105Law

/-!
# Part 154: Lemma PR (i) for a Gaussian pair, by the Mehler step of Part 134

Paper source: `proofs/option-n/theorem5-06-centre.tex`, Lemma PR (i), in absolute-value form.
The proof here is by the second-order Gebelein inequality `BstLean.Part134.mehler2_sharp` for the
truncated functions `min(relu(v + ·), N)`, and `N → ∞` by dominated convergence.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part137 BstLean.Part153
open BstLean.Part105 (BM sC sC_nonneg sC_sq gaussLin105)

/-! ## Closed forms -/

lemma PhiG_add_negP (v : ℝ) : PhiG v + PhiG (-v) = 1 := by
  have h1 : HasDerivAt (fun x => psiG (-x)) (PhiG (-v) * -1) v :=
    (hasDerivAt_psiG (-v)).comp v (hasDerivAt_neg v)
  have h2 : HasDerivAt (fun x => psiG x - x) (PhiG v - 1) v :=
    (hasDerivAt_psiG v).sub (hasDerivAt_id v)
  have e : (fun x => psiG (-x)) = fun x => psiG x - x := by
    funext x
    rw [← psiS_one, ← psiS_one, psiS_neg]
  rw [e] at h1
  have := h1.unique h2
  linarith

private lemma relu_ind (v z : ℝ) : relu (v + z) = (Ioi (-v)).indicator (fun z => v + z) z := by
  by_cases hz : z ∈ Ioi (-v)
  · rw [indicator_of_mem hz, relu_of_nonneg]
    have := mem_Ioi.mp hz
    linarith
  · rw [indicator_of_notMem hz, relu_of_nonpos]
    have := not_lt.mp (fun h => hz (mem_Ioi.mpr h))
    linarith

/-- `E relu(v + Z) = ψ₁(v)`. -/
lemma int_relu_one (v : ℝ) : ∫ z, relu (v + z) ∂gaussianReal 0 1 = psiG v := by
  rw [← psiS_one]
  unfold psiS
  simp only [one_mul]

/-- `E[relu(v + Z)·Z] = Φ(v)`: the first Hermite coefficient. -/
lemma int_relu_mul (v : ℝ) : ∫ z, relu (v + z) * z ∂gaussianReal 0 1 = PhiG v := by
  have e : (fun z : ℝ => relu (v + z) * z) = (Ioi (-v)).indicator (fun z => v * z + z ^ 2) := by
    funext z
    rw [relu_ind]
    by_cases hz : z ∈ Ioi (-v)
    · rw [indicator_of_mem hz, indicator_of_mem hz]; ring
    · rw [indicator_of_notMem hz, indicator_of_notMem hz]; ring
  rw [e, integral_indicator measurableSet_Ioi,
    integral_add ((intOn_id _).const_mul v) (integrable_pow_gauss 2).integrableOn,
    integral_const_mul, int_z, int_z2]
  ring

/-- `E relu(v + Z)² = (v² + 1)Φ(v) + vφ(v)`. -/
lemma int_relu_sq (v : ℝ) :
    ∫ z, relu (v + z) ^ 2 ∂gaussianReal 0 1 = (v ^ 2 + 1) * PhiG v + v * phiG v := by
  have e : (fun z : ℝ => relu (v + z) ^ 2) =
      (Ioi (-v)).indicator (fun z => v ^ 2 + (2 * v) * z + z ^ 2) := by
    funext z
    rw [relu_ind]
    by_cases hz : z ∈ Ioi (-v)
    · rw [indicator_of_mem hz, indicator_of_mem hz]; ring
    · rw [indicator_of_notMem hz, indicator_of_notMem hz]; ring
  have i0 : IntegrableOn (fun _ : ℝ => v ^ 2) (Ioi (-v)) (gaussianReal 0 1) :=
    (integrable_const _).integrableOn
  have i1 : IntegrableOn (fun z : ℝ => (2 * v) * z) (Ioi (-v)) (gaussianReal 0 1) :=
    (intOn_id _).const_mul _
  have hA : ∫ z in Ioi (-v), v ^ 2 + (2 * v) * z + z ^ 2 ∂gaussianReal 0 1 =
      (∫ z in Ioi (-v), v ^ 2 + (2 * v) * z ∂gaussianReal 0 1) +
        ∫ z in Ioi (-v), z ^ 2 ∂gaussianReal 0 1 :=
    integral_add (i0.add i1) (integrable_pow_gauss 2).integrableOn
  have hB : ∫ z in Ioi (-v), v ^ 2 + (2 * v) * z ∂gaussianReal 0 1 =
      (∫ z in Ioi (-v), v ^ 2 ∂gaussianReal 0 1) +
        ∫ z in Ioi (-v), (2 * v) * z ∂gaussianReal 0 1 := integral_add i0 i1
  rw [e, integral_indicator measurableSet_Ioi, hA, hB,
    setIntegral_const, integral_const_mul, int_z, int_z2]
  simp only [smul_eq_mul, PhiG]
  ring

/-- `Var relu(v + Z) − Φ(v)² = U(v)`. -/
lemma Ures_eq_int (v : ℝ) :
    ∫ z, relu (v + z) ^ 2 ∂gaussianReal 0 1 - psiG v ^ 2 - PhiG v ^ 2 = Ures v := by
  rw [int_relu_sq]
  unfold Ures
  have h := PhiG_add_negP v
  have hp : psiG (-v) = -v * PhiG (-v) + phiG v := by unfold psiG; rw [phiG_neg]
  rw [hp, show PhiG (-v) = 1 - PhiG v by linarith]
  unfold psiG
  ring

lemma Ures_zero_nonneg : 0 ≤ Ures 0 := by
  have h := PhiG_add_negP 0
  have h2 := psiG_mul_le 0
  simp only [neg_zero] at h h2
  have h0 : PhiG 0 = 1 / 2 := by linarith
  have h3 : 1 / (2 * π) ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [pi_gt_three]
  unfold Ures
  rw [neg_zero, h0]
  linarith

/-! ## From `stdGauss (Fin 1)` to the real line -/

private lemma int_fin1 {F : ℝ → ℝ} (hF : Measurable F) :
    ∫ x : Fin 1 → ℝ, F (x 0) ∂stdGauss (Fin 1) = ∫ t, F t ∂gaussianReal 0 1 := by
  have h2 := (measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) 0).map_eq
  conv_rhs => rw [← h2]
  rw [integral_map (measurable_pi_apply 0).aemeasurable hF.aestronglyMeasurable]
  rfl

private lemma int_fin1_prod {H : ℝ × ℝ → ℝ} (hH : Measurable H) :
    ∫ w : (Fin 1 → ℝ) × (Fin 1 → ℝ), H (w.1 0, w.2 0)
        ∂((stdGauss (Fin 1)).prod (stdGauss (Fin 1))) =
      ∫ p, H p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have h2 := measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) 0
  have h3 := (h2.prod h2).map_eq
  conv_rhs => rw [← h3]
  rw [integral_map (by fun_prop) hH.aestronglyMeasurable]
  rfl

private lemma var1 {f : ℝ → ℝ} (hf : BM f) :
    ∫ t, (f t - ∫ s, f s ∂gaussianReal 0 1) ^ 2 ∂gaussianReal 0 1 =
      ∫ t, f t ^ 2 ∂gaussianReal 0 1 - (∫ t, f t ∂gaussianReal 0 1) ^ 2 := by
  set c := ∫ s, f s ∂gaussianReal 0 1 with hc
  have e : ∀ t, (f t - c) ^ 2 = f t ^ 2 - (2 * c) * f t + c ^ 2 := fun t => by ring
  have hcc : ∫ _ : ℝ, c ^ 2 ∂gaussianReal 0 1 = c ^ 2 := by simp
  simp_rw [e]
  have i1 : Integrable (fun t => f t ^ 2) (gaussianReal 0 1) := hf.sq.integrable _
  have i2 : Integrable (fun t => (2 * c) * f t) (gaussianReal 0 1) :=
    (hf.integrable _).const_mul _
  have hA : ∫ t, f t ^ 2 - (2 * c) * f t + c ^ 2 ∂gaussianReal 0 1 =
      (∫ t, f t ^ 2 - (2 * c) * f t ∂gaussianReal 0 1) + ∫ _ : ℝ, c ^ 2 ∂gaussianReal 0 1 :=
    integral_add (i1.sub i2) (integrable_const _)
  have hB : ∫ t, f t ^ 2 - (2 * c) * f t ∂gaussianReal 0 1 =
      (∫ t, f t ^ 2 ∂gaussianReal 0 1) - ∫ t, (2 * c) * f t ∂gaussianReal 0 1 :=
    integral_sub i1 i2
  rw [hA, hB, integral_const_mul, hcc, ← hc]
  ring

/-- The second-order Gebelein inequality of Part 134 on the real line. -/
private lemma mehler1 {ρ : ℝ} (hρ : |ρ| ≤ 1) {f g : ℝ → ℝ} (hf : BM f) (hg : BM g) :
    |∫ p : ℝ × ℝ, f p.1 * g (ρ * p.1 + sC ρ * p.2) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) -
        (∫ t, f t ∂gaussianReal 0 1) * (∫ t, g t ∂gaussianReal 0 1) -
        ρ * ((∫ t, f t * t ∂gaussianReal 0 1) * (∫ t, g t * t ∂gaussianReal 0 1))| ≤
      ρ ^ 2 *
        √(∫ t, f t ^ 2 ∂gaussianReal 0 1 - (∫ t, f t ∂gaussianReal 0 1) ^ 2 -
          (∫ t, f t * t ∂gaussianReal 0 1) ^ 2) *
        √(∫ t, g t ^ 2 ∂gaussianReal 0 1 - (∫ t, g t ∂gaussianReal 0 1) ^ 2 -
          (∫ t, g t * t ∂gaussianReal 0 1) ^ 2) := by
  have h := BstLean.Part134.mehler2_sharp (ι := Fin 1) hρ (hf.comp (measurable_pi_apply 0))
    (hg.comp (measurable_pi_apply 0))
  have e0 : ∫ w : (Fin 1 → ℝ) × (Fin 1 → ℝ), f (w.1 0) * g ((ρ • w.1 + sC ρ • w.2) 0)
        ∂((stdGauss (Fin 1)).prod (stdGauss (Fin 1))) =
      ∫ p : ℝ × ℝ, f p.1 * g (ρ * p.1 + sC ρ * p.2)
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    int_fin1_prod (H := fun p => f p.1 * g (ρ * p.1 + sC ρ * p.2))
      ((hf.meas.comp measurable_fst).mul (hg.meas.comp (by fun_prop)))
  have ef : ∀ {f : ℝ → ℝ}, BM f →
      ∫ x : Fin 1 → ℝ, f (x 0) ∂stdGauss (Fin 1) = ∫ t, f t ∂gaussianReal 0 1 :=
    fun hf => int_fin1 hf.meas
  have efx : ∀ {f : ℝ → ℝ}, BM f →
      ∫ x : Fin 1 → ℝ, f (x 0) * x 0 ∂stdGauss (Fin 1) = ∫ t, f t * t ∂gaussianReal 0 1 :=
    fun {f} hf => int_fin1 (F := fun t => f t * t) (hf.meas.mul measurable_id)
  have ef2 : ∀ {f : ℝ → ℝ}, BM f → ∀ c : ℝ,
      ∫ x : Fin 1 → ℝ, (f (x 0) - c) ^ 2 ∂stdGauss (Fin 1) =
        ∫ t, (f t - c) ^ 2 ∂gaussianReal 0 1 :=
    fun {f} hf c => int_fin1 (F := fun t => (f t - c) ^ 2) ((hf.meas.sub_const c).pow_const 2)
  simp only [Fin.sum_univ_one] at h
  rw [e0, ef hf, ef hg, efx hf, efx hg, ef2 hf, ef2 hg, var1 hf, var1 hg] at h
  exact h

/-! ## Truncation -/

/-- `min(relu(v + t), N)`. -/
private noncomputable def fT (v : ℝ) (N : ℕ) (t : ℝ) : ℝ := min (relu (v + t)) (N : ℝ)

private lemma fT_meas (v : ℝ) (N : ℕ) : Measurable (fT v N) :=
  (measurable_relu.comp (measurable_const.add measurable_id)).min measurable_const

private lemma fT_nonneg (v : ℝ) (N : ℕ) (t : ℝ) : 0 ≤ fT v N t :=
  le_min (relu_nonneg _) (Nat.cast_nonneg N)

private lemma fT_le_abs (v : ℝ) (N : ℕ) (t : ℝ) : fT v N t ≤ |v + t| :=
  (min_le_left _ _).trans ((le_abs_self _).trans (abs_relu_le _))

private lemma fT_BM (v : ℝ) (N : ℕ) : BM (fT v N) :=
  ⟨fT_meas v N, N, fun t => by
    rw [abs_of_nonneg (fT_nonneg v N t)]; exact min_le_right _ _⟩

private lemma fT_tendsto (v t : ℝ) : Tendsto (fun N : ℕ => fT v N t) atTop (𝓝 (relu (v + t))) := by
  refine tendsto_atTop_of_eventually_const (i₀ := ⌈relu (v + t)⌉₊) fun N hN => ?_
  exact min_eq_left ((Nat.le_ceil _).trans (Nat.cast_le.mpr hN))

private lemma dom1 (v : ℝ) (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (hm : ∀ N, Measurable (F N))
    (hb : ∀ N t, |F N t| ≤ 1 + 2 * v ^ 2 + 3 * t ^ 2)
    (hl : ∀ t, Tendsto (fun N => F N t) atTop (𝓝 (f t))) :
    Tendsto (fun N => ∫ t, F N t ∂gaussianReal 0 1) atTop (𝓝 (∫ t, f t ∂gaussianReal 0 1)) := by
  refine tendsto_integral_of_dominated_convergence (fun t => 1 + 2 * v ^ 2 + 3 * t ^ 2)
    (fun N => (hm N).aestronglyMeasurable) ?_
    (fun N => Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hb N t)
    (Eventually.of_forall hl)
  exact (integrable_const _).add ((integrable_pow_gauss 2).const_mul 3)

private lemma lim_m (v : ℝ) : Tendsto (fun N => ∫ t, fT v N t ∂gaussianReal 0 1) atTop
    (𝓝 (psiG v)) := by
  rw [← int_relu_one]
  refine dom1 v _ _ (fT_meas v) (fun N t => ?_) (fT_tendsto v)
  rw [abs_of_nonneg (fT_nonneg v N t)]
  have h1 := fT_le_abs v N t
  have h2 : |v + t| ≤ 1 + |v + t| ^ 2 := by nlinarith [sq_nonneg (|v + t| - 1)]
  rw [sq_abs] at h2
  nlinarith [sq_nonneg (v - t)]

private lemma lim_q (v : ℝ) : Tendsto (fun N => ∫ t, fT v N t ^ 2 ∂gaussianReal 0 1) atTop
    (𝓝 (∫ t, relu (v + t) ^ 2 ∂gaussianReal 0 1)) := by
  refine dom1 v _ _ (fun N => (fT_meas v N).pow_const 2) (fun N t => ?_)
    (fun t => (fT_tendsto v t).pow 2)
  rw [abs_of_nonneg (sq_nonneg _)]
  have h1 := fT_le_abs v N t
  have h0 := fT_nonneg v N t
  have h2 : fT v N t ^ 2 ≤ |v + t| ^ 2 := pow_le_pow_left₀ h0 h1 2
  rw [sq_abs] at h2
  nlinarith [sq_nonneg (v - t)]

private lemma lim_c (v : ℝ) : Tendsto (fun N => ∫ t, fT v N t * t ∂gaussianReal 0 1) atTop
    (𝓝 (PhiG v)) := by
  rw [← int_relu_mul]
  refine dom1 v _ _ (fun N => (fT_meas v N).mul measurable_id) (fun N t => ?_)
    (fun t => (fT_tendsto v t).mul_const t)
  rw [abs_mul, abs_of_nonneg (fT_nonneg v N t)]
  have h1 := fT_le_abs v N t
  have h0 := fT_nonneg v N t
  have h3 : fT v N t * |t| ≤ |v + t| * |t| := mul_le_mul_of_nonneg_right h1 (abs_nonneg t)
  have h4 : |v + t| * |t| ≤ |v + t| ^ 2 + |t| ^ 2 := by
    nlinarith [sq_nonneg (|v + t| - |t|), abs_nonneg (v + t), abs_nonneg t]
  rw [sq_abs, sq_abs] at h4
  nlinarith [sq_nonneg (v - t)]

private lemma lim_a {ρ : ℝ} (hρ : |ρ| ≤ 1) (v v' : ℝ) :
    Tendsto (fun N => ∫ p : ℝ × ℝ, fT v N p.1 * fT v' N (ρ * p.1 + sC ρ * p.2)
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) atTop
    (𝓝 (∫ p : ℝ × ℝ, relu (v + p.1) * relu (v' + (ρ * p.1 + sC ρ * p.2))
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))) := by
  have hs2 := sC_sq hρ
  have hr2 : ρ ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one ρ).mpr hρ
  refine tendsto_integral_of_dominated_convergence
    (fun p : ℝ × ℝ => 2 * v ^ 2 + 3 * v' ^ 2 + 5 * p.1 ^ 2 + 3 * p.2 ^ 2)
    (fun N => (((fT_meas v N).comp measurable_fst).mul
      ((fT_meas v' N).comp (by fun_prop))).aestronglyMeasurable) ?_
    (fun N => Eventually.of_forall fun p => ?_)
    (Eventually.of_forall fun p => (fT_tendsto v p.1).mul (fT_tendsto v' _))
  · have i1 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2)
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := (integrable_pow_gauss 2).comp_fst _
    have i2 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2)
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := (integrable_pow_gauss 2).comp_snd _
    exact ((integrable_const _).add (i1.const_mul 5)).add (i2.const_mul 3)
  · set q := ρ * p.1 + sC ρ * p.2 with hq
    have a0 := fT_nonneg v N p.1
    have b0 := fT_nonneg v' N q
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg a0 b0)]
    have a2 : fT v N p.1 ^ 2 ≤ |v + p.1| ^ 2 := pow_le_pow_left₀ a0 (fT_le_abs v N p.1) 2
    have b2 : fT v' N q ^ 2 ≤ |v' + q| ^ 2 := pow_le_pow_left₀ b0 (fT_le_abs v' N q) 2
    rw [sq_abs] at a2 b2
    have a3 : (v + p.1) ^ 2 ≤ 2 * v ^ 2 + 2 * p.1 ^ 2 := by nlinarith [sq_nonneg (v - p.1)]
    have b3 : (v' + q) ^ 2 ≤ 3 * v' ^ 2 + 3 * p.1 ^ 2 + 3 * p.2 ^ 2 := by
      have t1 : (v' + q) ^ 2 ≤ 3 * v' ^ 2 + 3 * (ρ * p.1) ^ 2 + 3 * (sC ρ * p.2) ^ 2 := by
        rw [hq]
        nlinarith [sq_nonneg (v' - ρ * p.1), sq_nonneg (v' - sC ρ * p.2),
          sq_nonneg (ρ * p.1 - sC ρ * p.2)]
      have t2 : (ρ * p.1) ^ 2 ≤ p.1 ^ 2 := by
        rw [mul_pow]; nlinarith [sq_nonneg p.1]
      have t3 : (sC ρ * p.2) ^ 2 ≤ p.2 ^ 2 := by
        rw [mul_pow, hs2]; nlinarith [sq_nonneg p.2, sq_nonneg ρ]
      linarith
    nlinarith [sq_nonneg (fT v N p.1 - fT v' N q)]

/-- Lemma PR (i) for a standard Gaussian pair with unit scales. -/
private lemma PR_unit {ρ : ℝ} (hρ : |ρ| ≤ 1) (v v' : ℝ) :
    |∫ p : ℝ × ℝ, relu (v + p.1) * relu (v' + (ρ * p.1 + sC ρ * p.2))
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) -
        psiG v * psiG v' - ρ * (PhiG v * PhiG v')| ≤
      ρ ^ 2 * √(Ures v) * √(Ures v') := by
  have h := fun N : ℕ => mehler1 hρ (fT_BM v N) (fT_BM v' N)
  have hL := (((lim_a hρ v v').sub ((lim_m v).mul (lim_m v'))).sub
    (((lim_c v).mul (lim_c v')).const_mul ρ)).abs
  have hR := ((((lim_q v).sub ((lim_m v).pow 2)).sub ((lim_c v).pow 2)).sqrt.const_mul
    (ρ ^ 2)).mul (((lim_q v').sub ((lim_m v').pow 2)).sub ((lim_c v').pow 2)).sqrt
  have := le_of_tendsto_of_tendsto' hL hR h
  rw [Ures_eq_int, Ures_eq_int] at this
  exact this

/-- **Lemma PR (i), scalar form.** `(Z, Z′) = (x, ρx + √(1 − ρ²)y)` is a standard Gaussian pair
with correlation `ρ`. -/
theorem PR_scalar {ρ : ℝ} (hρ : |ρ| ≤ 1) (a a' : ℝ) {σ σ' : ℝ} (hσ : 0 < σ) (hσ' : 0 < σ') :
    |∫ p : ℝ × ℝ, relu (a + σ * p.1) * relu (a' + σ' * (ρ * p.1 + √(1 - ρ ^ 2) * p.2))
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) -
        psiS σ a * psiS σ' a' - ρ * σ * σ' * PhiG (a / σ) * PhiG (a' / σ')| ≤
      ρ ^ 2 * σ * σ' * √(Ures (a / σ)) * √(Ures (a' / σ')) := by
  have h := PR_unit hρ (a / σ) (a' / σ')
  have e : ∀ p : ℝ × ℝ, relu (a + σ * p.1) * relu (a' + σ' * (ρ * p.1 + √(1 - ρ ^ 2) * p.2)) =
      (σ * σ') * (relu (a / σ + p.1) * relu (a' / σ' + (ρ * p.1 + sC ρ * p.2))) := by
    intro p
    have e1 : a + σ * p.1 = σ * (a / σ + p.1) := by field_simp
    have e2 : a' + σ' * (ρ * p.1 + √(1 - ρ ^ 2) * p.2) =
        σ' * (a' / σ' + (ρ * p.1 + sC ρ * p.2)) := by
      unfold sC; field_simp
    rw [e1, e2, relu_mul_of_nonneg hσ.le, relu_mul_of_nonneg hσ'.le]
    ring
  simp_rw [e]
  rw [integral_const_mul, psiS_scale hσ, psiS_scale hσ', psiS_one, psiS_one]
  set I := ∫ p : ℝ × ℝ, relu (a / σ + p.1) * relu (a' / σ' + (ρ * p.1 + sC ρ * p.2))
    ∂((gaussianReal 0 1).prod (gaussianReal 0 1))
  have hpos : 0 < σ * σ' := mul_pos hσ hσ'
  have e3 : σ * σ' * I - σ * psiG (a / σ) * (σ' * psiG (a' / σ')) -
      ρ * σ * σ' * PhiG (a / σ) * PhiG (a' / σ') =
      (σ * σ') * (I - psiG (a / σ) * psiG (a' / σ') - ρ * (PhiG (a / σ) * PhiG (a' / σ'))) := by
    ring
  rw [e3, abs_mul, abs_of_pos hpos]
  calc σ * σ' * |I - psiG (a / σ) * psiG (a' / σ') - ρ * (PhiG (a / σ) * PhiG (a' / σ'))|
      ≤ σ * σ' * (ρ ^ 2 * √(Ures (a / σ)) * √(Ures (a' / σ'))) :=
        mul_le_mul_of_nonneg_left h hpos.le
    _ = _ := by ring

/-- **Lemma PR (i) for two linear forms of one standard Gaussian vector**, with every constant
`K ≥ sup U`. -/
theorem PRvec_of {K : ℝ} (hK : ∀ a, Ures a ≤ K) : PRvecBound K := by
  intro m g g' a a'
  have hK0 : 0 ≤ K := Ures_zero_nonneg.trans (hK 0)
  set σ := nrm g with hσd
  set σ' := nrm g' with hσd'
  set ρ := (g ⬝ᵥ g') / (σ * σ') with hρd
  have hσ0 : 0 ≤ σ := nrm_nonneg g
  have hσ0' : 0 ≤ σ' := nrm_nonneg g'
  have s1 : ∑ x, g x * g x = σ ^ 2 := by
    rw [hσd, nrm_sq]; unfold normSq; exact Finset.sum_congr rfl fun i _ => by ring
  have s4 : ∑ x, g' x * g' x = σ' ^ 2 := by
    rw [hσd', nrm_sq]; unfold normSq; exact Finset.sum_congr rfl fun i _ => by ring
  have hCS : (g ⬝ᵥ g') ^ 2 ≤ (σ * σ') ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g g'
    rw [mul_pow, hσd, hσd', nrm_sq, nrm_sq]
    exact this
  have hdot : σ * σ' * ρ = g ⬝ᵥ g' := by
    by_cases h0 : σ * σ' = 0
    · rw [h0, zero_pow two_ne_zero] at hCS
      have : g ⬝ᵥ g' = 0 := by nlinarith [sq_nonneg (g ⬝ᵥ g')]
      rw [this, h0, zero_mul]
    · rw [hρd, mul_div_assoc']; exact mul_div_cancel_left₀ _ h0
  have hρ2 : ρ ^ 2 ≤ 1 := by
    by_cases h0 : σ * σ' = 0
    · rw [hρd, h0, div_zero]; norm_num
    · rw [hρd, div_pow, div_le_one (by positivity)]; exact hCS
  have hρ : |ρ| ≤ 1 := (sq_le_one_iff_abs_le_one ρ).mp hρ2
  have hsq : √(1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by linarith)
  have s2 : ∑ x, g x * g' x = σ * σ' * ρ := by rw [hdot]; rfl
  have s3 : ∑ x, g' x * g x = σ * σ' * ρ := by
    rw [← s2]; exact Finset.sum_congr rfl fun i _ => by ring
  have law : ∫ z, relu (a + z ⬝ᵥ g) * relu (a' + z ⬝ᵥ g') ∂stdGauss (Fin m) =
      ∫ p : ℝ × ℝ, relu (a + σ * p.1) * relu (a' + σ' * (ρ * p.1 + √(1 - ρ ^ 2) * p.2))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    let A : Matrix (Fin 2) (Fin m) ℝ := Matrix.of ![g, g']
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![σ, 0; σ' * ρ, σ' * √(1 - ρ ^ 2)]
    have hAB : A * A.transpose = B * B.transpose := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [A, B, Matrix.mul_apply, Fin.sum_univ_two, s1, s2, s3, s4] <;> nlinarith
    have hl := gaussLin105 (Fin m) (Fin 2) (Fin 2) A B hAB
    let H : (Fin 2 → ℝ) → ℝ := fun y => relu (a + y 0) * relu (a' + y 1)
    have hH : Measurable H :=
      (measurable_relu.comp (measurable_const.add (measurable_pi_apply 0))).mul
        (measurable_relu.comp (measurable_const.add (measurable_pi_apply 1)))
    let G : ℝ × ℝ → ℝ := fun p =>
      relu (a + σ * p.1) * relu (a' + σ' * (ρ * p.1 + √(1 - ρ ^ 2) * p.2))
    have e1 : ∫ z, relu (a + z ⬝ᵥ g) * relu (a' + z ⬝ᵥ g') ∂stdGauss (Fin m) =
        ∫ z, H (A.mulVec z) ∂stdGauss (Fin m) := by
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp [H, A, dotProduct_comm]
    have e2 : ∫ z, H (A.mulVec z) ∂stdGauss (Fin m) =
        ∫ η, H (B.mulVec η) ∂stdGauss (Fin 2) := by
      rw [← integral_map (φ := fun ξ => A.mulVec ξ) (by fun_prop) hH.aestronglyMeasurable, hl,
        integral_map (φ := fun ξ => B.mulVec ξ) (by fun_prop) hH.aestronglyMeasurable]
    have e3 : ∫ η, H (B.mulVec η) ∂stdGauss (Fin 2) =
        ∫ p, G p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      have h := (measurePreserving_finTwoArrow (gaussianReal 0 1)).integral_comp' G
      rw [← h]
      refine integral_congr_ae (Eventually.of_forall fun η => ?_)
      show H (B.mulVec η) = G (η 0, η 1)
      have b0 : B.mulVec η 0 = σ * η 0 := by
        simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have b1 : B.mulVec η 1 = σ' * (ρ * η 0 + √(1 - ρ ^ 2) * η 1) := by
        simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        ring
      show relu (a + B.mulVec η 0) * relu (a' + B.mulVec η 1) = _
      rw [b0, b1]
    rw [e1, e2, e3]
  rw [law]
  rcases (mul_nonneg hσ0 hσ0').eq_or_lt with h0 | hpos
  · have hρ0 : ρ = 0 := by rw [hρd, ← h0, div_zero]
    have hd0 : g ⬝ᵥ g' = 0 := by rw [← hdot, hρ0, mul_zero]
    have e : ∫ p : ℝ × ℝ, relu (a + σ * p.1) * relu (a' + σ' * (ρ * p.1 + √(1 - ρ ^ 2) * p.2))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = psiS σ a * psiS σ' a' := by
      rw [hρ0]
      simp only [zero_mul, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        sub_zero, Real.sqrt_one, one_mul]
      exact integral_prod_mul (fun z => relu (a + σ * z)) (fun z => relu (a' + σ' * z))
    rw [e, hd0]
    simp
  · have hσ : 0 < σ := by
      rcases hσ0.eq_or_lt with h | h
      · rw [← h, zero_mul] at hpos; exact absurd hpos (lt_irrefl _)
      · exact h
    have hσ' : 0 < σ' := by
      rcases hσ0'.eq_or_lt with h | h
      · rw [← h, mul_zero] at hpos; exact absurd hpos (lt_irrefl _)
      · exact h
    have h := (abs_le.mp (PR_scalar hρ a a' hσ hσ')).2
    have hU : √(Ures (a / σ)) * √(Ures (a' / σ')) ≤ K := by
      calc √(Ures (a / σ)) * √(Ures (a' / σ')) ≤ √K * √K :=
            mul_le_mul (Real.sqrt_le_sqrt (hK _)) (Real.sqrt_le_sqrt (hK _)) (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)
        _ = K := Real.mul_self_sqrt hK0
    have e : K * (g ⬝ᵥ g') ^ 2 / (σ * σ') = ρ ^ 2 * σ * σ' * K := by
      rw [← hdot]; field_simp
    rw [e, ← hdot]
    have h5 : ρ ^ 2 * σ * σ' * (√(Ures (a / σ)) * √(Ures (a' / σ'))) ≤ ρ ^ 2 * σ * σ' * K :=
      mul_le_mul_of_nonneg_left hU (by positivity)
    nlinarith

end BstLean.Part154
