import BstLean.Part151Poinc
import BstLean.Part130Mean

/-!
# Part 153 S: the Poincaré inequality across the point `y = 0` (Lemma S, first assertion)

Role: Lemma S of `proofs/option-n/theorem5-04-standin-structure.tex`, first assertion, for a
function of the direction `x = y/|y|`, `y = c + τ·ξ`, `ξ` a standard Gaussian vector.

* `sphPt_dist_le`: `|u/|u| − v/|v||² ≤ |u − v|²/(|u||v|)` for `u, v ≠ 0`.
* `cut ε y = y / max(|y|, ε)`: the cut-off of `y ↦ y/|y|`; it is `(1/ε)`-Lipschitz (`cut_dist`),
  it has length at most `1`, and it is `sphPt y` where `|y| ≥ ε`.
* `gradSq_le_of_local`: a local Lipschitz constant `ℓ` at `ξ` bounds the gradient: `|∇f(ξ)|² ≤ ℓ²`.
* `gradSq_sph_le`: where `y ≠ 0`, `|∇_ξ Φ(y/|y|)|² ≤ τ²K²/|y|²` for a `K`-Lipschitz `Φ`.
* **`lemmaS_grad`**: `Var_ξ Φ(y/|y|) ≤ E Γ` if `|∇_ξ Φ(y/|y|)|² ≤ Γ` almost everywhere,
  `E|y|⁻⁴ < ∞` and `y ≠ 0` almost surely.
* `lemmaS_weak`: `Var_ξ Φ(y/|y|) ≤ τ²K²·E|y|⁻²`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Filter Topology Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq sphPt e0 normSq_nonneg normSq_smul normSq_sphPt sphPt_of_ne
  measurable_sphPt)
open BstLean.Part148 (EuLip)

/-! ## §1 The algebra of the radial projection -/

/-- The sign condition of the two inequalities `|u/a − v/b|² ≤ |u − v|²/(ab)`. -/
lemma key_sign {P Q a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hP : P ≤ a ^ 2) (hQ : Q ≤ b ^ 2)
    (hab : a < b → Q = b ^ 2) (hba : b < a → P = a ^ 2) :
    0 ≤ (b - a) * (Q * a - P * b) := by
  rcases lt_trichotomy a b with h | h | h
  · have hQ' := hab h
    have h1 : 0 ≤ Q * a - P * b := by
      rw [hQ']
      have h2 : P * b ≤ a ^ 2 * b := mul_le_mul_of_nonneg_right hP hb.le
      nlinarith [mul_pos ha hb, mul_pos (mul_pos ha hb) (sub_pos.mpr h)]
    exact mul_nonneg (sub_pos.mpr h).le h1
  · subst h; simp
  · have hP' := hba h
    have h1 : Q * a - P * b ≤ 0 := by
      rw [hP']
      have h2 : Q * a ≤ b ^ 2 * a := mul_le_mul_of_nonneg_right hQ ha.le
      nlinarith [mul_pos ha hb, mul_pos (mul_pos ha hb) (sub_pos.mpr h)]
    exact mul_nonneg_of_nonpos_of_nonpos (sub_neg.mpr h).le h1

/-- `|u/a − v/b|² ≤ |u − v|²/(ab)` under the sign condition `(b − a)(|v|²a − |u|²b) ≥ 0`. -/
lemma scaled_dist {ι : Type*} [Fintype ι] (u v : ι → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : 0 ≤ (b - a) * ((∑ i, v i ^ 2) * a - (∑ i, u i ^ 2) * b)) :
    ∑ i, (a⁻¹ * u i - b⁻¹ * v i) ^ 2 ≤ (∑ i, (u i - v i) ^ 2) / (a * b) := by
  have e1 : ∑ i, (a⁻¹ * u i - b⁻¹ * v i) ^ 2 =
      a⁻¹ ^ 2 * (∑ i, u i ^ 2) + b⁻¹ ^ 2 * (∑ i, v i ^ 2) - 2 * a⁻¹ * b⁻¹ * ∑ i, u i * v i := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, (u i - v i) ^ 2 = (∑ i, u i ^ 2) + (∑ i, v i ^ 2) - 2 * ∑ i, u i * v i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  generalize (∑ i, u i ^ 2) = P at h ⊢
  generalize (∑ i, v i ^ 2) = Q at h ⊢
  generalize (∑ i, u i * v i) = R
  have hab : 0 < a * b := mul_pos ha hb
  have e3 : a⁻¹ ^ 2 * P + b⁻¹ ^ 2 * Q - 2 * a⁻¹ * b⁻¹ * R =
      (P * b ^ 2 + Q * a ^ 2 - 2 * R * (a * b)) / (a * b) / (a * b) := by
    field_simp
  rw [e3]
  have h4 : P * b ^ 2 + Q * a ^ 2 - 2 * R * (a * b) ≤ (P + Q - 2 * R) * (a * b) := by
    nlinarith [h]
  exact div_le_div_of_nonneg_right ((div_le_iff₀ hab).mpr h4) hab.le

lemma sphPt_eq' {n : ℕ} {y : Fin n → ℝ} (h : normSq y ≠ 0) :
    sphPt y = (1 / √(normSq y)) • y := by
  rw [sphPt_of_ne y h]; rfl

/-- **The radial projection, distance of two directions**: for `u, v ≠ 0`,
`|u/|u| − v/|v||² ≤ |u − v|²/(|u|·|v|)`. -/
theorem sphPt_dist_le {n : ℕ} (u v : Fin n → ℝ) (hu : normSq u ≠ 0) (hv : normSq v ≠ 0) :
    ∑ i, (sphPt u i - sphPt v i) ^ 2 ≤
      (∑ i, (u i - v i) ^ 2) / (√(normSq u) * √(normSq v)) := by
  have hu0 : 0 < normSq u := lt_of_le_of_ne (normSq_nonneg u) (Ne.symm hu)
  have hv0 : 0 < normSq v := lt_of_le_of_ne (normSq_nonneg v) (Ne.symm hv)
  have ha : 0 < √(normSq u) := Real.sqrt_pos.mpr hu0
  have hb : 0 < √(normSq v) := Real.sqrt_pos.mpr hv0
  have eu : normSq u = √(normSq u) ^ 2 := (Real.sq_sqrt hu0.le).symm
  have ev : normSq v = √(normSq v) ^ 2 := (Real.sq_sqrt hv0.le).symm
  have hk := key_sign ha hb eu.le ev.le (fun _ => ev) (fun _ => eu)
  have h := scaled_dist u v ha hb hk
  rw [sphPt_eq' hu, sphPt_eq' hv]
  simp only [Pi.smul_apply, smul_eq_mul, one_div]
  exact h

/-- The cut-off of the radial projection: `y / max(|y|, ε)`. -/
noncomputable def cut {n : ℕ} (ε : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  (1 / max (√(normSq y)) ε) • y

lemma cut_dist_aux {n : ℕ} {ε a b : ℝ} (hε : 0 < ε) (u v : Fin n → ℝ)
    (ha : a = max (√(normSq u)) ε) (hb : b = max (√(normSq v)) ε) :
    ∑ i, (a⁻¹ * u i - b⁻¹ * v i) ^ 2 ≤ (∑ i, (u i - v i) ^ 2) / ε ^ 2 := by
  have hεa : ε ≤ a := ha ▸ le_max_right _ _
  have hεb : ε ≤ b := hb ▸ le_max_right _ _
  have hsa : √(normSq u) ≤ a := ha ▸ le_max_left _ _
  have hsb : √(normSq v) ≤ b := hb ▸ le_max_left _ _
  have ha0 : 0 < a := lt_of_lt_of_le hε hεa
  have hb0 : 0 < b := lt_of_lt_of_le hε hεb
  have hPa : normSq u ≤ a ^ 2 := by
    calc normSq u = √(normSq u) ^ 2 := (Real.sq_sqrt (normSq_nonneg u)).symm
      _ ≤ a ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsa 2
  have hQb : normSq v ≤ b ^ 2 := by
    calc normSq v = √(normSq v) ^ 2 := (Real.sq_sqrt (normSq_nonneg v)).symm
      _ ≤ b ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsb 2
  have hab : a < b → normSq v = b ^ 2 := by
    intro h
    have e : b = √(normSq v) := by
      rcases max_choice (√(normSq v)) ε with h1 | h1
      · rw [hb, h1]
      · exfalso
        have : b = ε := by rw [hb, h1]
        linarith
    rw [e, Real.sq_sqrt (normSq_nonneg v)]
  have hba : b < a → normSq u = a ^ 2 := by
    intro h
    have e : a = √(normSq u) := by
      rcases max_choice (√(normSq u)) ε with h1 | h1
      · rw [ha, h1]
      · exfalso
        have : a = ε := by rw [ha, h1]
        linarith
    rw [e, Real.sq_sqrt (normSq_nonneg u)]
  have hk := key_sign ha0 hb0 hPa hQb hab hba
  have h1 := scaled_dist u v ha0 hb0 hk
  refine h1.trans ?_
  refine div_le_div_of_nonneg_left (Finset.sum_nonneg fun i _ => sq_nonneg _) (pow_pos hε 2) ?_
  nlinarith [mul_nonneg (sub_nonneg.mpr hεa) (sub_nonneg.mpr hεb)]

/-- The cut-off is `(1/ε)`-Lipschitz for the Euclidean norm. -/
lemma cut_dist {n : ℕ} {ε : ℝ} (hε : 0 < ε) (u v : Fin n → ℝ) :
    ∑ i, (cut ε u i - cut ε v i) ^ 2 ≤ (∑ i, (u i - v i) ^ 2) / ε ^ 2 := by
  have h := cut_dist_aux hε u v rfl rfl
  unfold cut
  simp only [Pi.smul_apply, smul_eq_mul, one_div]
  exact h

/-- The cut-off has length at most `1`. -/
lemma cut_normSq_le {n : ℕ} {ε : ℝ} (hε : 0 < ε) (y : Fin n → ℝ) : normSq (cut ε y) ≤ 1 := by
  have ha0 : 0 < max (√(normSq y)) ε := lt_of_lt_of_le hε (le_max_right _ _)
  have hPa : normSq y ≤ (max (√(normSq y)) ε) ^ 2 := by
    calc normSq y = √(normSq y) ^ 2 := (Real.sq_sqrt (normSq_nonneg y)).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_left _ _) 2
  unfold cut
  rw [normSq_smul, one_div, inv_pow, inv_mul_le_iff₀ (pow_pos ha0 2), mul_one]
  exact hPa

/-- The cut-off is the radial projection where `|y| ≥ ε`. -/
lemma cut_eq_sphPt {n : ℕ} {ε : ℝ} (hε : 0 < ε) {y : Fin n → ℝ} (h : ε ≤ √(normSq y)) :
    cut ε y = sphPt y := by
  have hy : normSq y ≠ 0 := by
    intro h0
    rw [h0, Real.sqrt_zero] at h
    linarith
  rw [sphPt_eq' hy]
  unfold cut
  rw [max_eq_left h]

/-! ## §2 The affine map `ξ ↦ c + τ·ξ` -/

lemma affine_sq {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (ξ ξ' : Fin n → ℝ) :
    ∑ i, ((c + τ • ξ) i - (c + τ • ξ') i) ^ 2 = τ ^ 2 * ∑ i, (ξ i - ξ' i) ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma cont_ns {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    Continuous (fun ξ : Fin n → ℝ => normSq (c + τ • ξ)) := by
  unfold normSq
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

/-- `ξ ↦ Φ(cut_ε(c + τ·ξ))` is Lipschitz with the constant `K·τ/ε`. -/
lemma cutF_lip {n : ℕ} (c : Fin n → ℝ) {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε)
    {Φ : (Fin n → ℝ) → ℝ} {K : ℝ} (hK0 : 0 ≤ K) (hΦ : EuLip Φ K) :
    EuLip (fun ξ => Φ (cut ε (c + τ • ξ))) (K * τ / ε) := by
  intro ξ ξ'
  refine (hΦ _ _).trans ?_
  have h1 := cut_dist hε (c + τ • ξ) (c + τ • ξ')
  rw [affine_sq] at h1
  have h2 : √(∑ i, (cut ε (c + τ • ξ) i - cut ε (c + τ • ξ') i) ^ 2) ≤
      τ / ε * √(∑ i, (ξ i - ξ' i) ^ 2) := by
    calc √(∑ i, (cut ε (c + τ • ξ) i - cut ε (c + τ • ξ') i) ^ 2)
        ≤ √(τ ^ 2 * (∑ i, (ξ i - ξ' i) ^ 2) / ε ^ 2) := Real.sqrt_le_sqrt h1
      _ = τ / ε * √(∑ i, (ξ i - ξ' i) ^ 2) := by
          rw [show τ ^ 2 * (∑ i, (ξ i - ξ' i) ^ 2) / ε ^ 2 =
            (τ / ε) ^ 2 * ∑ i, (ξ i - ξ' i) ^ 2 by ring, Real.sqrt_mul (sq_nonneg _),
            Real.sqrt_sq (div_pos hτ hε).le]
  calc K * √(∑ i, (cut ε (c + τ • ξ) i - cut ε (c + τ • ξ') i) ^ 2)
      ≤ K * (τ / ε * √(∑ i, (ξ i - ξ' i) ^ 2)) := mul_le_mul_of_nonneg_left h2 hK0
    _ = K * τ / ε * √(∑ i, (ξ i - ξ' i) ^ 2) := by ring

/-! ## §3 A local Lipschitz constant bounds the gradient -/

/-- **A local Lipschitz constant bounds the gradient.** If for every `δ > 0` the inequality
`|f ξ' − f ξ| ≤ (ℓ + δ)·|ξ' − ξ|` holds for every `ξ'` near `ξ`, then `|∇f(ξ)|² ≤ ℓ²`
(the gradient is `0` by convention where `f` is not differentiable). -/
theorem gradSq_le_of_local {ι : Type} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    {ξ : ι → ℝ} {ℓ : ℝ}
    (h : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ ξ' in 𝓝 ξ, |f ξ' - f ξ| ≤ (ℓ + δ) * √(∑ i, (ξ' i - ξ i) ^ 2)) :
    ∑ i, (fderiv ℝ f ξ (Pi.single i 1)) ^ 2 ≤ ℓ ^ 2 := by
  by_cases hx : DifferentiableAt ℝ f ξ
  swap
  · rw [fderiv_zero_of_not_differentiableAt hx]
    have e : ∑ i : ι, ((0 : (ι → ℝ) →L[ℝ] ℝ) (Pi.single i 1)) ^ 2 = 0 := by simp
    rw [e]
    positivity
  obtain ⟨g, hg⟩ : ∃ g : ι → ℝ, g = fun i => fderiv ℝ f ξ (Pi.single i 1) := ⟨_, rfl⟩
  have hlin : ∀ w : ι → ℝ, fderiv ℝ f ξ w = w ⬝ᵥ g := by
    intro w
    have h := (fderiv ℝ f ξ).toLinearMap.pi_apply_eq_sum_univ w
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at h
    rw [h]
    simp only [dotProduct, hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  have hgoal : ∑ i, (fderiv ℝ f ξ (Pi.single i 1)) ^ 2 = ∑ i, g i ^ 2 := by rw [hg]
  rw [hgoal]
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∑ i, g i ^ 2 := ⟨_, rfl⟩
  rw [← hG]
  have hG0 : 0 ≤ G := by rw [hG]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hGG : fderiv ℝ f ξ g = G := by
    rw [hlin g, hG]
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => (sq _).symm
  have hd : HasDerivAt (fun t : ℝ => f (ξ + t • g)) (fderiv ℝ f ξ g) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => ξ + t • g) g 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const g).const_add ξ
      simpa using this
    have h2 : HasFDerivAt f (fderiv ℝ f ξ) (ξ + (0 : ℝ) • g) := by
      simpa using hx.hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have ht := hd.tendsto_slope_zero_right
  rw [hGG] at ht
  have key : ∀ δ : ℝ, 0 < δ → G ≤ (ℓ + δ) * √G := by
    intro δ hδ
    have hcont : Tendsto (fun t : ℝ => ξ + t • g) (𝓝[>] 0) (𝓝 ξ) := by
      have hc : Continuous (fun t : ℝ => ξ + t • g) := by fun_prop
      have h0 := hc.tendsto 0
      simp only [zero_smul, add_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have hev := hcont.eventually (h δ hδ)
    refine le_of_tendsto ht ?_
    filter_upwards [hev, self_mem_nhdsWithin] with t ht1 ht0
    have ht0' : (0 : ℝ) < t := ht0
    have e : √(∑ i, ((ξ + t • g) i - ξ i) ^ 2) = t * √G := by
      have e' : ∑ i, ((ξ + t • g) i - ξ i) ^ 2 = t ^ 2 * G := by
        rw [hG, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [e', Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ht0'.le]
    rw [e] at ht1
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    have h3 := (abs_le.mp ht1).2
    rw [inv_mul_le_iff₀ ht0']
    linarith
  by_cases hGz : G = 0
  · rw [hGz]; positivity
  have hs : 0 < √G := Real.sqrt_pos.mpr (lt_of_le_of_ne hG0 (Ne.symm hGz))
  have h1 : √G ≤ ℓ := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have e : √G * √G = G := Real.mul_self_sqrt hG0
    have h2 : √G * √G ≤ (ℓ + δ) * √G := by rw [e]; exact key δ hδ
    exact le_of_mul_le_mul_right h2 hs
  calc G = √G ^ 2 := (Real.sq_sqrt hG0).symm
    _ ≤ ℓ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2

/-- Where `y = c + τ·ξ ≠ 0`, the gradient of `ξ ↦ Φ(y/|y|)` has squared length at most
`τ²K²/|y|²`, for a `K`-Lipschitz `Φ`. -/
theorem gradSq_sph_le {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) {Φ : (Fin n → ℝ) → ℝ} {K : ℝ}
    (hK0 : 0 ≤ K) (hΦ : EuLip Φ K) (ξ : Fin n → ℝ) (hy : normSq (c + τ • ξ) ≠ 0) :
    ∑ i, (fderiv ℝ (fun ξ => Φ (sphPt (c + τ • ξ))) ξ (Pi.single i 1)) ^ 2 ≤
      τ ^ 2 * K ^ 2 * (normSq (c + τ • ξ))⁻¹ := by
  have hs0 : 0 < normSq (c + τ • ξ) := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hy)
  have hsq0 : 0 < √(normSq (c + τ • ξ)) := Real.sqrt_pos.mpr hs0
  have hℓ : τ ^ 2 * K ^ 2 * (normSq (c + τ • ξ))⁻¹ =
      (K * |τ| / √(normSq (c + τ • ξ))) ^ 2 := by
    rw [div_pow, mul_pow, sq_abs, Real.sq_sqrt hs0.le]
    ring
  rw [hℓ]
  refine gradSq_le_of_local fun δ hδ => ?_
  have hc := cont_ns c τ
  have hne' : ∀ᶠ ξ' in 𝓝 ξ, normSq (c + τ • ξ') ≠ 0 := hc.continuousAt.eventually_ne hy
  have hH : ContinuousAt (fun ξ' : Fin n → ℝ =>
      K * |τ| / √(√(normSq (c + τ • ξ')) * √(normSq (c + τ • ξ)))) ξ := by
    refine ContinuousAt.div continuousAt_const ?_ ?_
    · exact (Real.continuous_sqrt.comp
        ((Real.continuous_sqrt.comp hc).mul continuous_const)).continuousAt
    · exact (Real.sqrt_pos.mpr (mul_pos hsq0 hsq0)).ne'
  have hval : K * |τ| / √(√(normSq (c + τ • ξ)) * √(normSq (c + τ • ξ))) =
      K * |τ| / √(normSq (c + τ • ξ)) := by
    rw [Real.sqrt_mul_self (Real.sqrt_nonneg _)]
  have hlt : ∀ᶠ ξ' in 𝓝 ξ, K * |τ| / √(√(normSq (c + τ • ξ')) * √(normSq (c + τ • ξ))) <
      K * |τ| / √(normSq (c + τ • ξ)) + δ := by
    have h0 : K * |τ| / √(√(normSq (c + τ • ξ)) * √(normSq (c + τ • ξ))) <
        K * |τ| / √(normSq (c + τ • ξ)) + δ := by rw [hval]; linarith
    exact hH.tendsto.eventually (gt_mem_nhds h0)
  filter_upwards [hne', hlt] with ξ' h1 h2
  refine (hΦ _ _).trans ?_
  have hd := sphPt_dist_le (c + τ • ξ') (c + τ • ξ) h1 hy
  rw [affine_sq] at hd
  have hsq : √(∑ i, (sphPt (c + τ • ξ') i - sphPt (c + τ • ξ) i) ^ 2) ≤
      |τ| * √(∑ i, (ξ' i - ξ i) ^ 2) /
        √(√(normSq (c + τ • ξ')) * √(normSq (c + τ • ξ))) := by
    calc √(∑ i, (sphPt (c + τ • ξ') i - sphPt (c + τ • ξ) i) ^ 2)
        ≤ √(τ ^ 2 * (∑ i, (ξ' i - ξ i) ^ 2) /
            (√(normSq (c + τ • ξ')) * √(normSq (c + τ • ξ)))) := Real.sqrt_le_sqrt hd
      _ = _ := by
          rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul (sq_nonneg _),
            Real.sqrt_sq_eq_abs]
  calc K * √(∑ i, (sphPt (c + τ • ξ') i - sphPt (c + τ • ξ) i) ^ 2)
      ≤ K * (|τ| * √(∑ i, (ξ' i - ξ i) ^ 2) /
          √(√(normSq (c + τ • ξ')) * √(normSq (c + τ • ξ)))) :=
        mul_le_mul_of_nonneg_left hsq hK0
    _ = K * |τ| / √(√(normSq (c + τ • ξ')) * √(normSq (c + τ • ξ))) *
          √(∑ i, (ξ' i - ξ i) ^ 2) := by ring
    _ ≤ (K * |τ| / √(normSq (c + τ • ξ)) + δ) * √(∑ i, (ξ' i - ξ i) ^ 2) :=
        mul_le_mul_of_nonneg_right h2.le (Real.sqrt_nonneg _)

/-! ## §4 Lemma S -/

/-- The sequence `ε_j = 1/(j + 1)`. -/
noncomputable def epsSeq (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

lemma epsSeq_pos (j : ℕ) : 0 < epsSeq j := by unfold epsSeq; positivity

lemma epsSeq_tendsto : Tendsto epsSeq atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The Poincaré inequality for the cut-off function, with the error term of the cut-off. -/
lemma poincare_cut {n : ℕ} (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {Φ : (Fin n → ℝ) → ℝ} {K : ℝ}
    (hK0 : 0 ≤ K) (hΦ : EuLip Φ K) {Γ : (Fin n → ℝ) → ℝ} (hΓ : Integrable Γ (stdGauss (Fin n)))
    (hgrad : ∀ᵐ ξ ∂stdGauss (Fin n),
      ∑ i, (fderiv ℝ (fun ξ => Φ (sphPt (c + τ • ξ))) ξ (Pi.single i 1)) ^ 2 ≤ Γ ξ)
    (hinv : Integrable (fun ξ : Fin n → ℝ => (normSq (c + τ • ξ))⁻¹ ^ 2) (stdGauss (Fin n)))
    (hne : ∀ᵐ ξ ∂stdGauss (Fin n), normSq (c + τ • ξ) ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∫ ξ, (Φ (cut ε (c + τ • ξ)) - ∫ ξ', Φ (cut ε (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2
        ∂stdGauss (Fin n) ≤
      ∫ ξ, Γ ξ ∂stdGauss (Fin n) +
        K ^ 2 * τ ^ 2 * ε ^ 2 * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ 2 ∂stdGauss (Fin n) := by
  have hL := cutF_lip c hτ hε hK0 hΦ
  have hL0 : 0 ≤ K * τ / ε := by positivity
  have hmain := BstLean.Part151.poincare_lip_le hL0 hL
    (Γ := fun ξ => Γ ξ + K ^ 2 * τ ^ 2 * ε ^ 2 * (normSq (c + τ • ξ))⁻¹ ^ 2)
    (hΓ.add (hinv.const_mul _)) (by
      filter_upwards [hgrad, hne] with ξ hg hz
      have hΓ0 : 0 ≤ Γ ξ := le_trans (Finset.sum_nonneg fun i _ => sq_nonneg _) hg
      have hs : 0 < normSq (c + τ • ξ) := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hz)
      by_cases hc : ε ^ 2 < normSq (c + τ • ξ)
      · have heq : (fun ξ => Φ (cut ε (c + τ • ξ))) =ᶠ[𝓝 ξ]
            (fun ξ => Φ (sphPt (c + τ • ξ))) := by
          have hU : ∀ᶠ ξ' in 𝓝 ξ, ε ^ 2 < normSq (c + τ • ξ') :=
            (isOpen_lt continuous_const (cont_ns c τ)).mem_nhds hc
          filter_upwards [hU] with ξ' h'
          rw [cut_eq_sphPt hε ((Real.le_sqrt' hε).mpr h'.le)]
        rw [heq.fderiv_eq]
        have h0 : 0 ≤ K ^ 2 * τ ^ 2 * ε ^ 2 * (normSq (c + τ • ξ))⁻¹ ^ 2 := by positivity
        linarith
      · have h1 := BstLean.Part151.gradSq_le hL0 hL ξ
        unfold BstLean.Part151.gradSq at h1
        refine h1.trans ?_
        have h2 : (ε ^ 2)⁻¹ ≤ (normSq (c + τ • ξ))⁻¹ := inv_anti₀ hs (not_lt.mp hc)
        have h3 : ((ε ^ 2)⁻¹) ^ 2 ≤ (normSq (c + τ • ξ))⁻¹ ^ 2 :=
          pow_le_pow_left₀ (by positivity) h2 2
        have h4 : (K * τ / ε) ^ 2 = K ^ 2 * τ ^ 2 * ε ^ 2 * ((ε ^ 2)⁻¹) ^ 2 := by
          field_simp
        rw [h4]
        have h5 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ K ^ 2 * τ ^ 2 * ε ^ 2 by positivity)
        linarith)
  rw [integral_add hΓ (hinv.const_mul _), integral_const_mul] at hmain
  exact hmain

/-- **Lemma S, first assertion, for a function of the direction `x = y/|y|`**, `y = c + τ·ξ`:
`Var_ξ Φ(x) ≤ E Γ` if `|∇_ξ Φ(x)|² ≤ Γ` almost everywhere, `E|y|⁻⁴ < ∞`, `y ≠ 0` almost surely,
and `Φ` is Lipschitz. The first part says that the centred square is integrable. -/
theorem lemmaS_grad {n : ℕ} (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {Φ : (Fin n → ℝ) → ℝ} {K : ℝ}
    (hK0 : 0 ≤ K) (hΦ : EuLip Φ K) {Γ : (Fin n → ℝ) → ℝ} (hΓ : Integrable Γ (stdGauss (Fin n)))
    (hgrad : ∀ᵐ ξ ∂stdGauss (Fin n),
      ∑ i, (fderiv ℝ (fun ξ => Φ (sphPt (c + τ • ξ))) ξ (Pi.single i 1)) ^ 2 ≤ Γ ξ)
    (hinv : Integrable (fun ξ : Fin n → ℝ => (normSq (c + τ • ξ))⁻¹ ^ 2) (stdGauss (Fin n)))
    (hne : ∀ᵐ ξ ∂stdGauss (Fin n), normSq (c + τ • ξ) ≠ 0) :
    Integrable (fun ξ => (Φ (sphPt (c + τ • ξ)) -
        ∫ ξ', Φ (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2) (stdGauss (Fin n)) ∧
    ∫ ξ, (Φ (sphPt (c + τ • ξ)) - ∫ ξ', Φ (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2
        ∂stdGauss (Fin n) ≤ ∫ ξ, Γ ξ ∂stdGauss (Fin n) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  -- `n ≥ 1`, because `y ≠ 0` almost surely
  have hn : 1 ≤ n := by
    by_contra hcon
    have h0 : n = 0 := by omega
    subst h0
    have hF : ∀ᵐ ξ ∂stdGauss (Fin 0), False := by
      filter_upwards [hne] with ξ h
      exact h (by simp [normSq])
    rw [eventually_false_iff_eq_bot, ae_eq_bot] at hF
    exact IsProbabilityMeasure.ne_zero _ hF
  -- the bound of `Φ` on the unit ball
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = |Φ 0| + K := ⟨_, rfl⟩
  have hΦb : ∀ x : Fin n → ℝ, normSq x ≤ 1 → |Φ x| ≤ C := by
    intro x hx
    have h := hΦ x 0
    simp only [Pi.zero_apply, sub_zero] at h
    have h1 : √(∑ i, x i ^ 2) ≤ 1 := Real.sqrt_le_one.mpr hx
    have h2 : K * √(∑ i, x i ^ 2) ≤ K * 1 := mul_le_mul_of_nonneg_left h1 hK0
    have h3 := abs_sub_abs_le_abs_sub (Φ x) (Φ 0)
    rw [hC]; linarith
  have hfb : ∀ ξ : Fin n → ℝ, |Φ (sphPt (c + τ • ξ))| ≤ C := fun ξ =>
    hΦb _ (normSq_sphPt hn _).le
  have hFb : ∀ ε : ℝ, 0 < ε → ∀ ξ : Fin n → ℝ, |Φ (cut ε (c + τ • ξ))| ≤ C := fun ε hε ξ =>
    hΦb _ (cut_normSq_le hε _)
  have hfm : Measurable (fun ξ : Fin n → ℝ => Φ (sphPt (c + τ • ξ))) :=
    (hΦ.continuous hK0).measurable.comp
      (measurable_sphPt.comp (measurable_const.add (measurable_id.const_smul τ)))
  have hFm : ∀ ε : ℝ, 0 < ε → Measurable (fun ξ : Fin n → ℝ => Φ (cut ε (c + τ • ξ))) :=
    fun ε hε => ((cutF_lip c hτ hε hK0 hΦ).continuous (by positivity)).measurable
  have hsq : ∀ a b : ℝ, |a| ≤ C → |b| ≤ C → ‖(a - b) ^ 2‖ ≤ (2 * C) ^ 2 := by
    intro a b ha hb
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := abs_le.mp ha
    have h2 := abs_le.mp hb
    apply sq_le_sq' <;> linarith
  have hmb : ∀ g : (Fin n → ℝ) → ℝ, (∀ ξ, |g ξ| ≤ C) → |∫ ξ, g ξ ∂stdGauss (Fin n)| ≤ C := by
    intro g hg
    have h := norm_integral_le_of_norm_le_const (μ := stdGauss (Fin n)) (f := g) (C := C)
      (Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact hg ξ)
    simpa using h
  -- pointwise convergence
  have hpt : ∀ ξ : Fin n → ℝ, normSq (c + τ • ξ) ≠ 0 →
      ∀ᶠ j in atTop, Φ (cut (epsSeq j) (c + τ • ξ)) = Φ (sphPt (c + τ • ξ)) := by
    intro ξ hz
    have hs : 0 < √(normSq (c + τ • ξ)) :=
      Real.sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hz))
    filter_upwards [epsSeq_tendsto.eventually (gt_mem_nhds hs)] with j hj
    rw [cut_eq_sphPt (epsSeq_pos j) hj.le]
  have hptT : ∀ᵐ ξ ∂stdGauss (Fin n), Tendsto (fun j => Φ (cut (epsSeq j) (c + τ • ξ))) atTop
      (𝓝 (Φ (sphPt (c + τ • ξ)))) := by
    filter_upwards [hne] with ξ hz
    exact Tendsto.congr' ((hpt ξ hz).mono fun j h => h.symm) tendsto_const_nhds
  -- convergence of the means
  have hm : Tendsto (fun j => ∫ ξ, Φ (cut (epsSeq j) (c + τ • ξ)) ∂stdGauss (Fin n)) atTop
      (𝓝 (∫ ξ, Φ (sphPt (c + τ • ξ)) ∂stdGauss (Fin n))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun j => (hFm _ (epsSeq_pos j)).aestronglyMeasurable) (integrable_const C)
      (fun j => Eventually.of_forall fun ξ => ?_) hptT
    rw [Real.norm_eq_abs]
    exact hFb _ (epsSeq_pos j) ξ
  -- convergence of the variances
  have hV : Tendsto (fun j => ∫ ξ, (Φ (cut (epsSeq j) (c + τ • ξ)) -
        ∫ ξ', Φ (cut (epsSeq j) (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n)) atTop
      (𝓝 (∫ ξ, (Φ (sphPt (c + τ • ξ)) -
        ∫ ξ', Φ (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (2 * C) ^ 2)
      (fun j => (((hFm _ (epsSeq_pos j)).sub measurable_const).pow_const 2).aestronglyMeasurable)
      (integrable_const _) (fun j => Eventually.of_forall fun ξ => ?_) ?_
    · exact hsq _ _ (hFb _ (epsSeq_pos j) ξ) (hmb _ (hFb _ (epsSeq_pos j)))
    · filter_upwards [hptT] with ξ hξ
      exact (hξ.sub hm).pow 2
  -- the bounds
  have hB : Tendsto (fun j => ∫ ξ, Γ ξ ∂stdGauss (Fin n) +
        K ^ 2 * τ ^ 2 * epsSeq j ^ 2 * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ 2 ∂stdGauss (Fin n)) atTop
      (𝓝 (∫ ξ, Γ ξ ∂stdGauss (Fin n))) := by
    have h := (tendsto_const_nhds (x := ∫ ξ, Γ ξ ∂stdGauss (Fin n)) (f := atTop (α := ℕ))).add
      ((((epsSeq_tendsto.pow 2).const_mul (K ^ 2 * τ ^ 2)).mul_const
        (∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ 2 ∂stdGauss (Fin n))))
    have e : ∫ ξ, Γ ξ ∂stdGauss (Fin n) +
        K ^ 2 * τ ^ 2 * 0 ^ 2 * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ 2 ∂stdGauss (Fin n) =
        ∫ ξ, Γ ξ ∂stdGauss (Fin n) := by ring
    rw [e] at h
    exact h
  refine ⟨?_, ?_⟩
  · refine Integrable.of_bound ((hfm.sub measurable_const).pow_const 2).aestronglyMeasurable
      ((2 * C) ^ 2) (Eventually.of_forall fun ξ => ?_)
    exact hsq _ _ (hfb ξ) (hmb _ hfb)
  · exact le_of_tendsto_of_tendsto' hV hB fun j =>
      poincare_cut c hτ hK0 hΦ hΓ hgrad hinv hne (epsSeq_pos j)

/-- **Lemma S from the global Lipschitz constant alone**: `Var_ξ Φ(y/|y|) ≤ τ²K²·E|y|⁻²`. -/
theorem lemmaS_weak {n : ℕ} (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {Φ : (Fin n → ℝ) → ℝ} {K : ℝ}
    (hK0 : 0 ≤ K) (hΦ : EuLip Φ K)
    (hinv : Integrable (fun ξ : Fin n → ℝ => (normSq (c + τ • ξ))⁻¹ ^ 2) (stdGauss (Fin n)))
    (hinv1 : Integrable (fun ξ : Fin n → ℝ => (normSq (c + τ • ξ))⁻¹) (stdGauss (Fin n)))
    (hne : ∀ᵐ ξ ∂stdGauss (Fin n), normSq (c + τ • ξ) ≠ 0) :
    ∫ ξ, (Φ (sphPt (c + τ • ξ)) - ∫ ξ', Φ (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2
        ∂stdGauss (Fin n) ≤
      τ ^ 2 * K ^ 2 * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ∂stdGauss (Fin n) := by
  have h := (lemmaS_grad c hτ hK0 hΦ
    (Γ := fun ξ => τ ^ 2 * K ^ 2 * (normSq (c + τ • ξ))⁻¹) (hinv1.const_mul _)
    (by
      filter_upwards [hne] with ξ hz
      exact gradSq_sph_le c τ hK0 hΦ ξ hz) hinv hne).2
  rwa [integral_const_mul] at h

/-- `y = c + τ·ξ ≠ 0` almost surely, for `n ≥ 1` and `τ ≠ 0`. -/
theorem ae_normSq_ne {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : τ ≠ 0) :
    ∀ᵐ ξ ∂stdGauss (Fin n), normSq (c + τ • ξ) ≠ 0 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have h0 : stdGauss (Fin n) {(-τ⁻¹) • c} = 0 := by unfold stdGauss; exact measure_singleton _
  have h1 : ∀ᵐ ξ ∂stdGauss (Fin n), ξ ∉ ({(-τ⁻¹) • c} : Set (Fin n → ℝ)) :=
    compl_mem_ae_iff.mpr h0
  filter_upwards [h1] with ξ hξ hz
  apply hξ
  unfold normSq at hz
  rw [Set.mem_singleton_iff]
  funext i
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hz i
    (Finset.mem_univ i)
  have h3 : (c + τ • ξ) i = 0 := (pow_eq_zero_iff two_ne_zero).mp h2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h3 ⊢
  field_simp
  linarith

end BstLean.Part153

#print axioms BstLean.Part153.sphPt_dist_le
#print axioms BstLean.Part153.gradSq_le_of_local
#print axioms BstLean.Part153.gradSq_sph_le
#print axioms BstLean.Part153.lemmaS_grad
#print axioms BstLean.Part153.lemmaS_weak
#print axioms BstLean.Part153.ae_normSq_ne
