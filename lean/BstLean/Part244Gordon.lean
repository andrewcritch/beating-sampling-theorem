import BstLean.Part244Soft

/-! Part 244: **Gordon's min–max comparison** for finite families of linear forms of one
standard Gaussian vector. The proof interpolates along `cos θ · a + sin θ · b` and uses
Stein's identity, as in the Part 152 proof of Sudakov–Fernique. -/
namespace BstLean.Part244
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part152 (lse smx cpath cpath' cpath_dot cpath'_dot dot_update sq_dist_dot cpath_gram
  stein_coord integrable_coord integrable_dot sumabs_integrable abs_dot_le_sum)

section core

open scoped Classical

variable {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] {n : ℕ}

lemma minmax_abs_le (z : I × J → ℝ) : |minmax z| ≤ ∑ s, |z s| := by
  have hs : ∀ s, |z s| ≤ ∑ s, |z s| := fun s =>
    Finset.single_le_sum (f := fun s => |z s|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
  obtain ⟨i0⟩ := ‹Nonempty I›
  obtain ⟨j0⟩ := ‹Nonempty J›
  rw [abs_le]
  constructor
  · unfold minmax
    refine Finset.le_inf' _ _ fun i _ => ?_
    have h1 := Finset.le_sup' (fun j => z (i, j)) (Finset.mem_univ j0)
    have h2 := neg_abs_le (z (i, j0))
    have h3 := hs (i, j0)
    linarith
  · unfold minmax
    refine (Finset.inf'_le _ (Finset.mem_univ i0)).trans ?_
    exact Finset.sup'_le _ _ fun j _ => (le_abs_self _).trans (hs (i0, j))

lemma gmm_abs_le {β : ℝ} (hβ : 0 < β) (z : I × J → ℝ) :
    |gmm β z| ≤ ∑ s, |z s| + (Real.log (Fintype.card I) / β + Real.log (Fintype.card J) / β) := by
  have hI : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hJ : (1 : ℝ) ≤ Fintype.card J := by exact_mod_cast Fintype.card_pos
  have lI : 0 ≤ Real.log (Fintype.card I) / β := div_nonneg (Real.log_nonneg hI) hβ.le
  have lJ : 0 ≤ Real.log (Fintype.card J) / β := div_nonneg (Real.log_nonneg hJ) hβ.le
  have h1 := gmm_le hβ z
  have h2 := le_gmm hβ z
  have h3 := abs_le.mp (minmax_abs_le z)
  rw [abs_le]
  constructor <;> linarith [h3.1, h3.2]

lemma gmm_measurable (β : ℝ) (c : I × J → Fin (n + 1) → ℝ) :
    Measurable fun ζ : Fin (n + 1) → ℝ => gmm β (fun s => c s ⬝ᵥ ζ) := by
  simp only [gmm, rowW, lse, dotProduct]
  fun_prop

lemma gmm_integrable {β : ℝ} (hβ : 0 < β) (c : I × J → Fin (n + 1) → ℝ) :
    Integrable (fun ζ : Fin (n + 1) → ℝ => gmm β (fun s => c s ⬝ᵥ ζ)) (stdGauss (Fin (n + 1))) :=
  Integrable.mono' ((sumabs_integrable c).add (integrable_const _))
    (gmm_measurable β c).aestronglyMeasurable (ae_of_all _ fun ζ => gmm_abs_le hβ _)

lemma piW_measurable (β : ℝ) (c : I × J → Fin (n + 1) → ℝ) (s : I × J) :
    Measurable fun ζ : Fin (n + 1) → ℝ => piW β (fun s => c s ⬝ᵥ ζ) s := by
  simp only [piW, qW, pW, rowW, smx, lse, dotProduct]
  fun_prop

lemma Tm_measurable (β : ℝ) (c : I × J → Fin (n + 1) → ℝ) (s s' : I × J) :
    Measurable fun ζ : Fin (n + 1) → ℝ => Tm β (fun s => c s ⬝ᵥ ζ) s s' := by
  have hpi : ∀ s, Measurable fun ζ : Fin (n + 1) → ℝ => piW β (fun s => c s ⬝ᵥ ζ) s :=
    fun s => piW_measurable β c s
  have hq : ∀ i, Measurable fun ζ : Fin (n + 1) → ℝ => qW β (fun s => c s ⬝ᵥ ζ) i := by
    intro i
    simp only [qW, rowW, smx, lse, dotProduct]
    fun_prop
  have hp : ∀ s, Measurable fun ζ : Fin (n + 1) → ℝ => pW β (fun s => c s ⬝ᵥ ζ) s := by
    intro s
    simp only [pW, smx, dotProduct]
    fun_prop
  unfold Tm
  by_cases h : s = s'
  · by_cases h1 : s.1 = s'.1
    · simp only [if_pos h, if_pos h1]
      exact ((hpi s).sub (((measurable_const.mul (hq s.1)).mul (hp s)).mul (hp s'))).add
        ((hpi s).mul (hpi s'))
    · simp only [if_pos h, if_neg h1, sub_zero]
      exact (hpi s).add ((hpi s).mul (hpi s'))
  · by_cases h1 : s.1 = s'.1
    · simp only [if_neg h, if_pos h1, zero_sub]
      exact ((((measurable_const.mul (hq s.1)).mul (hp s)).mul (hp s')).neg).add
        ((hpi s).mul (hpi s'))
    · simp only [if_neg h, if_neg h1, sub_zero, zero_add]
      exact (hpi s).mul (hpi s')

/-- The sign of the derivative along the path (Stein's identity and the Gordon conditions). -/
lemma gordon_path_deriv_nonpos (a b : I × J → Fin (n + 1) → ℝ)
    (horth : ∀ s s', a s ⬝ᵥ b s' = 0)
    (hwithin : ∀ s s', s.1 = s'.1 → ∑ k, (b s k - b s' k) ^ 2 ≤ ∑ k, (a s k - a s' k) ^ 2)
    (hcross : ∀ s s', s.1 ≠ s'.1 → ∑ k, (a s k - a s' k) ^ 2 ≤ ∑ k, (b s k - b s' k) ^ 2)
    {β : ℝ} (hβ : 0 < β) {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2)) :
    ∫ ζ, ∑ s, piW β (fun s => cpath a b θ s ⬝ᵥ ζ) s * (cpath' a b θ s ⬝ᵥ ζ)
      ∂stdGauss (Fin (n + 1)) ≤ 0 := by
  set c := cpath a b θ with hc
  set c' := cpath' a b θ with hc'
  set p : (Fin (n + 1) → ℝ) → I × J → ℝ := fun ζ => piW β (fun s => c s ⬝ᵥ ζ) with hp
  set Φ' : I × J → Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ :=
    fun s k ζ => β * ∑ s', Tm β (fun s => c s ⬝ᵥ ζ) s s' * c s' k with hΦ'
  have hpm : ∀ s, Measurable fun ζ => p ζ s := fun s => piW_measurable β c s
  have hΦ'm : ∀ s k, Measurable (Φ' s k) := by
    intro s k
    exact measurable_const.mul (Finset.measurable_sum _ fun s' _ =>
      (Tm_measurable β c s s').mul measurable_const)
  have hpabs : ∀ ζ s, |p ζ s| ≤ 1 := fun ζ s => by
    rw [abs_of_nonneg (piW_nonneg _ _ _)]; exact piW_le_one _ _ _
  have hΦb : ∀ s k ζ, |Φ' s k ζ| ≤ 4 * β * ∑ s', |c s' k| := by
    intro s k ζ
    have hsum : |∑ s', Tm β (fun s => c s ⬝ᵥ ζ) s s' * c s' k| ≤ 4 * ∑ s', |c s' k| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun s' _ => ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_Tm_le _ _ _ _) (abs_nonneg _)
    simp only [hΦ']
    rw [abs_mul, abs_of_pos hβ]
    calc β * |∑ s', Tm β (fun s => c s ⬝ᵥ ζ) s s' * c s' k| ≤ β * (4 * ∑ s', |c s' k|) :=
          mul_le_mul_of_nonneg_left hsum hβ.le
      _ = 4 * β * ∑ s', |c s' k| := by ring
  have hst : ∀ s k, ∫ ζ, ζ k * p ζ s ∂stdGauss (Fin (n + 1)) =
      ∫ ζ, Φ' s k ζ ∂stdGauss (Fin (n + 1)) := by
    intro s k
    refine stein_coord k (hpm s) (hΦ'm s k) (fun ζ => ?_)
      (C := 1 + 4 * β * ∑ s', |c s' k|) (fun ζ => ?_) (fun ζ => ?_)
    · have hz : ∀ s', HasDerivAt (fun t => c s' ⬝ᵥ Function.update ζ k t) (c s' k) (ζ k) := by
        intro s'
        have h := ((hasDerivAt_id (ζ k)).sub_const (ζ k)).const_mul (c s' k) |>.const_add
          (c s' ⬝ᵥ ζ)
        simp only [mul_one] at h
        refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
        simp only [id]
        exact dot_update _ _ _ _
      have h := piW_hasDerivAt β hβ.ne' (z := fun t s' => c s' ⬝ᵥ Function.update ζ k t)
        (z' := fun s' => c s' k) (t := ζ k) hz s
      simp only [Function.update_eq_self] at h
      exact h
    · have : 0 ≤ 4 * β * ∑ s', |c s' k| :=
        mul_nonneg (by linarith) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      linarith [hpabs ζ s]
    · have h0 : 0 ≤ (1 : ℝ) := zero_le_one
      linarith [hΦb s k ζ]
  have i1 : ∀ s k, Integrable (fun ζ => ζ k * p ζ s) (stdGauss (Fin (n + 1))) := by
    intro s k
    refine Integrable.mono' (integrable_coord k).norm
      (((measurable_pi_apply k).mul (hpm s)).aestronglyMeasurable) (ae_of_all _ fun ζ => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (hpabs ζ s)
  have i2 : ∀ s k, Integrable (Φ' s k) (stdGauss (Fin (n + 1))) := by
    intro s k
    refine Integrable.mono' (integrable_const (4 * β * ∑ s', |c s' k|))
      (hΦ'm s k).aestronglyMeasurable (ae_of_all _ fun ζ => ?_)
    rw [Real.norm_eq_abs]
    exact hΦb s k ζ
  have e1 : ∫ ζ, ∑ s, p ζ s * (c' s ⬝ᵥ ζ) ∂stdGauss (Fin (n + 1)) =
      ∫ ζ, ∑ s, ∑ k, c' s k * Φ' s k ζ ∂stdGauss (Fin (n + 1)) := by
    have l1 : ∀ ζ, ∑ s, p ζ s * (c' s ⬝ᵥ ζ) = ∑ s, ∑ k, c' s k * (ζ k * p ζ s) := by
      intro ζ
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp_rw [l1]
    rw [integral_finsetSum _ fun s _ => integrable_finsetSum _ fun k _ => (i1 s k).const_mul _,
      integral_finsetSum _ fun s _ => integrable_finsetSum _ fun k _ => (i2 s k).const_mul _]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_finsetSum _ fun k _ => (i1 s k).const_mul _,
      integral_finsetSum _ fun k _ => (i2 s k).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_const_mul, hst s k]
  rw [e1]
  refine integral_nonpos fun ζ => ?_
  set T := Tm β (fun s => c s ⬝ᵥ ζ) with hT
  set Δ : I × J → I × J → ℝ := fun s s' => b s ⬝ᵥ b s' - a s ⬝ᵥ a s' with hΔ
  have per : ∑ s, ∑ k, c' s k * Φ' s k ζ =
      β * (Real.sin θ * Real.cos θ) * ∑ s, ∑ s', T s s' * Δ s s' := by
    have l : ∀ s, ∑ k, c' s k * Φ' s k ζ = β * ∑ s', T s s' * (c' s ⬝ᵥ c s') := by
      intro s
      simp only [hΦ', dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun k _ => by
        simp only [hT, dotProduct]; ring
    simp_rw [l]
    rw [← Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    simp only [hc, hc', cpath_gram a b horth, hΔ]
    ring
  rw [per]
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hq := quad_nonpos T Δ (fun s s' => Tm_symm _ _ s s') (fun s => Tm_row _ _ s)
    (fun s s' => by
      have hd : Δ s s + Δ s' s' - 2 * Δ s s' =
          ∑ k, (b s k - b s' k) ^ 2 - ∑ k, (a s k - a s' k) ^ 2 := by
        rw [sq_dist_dot, sq_dist_dot]; simp only [hΔ]; ring
      rw [hd]
      by_cases he : s = s'
      · subst he; simp
      by_cases h1 : s.1 = s'.1
      · exact mul_nonneg_of_nonpos_of_nonpos (Tm_same_row _ _ he h1)
          (by linarith [hwithin s s' h1])
      · exact mul_nonneg (Tm_cross_row _ _ h1) (by linarith [hcross s s' h1]))
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hβ.le (mul_nonneg hs0 hc0)) hq

/-- The comparison for the smoothed min–max. -/
lemma gordon_step (a b : I × J → Fin (n + 1) → ℝ) (horth : ∀ s s', a s ⬝ᵥ b s' = 0)
    (hwithin : ∀ s s', s.1 = s'.1 → ∑ k, (b s k - b s' k) ^ 2 ≤ ∑ k, (a s k - a s' k) ^ 2)
    (hcross : ∀ s s', s.1 ≠ s'.1 → ∑ k, (a s k - a s' k) ^ 2 ≤ ∑ k, (b s k - b s' k) ^ 2)
    {β : ℝ} (hβ : 0 < β) :
    ∫ ζ, gmm β (fun s => b s ⬝ᵥ ζ) ∂stdGauss (Fin (n + 1)) ≤
      ∫ ζ, gmm β (fun s => a s ⬝ᵥ ζ) ∂stdGauss (Fin (n + 1)) := by
  set F : ℝ → (Fin (n + 1) → ℝ) → ℝ := fun θ ζ => gmm β (fun s => cpath a b θ s ⬝ᵥ ζ) with hF
  set D : ℝ → (Fin (n + 1) → ℝ) → ℝ :=
    fun θ ζ => ∑ s, piW β (fun s => cpath a b θ s ⬝ᵥ ζ) s * (cpath' a b θ s ⬝ᵥ ζ) with hD
  set bnd : (Fin (n + 1) → ℝ) → ℝ := fun ζ => ∑ s, (|a s ⬝ᵥ ζ| + |b s ⬝ᵥ ζ|) with hbnd
  have hFd : ∀ ζ θ, HasDerivAt (fun θ => F θ ζ) (D θ ζ) θ := by
    intro ζ θ
    have hz : ∀ s, HasDerivAt (fun θ => cpath a b θ s ⬝ᵥ ζ) (cpath' a b θ s ⬝ᵥ ζ) θ := by
      intro s
      simp only [cpath_dot, cpath'_dot]
      exact ((Real.hasDerivAt_cos θ).mul_const (a s ⬝ᵥ ζ)).add
        ((Real.hasDerivAt_sin θ).mul_const (b s ⬝ᵥ ζ))
    exact gmm_hasDerivAt β hβ.ne' (z := fun θ s => cpath a b θ s ⬝ᵥ ζ) hz
  have hDb : ∀ θ ζ, |D θ ζ| ≤ bnd ζ := by
    intro θ ζ
    simp only [hD, hbnd]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [abs_mul, abs_of_nonneg (piW_nonneg _ _ _), cpath'_dot]
    have h1 : |-Real.sin θ * (a s ⬝ᵥ ζ) + Real.cos θ * (b s ⬝ᵥ ζ)| ≤
        |a s ⬝ᵥ ζ| + |b s ⬝ᵥ ζ| := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_neg]
        exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one θ)
      · rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one θ)
    exact (mul_le_of_le_one_left (abs_nonneg _) (piW_le_one _ _ _)).trans h1
  have hDm : ∀ θ, Measurable (D θ) := by
    intro θ
    simp only [hD, piW, qW, pW, rowW, smx, lse, dotProduct]
    fun_prop
  have ibnd : Integrable bnd (stdGauss (Fin (n + 1))) :=
    integrable_finsetSum _ fun s _ => (integrable_dot (a s)).abs.add (integrable_dot (b s)).abs
  have hφ : ∀ θ, HasDerivAt (fun θ => ∫ ζ, F θ ζ ∂stdGauss (Fin (n + 1)))
      (∫ ζ, D θ ζ ∂stdGauss (Fin (n + 1))) θ := fun θ =>
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ) Filter.univ_mem
      (Filter.Eventually.of_forall fun θ => (gmm_measurable β (cpath a b θ)).aestronglyMeasurable)
      (gmm_integrable hβ (cpath a b θ)) (hDm θ).aestronglyMeasurable
      (ae_of_all _ fun ζ θ _ => hDb θ ζ) ibnd (ae_of_all _ fun ζ θ _ => hFd ζ θ)).2
  have hneg : ∀ θ ∈ Icc (0 : ℝ) (π / 2), ∫ ζ, D θ ζ ∂stdGauss (Fin (n + 1)) ≤ 0 :=
    fun θ hθ => gordon_path_deriv_nonpos a b horth hwithin hcross hβ hθ
  have hanti : AntitoneOn (fun θ => ∫ ζ, F θ ζ ∂stdGauss (Fin (n + 1))) (Icc 0 (π / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 (π / 2))
      (continuous_iff_continuousAt.2 fun θ => (hφ θ).continuousAt).continuousOn
      (fun θ _ => (hφ θ).differentiableAt.differentiableWithinAt) fun θ hθ => ?_
    rw [(hφ θ).deriv]
    exact hneg θ (interior_subset hθ)
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  have h := hanti (left_mem_Icc.mpr hpi) (right_mem_Icc.mpr hpi) hpi
  simp only [hF, cpath_dot, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two,
    Real.sin_pi_div_two, one_mul, zero_mul, add_zero, zero_add] at h
  exact h

lemma minmax_measurable (c : I × J → Fin (n + 1) → ℝ) :
    Measurable fun ζ : Fin (n + 1) → ℝ => minmax (fun s => c s ⬝ᵥ ζ) := by
  unfold minmax
  have hrow : ∀ i ∈ (Finset.univ : Finset I), Continuous fun ζ : Fin (n + 1) → ℝ =>
      Finset.univ.sup' Finset.univ_nonempty (fun j => c (i, j) ⬝ᵥ ζ) := by
    intro i _
    exact Continuous.finset_sup'_apply Finset.univ_nonempty fun j _ =>
      continuous_const.dotProduct continuous_id
  exact (Continuous.finset_inf'_apply Finset.univ_nonempty hrow).measurable

lemma minmax_integrable (c : I × J → Fin (n + 1) → ℝ) :
    Integrable (fun ζ : Fin (n + 1) → ℝ => minmax (fun s => c s ⬝ᵥ ζ))
      (stdGauss (Fin (n + 1))) :=
  Integrable.mono' (sumabs_integrable c) (minmax_measurable c).aestronglyMeasurable
    (ae_of_all _ fun ζ => by rw [Real.norm_eq_abs]; exact minmax_abs_le _)

/-- **Gordon's min–max comparison** on `Fin (n + 1)`. -/
theorem gordon_fin (a b : I × J → Fin (n + 1) → ℝ) (horth : ∀ s s', a s ⬝ᵥ b s' = 0)
    (hwithin : ∀ s s', s.1 = s'.1 → ∑ k, (b s k - b s' k) ^ 2 ≤ ∑ k, (a s k - a s' k) ^ 2)
    (hcross : ∀ s s', s.1 ≠ s'.1 → ∑ k, (a s k - a s' k) ^ 2 ≤ ∑ k, (b s k - b s' k) ^ 2) :
    ∫ ζ, minmax (fun s => b s ⬝ᵥ ζ) ∂stdGauss (Fin (n + 1)) ≤
      ∫ ζ, minmax (fun s => a s ⬝ᵥ ζ) ∂stdGauss (Fin (n + 1)) := by
  have hI : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hJ : (1 : ℝ) ≤ Fintype.card J := by exact_mod_cast Fintype.card_pos
  set L := Real.log (Fintype.card I) + Real.log (Fintype.card J) with hL
  have hL0 : 0 ≤ L := add_nonneg (Real.log_nonneg hI) (Real.log_nonneg hJ)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set β : ℝ := (L + 1) / ε with hβd
  have hβ : 0 < β := div_pos (by linarith) hε
  have hle : L / β ≤ ε := by
    rw [hβd, div_div_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  have hsplit : Real.log (Fintype.card I) / β + Real.log (Fintype.card J) / β = L / β := by
    rw [hL, add_div]
  calc ∫ ζ, minmax (fun s => b s ⬝ᵥ ζ) ∂stdGauss (Fin (n + 1))
      ≤ ∫ ζ, (gmm β (fun s => b s ⬝ᵥ ζ) + Real.log (Fintype.card I) / β)
          ∂stdGauss (Fin (n + 1)) :=
        integral_mono (minmax_integrable b) ((gmm_integrable hβ b).add (integrable_const _))
          fun ζ => by have := le_gmm hβ (fun s => b s ⬝ᵥ ζ); simp only; linarith
    _ = ∫ ζ, gmm β (fun s => b s ⬝ᵥ ζ) ∂stdGauss (Fin (n + 1)) +
          Real.log (Fintype.card I) / β := by
        rw [integral_add (gmm_integrable hβ b) (integrable_const _), integral_const]
        simp
    _ ≤ ∫ ζ, gmm β (fun s => a s ⬝ᵥ ζ) ∂stdGauss (Fin (n + 1)) +
          Real.log (Fintype.card I) / β := by
        linarith [gordon_step a b horth hwithin hcross hβ]
    _ ≤ ∫ ζ, (minmax (fun s => a s ⬝ᵥ ζ) + Real.log (Fintype.card J) / β)
          ∂stdGauss (Fin (n + 1)) + Real.log (Fintype.card I) / β := by
        have hm := integral_mono (gmm_integrable hβ a)
          ((minmax_integrable a).add (integrable_const (Real.log (Fintype.card J) / β)))
          fun ζ => gmm_le hβ (fun s => a s ⬝ᵥ ζ)
        exact add_le_add_left hm _
    _ = ∫ ζ, minmax (fun s => a s ⬝ᵥ ζ) ∂stdGauss (Fin (n + 1)) + L / β := by
        rw [integral_add (minmax_integrable a) (integrable_const _), integral_const]
        simp only [probReal_univ, one_smul]
        linarith
    _ ≤ _ := by linarith

end core

/-- **Gordon's min–max comparison** for two finite families of linear forms of one standard
Gaussian vector `ζ` on `κ → ℝ`, indexed by rows `I` and columns `J`. If the families are
orthogonal (independent), the column increments of `b` inside each row are at most those of `a`,
and the increments of `a` across different rows are at most those of `b`, then
`E min_i max_j ⟨b_{ij}, ζ⟩ ≤ E min_i max_j ⟨a_{ij}, ζ⟩`. -/
theorem gordon {κ I J : Type} [Fintype κ] [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (a b : I × J → κ → ℝ) (horth : ∀ s s', a s ⬝ᵥ b s' = 0)
    (hwithin : ∀ s s', s.1 = s'.1 → ∑ k, (b s k - b s' k) ^ 2 ≤ ∑ k, (a s k - a s' k) ^ 2)
    (hcross : ∀ s s', s.1 ≠ s'.1 → ∑ k, (a s k - a s' k) ^ 2 ≤ ∑ k, (b s k - b s' k) ^ 2) :
    ∫ ζ, minmax (fun s => b s ⬝ᵥ ζ) ∂stdGauss κ ≤ ∫ ζ, minmax (fun s => a s ⬝ᵥ ζ) ∂stdGauss κ := by
  classical
  rcases h : Fintype.card κ with _ | n
  · have : IsEmpty κ := Fintype.card_eq_zero_iff.mp h
    have h0 : ∀ (c ζ : κ → ℝ), c ⬝ᵥ ζ = 0 := fun c ζ => by simp [dotProduct]
    simp only [h0]
    exact le_rfl
  · set f : Fin (n + 1) ≃ κ := (Fintype.equivFinOfCardEq h).symm with hf
    have hp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) f)
        (stdGauss (Fin (n + 1))) (stdGauss κ) :=
      measurePreserving_piCongrLeft (fun _ : κ => gaussianReal 0 1) f
    have hk : ∀ (Z : Fin (n + 1) → ℝ) (i : κ),
        (MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) f) Z i = Z (f.symm i) := by
      intro Z i
      obtain ⟨j, rfl⟩ := f.surjective i
      rw [Equiv.symm_apply_apply]
      exact Equiv.piCongrLeft_apply_apply (P := fun _ : κ => ℝ) f Z j
    have hdot : ∀ (c : κ → ℝ) (Z : Fin (n + 1) → ℝ),
        c ⬝ᵥ (MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) f) Z = (fun j => c (f j)) ⬝ᵥ Z := by
      intro c Z
      simp only [dotProduct, hk]
      rw [← Equiv.sum_comp f]
      simp
    rw [← hp.integral_comp' (fun ζ => minmax (fun s => a s ⬝ᵥ ζ)),
      ← hp.integral_comp' (fun ζ => minmax (fun s => b s ⬝ᵥ ζ))]
    simp only [hdot]
    refine gordon_fin (fun s j => a s (f j)) (fun s j => b s (f j)) (fun s s' => ?_)
      (fun s s' h1 => ?_) (fun s s' h1 => ?_)
    · have := horth s s'
      simp only [dotProduct] at this ⊢
      rw [← Equiv.sum_comp f] at this
      exact this
    · have := hwithin s s' h1
      rw [← Equiv.sum_comp f (fun k => (a s k - a s' k) ^ 2),
        ← Equiv.sum_comp f (fun k => (b s k - b s' k) ^ 2)] at this
      exact this
    · have := hcross s s' h1
      rw [← Equiv.sum_comp f (fun k => (a s k - a s' k) ^ 2),
        ← Equiv.sum_comp f (fun k => (b s k - b s' k) ^ 2)] at this
      exact this

end BstLean.Part244
