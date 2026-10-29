import BstLean.Part162Pq
import BstLean.Part153S

/-!
# Part 165 (file `Poin`): the Gaussian `L^p` Poincaré inequality for a function of the direction

No proof is left open; no `native_decide` or `axiom` is used.

`y = c + τξ`, `x = y/|y|` (`sphPt`), `ξ` standard Gaussian in `ℝⁿ`. For a Lipschitz `Φ` and a
weight `Γ` with `|∇_ξ Φ(x)|² ≤ Γ` almost everywhere:
`E|Φ(x) − EΦ(x)|^p ≤ (π/2)^p·E|g|^p·E Γ^{p/2}` (`lemmaS_grad_p`).

Route: the cut-off `Φ(cut_ε(y))` is Lipschitz (`cutF_lip` of Part 153), so Part 162's
`poincare_p` applies to it. Its gradient is the gradient of `Φ(x)` where `|y| > ε`, and at most
`Kτ/ε ≤ Kτε/|y|²` where `|y| ≤ ε`. Then `ε → 0` (dominated convergence, as in Part 153's
`lemmaS_grad`). This is the paper's Corollary `t7:p06:rotation-singular` for this `Φ`.
-/

namespace BstLean.Part165

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq sphPt normSq_nonneg normSq_sphPt measurable_sphPt)
open BstLean.Part148 (EuLip)
open BstLean.Part153 (cut cutF_lip cut_eq_sphPt cut_normSq_le cont_ns epsSeq epsSeq_pos
  epsSeq_tendsto)
open BstLean.Part162 (gmom gmom_nonneg poincare_p)

variable {n : ℕ}

/-- The pointwise gradient bound of the cut-off function (`p`-th power). -/
lemma cut_grad_pow {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ) {Φ : (Fin n → ℝ) → ℝ} {K : ℝ}
    (hK0 : 0 ≤ K) (hΦ : EuLip Φ K) {p : ℕ} {Γ : (Fin n → ℝ) → ℝ} (hΓ0 : ∀ ξ, 0 ≤ Γ ξ)
    {ε : ℝ} (hε : 0 < ε) (ξ : Fin n → ℝ)
    (hg : ∑ i, (fderiv ℝ (fun ξ => Φ (sphPt (c + τ • ξ))) ξ (Pi.single i 1)) ^ 2 ≤ Γ ξ)
    (hz : normSq (c + τ • ξ) ≠ 0) :
    √(BstLean.Part151.gradSq (fun ξ => Φ (cut ε (c + τ • ξ))) ξ) ^ p ≤
      √(Γ ξ) ^ p + (K * τ * ε) ^ p * (normSq (c + τ • ξ))⁻¹ ^ p := by
  have hs : 0 < normSq (c + τ • ξ) := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hz)
  have hR0 : 0 ≤ (K * τ * ε) ^ p * (normSq (c + τ • ξ))⁻¹ ^ p := by positivity
  have hS0 : 0 ≤ √(Γ ξ) ^ p := by positivity
  by_cases hc : ε ^ 2 < normSq (c + τ • ξ)
  · have heq : (fun ξ => Φ (cut ε (c + τ • ξ))) =ᶠ[𝓝 ξ]
        (fun ξ => Φ (sphPt (c + τ • ξ))) := by
      have hU : ∀ᶠ ξ' in 𝓝 ξ, ε ^ 2 < normSq (c + τ • ξ') :=
        (isOpen_lt continuous_const (cont_ns c τ)).mem_nhds hc
      filter_upwards [hU] with ξ' h'
      rw [cut_eq_sphPt hε ((Real.le_sqrt' hε).mpr h'.le)]
    have h1 : BstLean.Part151.gradSq (fun ξ => Φ (cut ε (c + τ • ξ))) ξ ≤ Γ ξ := by
      unfold BstLean.Part151.gradSq
      rw [heq.fderiv_eq]
      exact hg
    have h2 : √(BstLean.Part151.gradSq (fun ξ => Φ (cut ε (c + τ • ξ))) ξ) ≤ √(Γ ξ) :=
      Real.sqrt_le_sqrt h1
    have h3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 p
    linarith
  · have hL0 : 0 ≤ K * τ / ε := by positivity
    have h1 := BstLean.Part151.gradSq_le hL0 (cutF_lip c hτ hε hK0 hΦ) ξ
    have h2 : √(BstLean.Part151.gradSq (fun ξ => Φ (cut ε (c + τ • ξ))) ξ) ≤ K * τ / ε := by
      rw [← Real.sqrt_sq hL0]; exact Real.sqrt_le_sqrt h1
    have hle : normSq (c + τ • ξ) ≤ ε ^ 2 := not_lt.mp hc
    have h3 : K * τ / ε ≤ K * τ * ε * (normSq (c + τ • ξ))⁻¹ := by
      have hq : 1 ≤ ε ^ 2 / normSq (c + τ • ξ) := by rw [le_div_iff₀ hs]; linarith
      calc K * τ / ε ≤ K * τ / ε * (ε ^ 2 / normSq (c + τ • ξ)) := le_mul_of_one_le_right hL0 hq
        _ = K * τ * ε * (normSq (c + τ • ξ))⁻¹ := by field_simp
    have h4 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (h2.trans h3) p
    rw [mul_pow] at h4
    linarith

/-- **The Gaussian `L^p` Poincaré inequality for a function of the direction `x = y/|y|`**:
`E|Φ(x) − EΦ(x)|^p ≤ (π/2)^p·E|g|^p·E[Γ^{p/2}]` if `|∇_ξ Φ(x)|² ≤ Γ` almost everywhere,
`E|y|^{−2p} < ∞`, `y ≠ 0` almost surely, and `Φ` is Lipschitz. -/
theorem lemmaS_grad_p (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {Φ : (Fin n → ℝ) → ℝ} {K : ℝ}
    (hK0 : 0 ≤ K) (hΦ : EuLip Φ K) {p : ℕ} (hp : 1 ≤ p) {Γ : (Fin n → ℝ) → ℝ}
    (hΓ0 : ∀ ξ, 0 ≤ Γ ξ) (hΓ : Integrable (fun ξ => √(Γ ξ) ^ p) (stdGauss (Fin n)))
    (hgrad : ∀ᵐ ξ ∂stdGauss (Fin n),
      ∑ i, (fderiv ℝ (fun ξ => Φ (sphPt (c + τ • ξ))) ξ (Pi.single i 1)) ^ 2 ≤ Γ ξ)
    (hinv : Integrable (fun ξ : Fin n → ℝ => (normSq (c + τ • ξ))⁻¹ ^ p) (stdGauss (Fin n)))
    (hne : ∀ᵐ ξ ∂stdGauss (Fin n), normSq (c + τ • ξ) ≠ 0) :
    ∫ ξ, |Φ (sphPt (c + τ • ξ)) - ∫ ξ', Φ (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)| ^ p
        ∂stdGauss (Fin n) ≤
      (π / 2) ^ p * (gmom p * ∫ ξ, √(Γ ξ) ^ p ∂stdGauss (Fin n)) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn : 1 ≤ n := by
    by_contra hcon
    have h0 : n = 0 := by omega
    subst h0
    have hF : ∀ᵐ ξ ∂stdGauss (Fin 0), False := by
      filter_upwards [hne] with ξ h
      exact h (by simp [normSq])
    rw [eventually_false_iff_eq_bot, ae_eq_bot] at hF
    exact IsProbabilityMeasure.ne_zero _ hF
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
  have hFm : ∀ ε : ℝ, 0 < ε → Measurable (fun ξ : Fin n → ℝ => Φ (cut ε (c + τ • ξ))) :=
    fun ε hε => ((cutF_lip c hτ hε hK0 hΦ).continuous (by positivity)).measurable
  have hfm : Measurable (fun ξ : Fin n → ℝ => Φ (sphPt (c + τ • ξ))) :=
    (hΦ.continuous hK0).measurable.comp
      (measurable_sphPt.comp (measurable_const.add (measurable_id.const_smul τ)))
  have hpw : ∀ a b : ℝ, |a| ≤ C → |b| ≤ C → ‖|a - b| ^ p‖ ≤ (2 * C) ^ p := by
    intro a b ha hb
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ p
    have h1 := abs_le.mp ha
    have h2 := abs_le.mp hb
    rw [abs_le]; constructor <;> linarith
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
  have hm : Tendsto (fun j => ∫ ξ, Φ (cut (epsSeq j) (c + τ • ξ)) ∂stdGauss (Fin n)) atTop
      (𝓝 (∫ ξ, Φ (sphPt (c + τ • ξ)) ∂stdGauss (Fin n))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun j => (hFm _ (epsSeq_pos j)).aestronglyMeasurable) (integrable_const C)
      (fun j => Eventually.of_forall fun ξ => ?_) hptT
    rw [Real.norm_eq_abs]
    exact hFb _ (epsSeq_pos j) ξ
  have hV : Tendsto (fun j => ∫ ξ, |Φ (cut (epsSeq j) (c + τ • ξ)) -
        ∫ ξ', Φ (cut (epsSeq j) (c + τ • ξ')) ∂stdGauss (Fin n)| ^ p ∂stdGauss (Fin n)) atTop
      (𝓝 (∫ ξ, |Φ (sphPt (c + τ • ξ)) -
        ∫ ξ', Φ (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)| ^ p ∂stdGauss (Fin n))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (2 * C) ^ p)
      (fun j => (((hFm _ (epsSeq_pos j)).sub measurable_const).abs.pow_const p).aestronglyMeasurable)
      (integrable_const _) (fun j => Eventually.of_forall fun ξ => ?_) ?_
    · exact hpw _ _ (hFb _ (epsSeq_pos j) ξ) (hmb _ (hFb _ (epsSeq_pos j)))
    · filter_upwards [hptT] with ξ hξ
      exact ((hξ.sub hm).abs).pow p
  -- the bound at each `ε`
  have hcut : ∀ ε : ℝ, 0 < ε →
      ∫ ξ, |Φ (cut ε (c + τ • ξ)) - ∫ ξ', Φ (cut ε (c + τ • ξ')) ∂stdGauss (Fin n)| ^ p
          ∂stdGauss (Fin n) ≤
        (π / 2) ^ p * (gmom p * (∫ ξ, √(Γ ξ) ^ p ∂stdGauss (Fin n) +
          (K * τ * ε) ^ p * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ p ∂stdGauss (Fin n))) := by
    intro ε hε
    have hL0 : 0 ≤ K * τ / ε := by positivity
    have hP := poincare_p hL0 (cutF_lip c hτ hε hK0 hΦ) hp
    refine hP.trans ?_
    have hgm := gmom_nonneg p
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hgm) (by positivity)
    have hI : Integrable (fun ξ => √(Γ ξ) ^ p +
        (K * τ * ε) ^ p * (normSq (c + τ • ξ))⁻¹ ^ p) (stdGauss (Fin n)) :=
      hΓ.add (hinv.const_mul _)
    have hL : Integrable (fun ξ => √(BstLean.Part151.gradSq
        (fun ξ => Φ (cut ε (c + τ • ξ))) ξ) ^ p) (stdGauss (Fin n)) := by
      refine Integrable.of_bound
        (((BstLean.Part151.measurable_gradSq _).sqrt.pow_const p).aestronglyMeasurable)
        ((K * τ / ε) ^ p) (Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 := BstLean.Part151.gradSq_le hL0 (cutF_lip c hτ hε hK0 hΦ) ξ
      have h2 : √(BstLean.Part151.gradSq (fun ξ => Φ (cut ε (c + τ • ξ))) ξ) ≤ K * τ / ε := by
        rw [← Real.sqrt_sq hL0]; exact Real.sqrt_le_sqrt h1
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 p
    rw [← integral_const_mul, ← integral_add hΓ (hinv.const_mul _)]
    refine integral_mono_ae hL hI ?_
    filter_upwards [hgrad, hne] with ξ hg hz
    exact cut_grad_pow hτ hK0 hΦ hΓ0 hε ξ hg hz
  -- the limit
  have hB : Tendsto (fun j => (π / 2) ^ p * (gmom p * (∫ ξ, √(Γ ξ) ^ p ∂stdGauss (Fin n) +
        (K * τ * epsSeq j) ^ p * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ p ∂stdGauss (Fin n)))) atTop
      (𝓝 ((π / 2) ^ p * (gmom p * ∫ ξ, √(Γ ξ) ^ p ∂stdGauss (Fin n)))) := by
    have h0 : Tendsto (fun j => (K * τ * epsSeq j) ^ p) atTop (𝓝 ((K * τ * 0) ^ p)) :=
      ((epsSeq_tendsto.const_mul (K * τ)).pow p)
    rw [mul_zero, zero_pow (by omega)] at h0
    have h1 := ((tendsto_const_nhds (x := ∫ ξ, √(Γ ξ) ^ p ∂stdGauss (Fin n))).add
      (h0.mul_const (∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ p ∂stdGauss (Fin n)))).const_mul (gmom p)
      |>.const_mul ((π / 2) ^ p)
    simpa using h1
  exact le_of_tendsto_of_tendsto' hV hB fun j => hcut _ (epsSeq_pos j)

end BstLean.Part165
