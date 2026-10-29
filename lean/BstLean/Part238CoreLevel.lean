import BstLean.Part238Basic

/-! Part 238: the sharp core level of Lemma `t7:p04:schur` with Lemma `t7:p04:MS`.
The core good pairs that are core kernel pairs carry the three TI mode bounds.
The other core good pairs carry the wide operator bound `n λ₀`.
The tangential gain `χ` enters only after integration. -/
namespace BstLean.Part238
open MeasureTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part182 BstLean.Part208
open BstLean.Part153 (nrm nrm_nonneg nrm_sq abs_dot_le_nrm projT jacT)
open BstLean.Part151 (jac)

lemma sq4 {s1 s2 w1 w2 y z : ℝ} (h1 : s1 * s1 = w1) (h2 : s2 * s2 = w2) :
    s2 * (s1 * y) * (s1 * (s2 * z)) = w1 * w2 * (y * z) := by
  rw [← h1, ← h2]; ring

/-- **Sharp core level.** Input distribution `stdGauss (Fin (d+1))`, centre `c = a u`,
scale `τ`, core input set `Ω = OmegaS c t₀ z₀`. On the core good pairs `G ⊆ Ω²` that lie in
the core kernel set `C`, the three mode bounds hold; on the other pairs of `G` the wide
operator bound `n λ₀` holds. Then the core contribution is bounded by
`n min(kE + 2 ko √χ + ks χ, λ₁) E_w + n λ₀ W P_p + (H^{1/2} A₄)^{1/2}`. -/
theorem core_level_sharp {d m : ℕ} (hd : 5 ≤ d)
    (A₁ : Matrix (Fin m) (Fin (d + 1)) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (u : Fin (d + 1) → ℝ) (hu : normSq u = 1) {a τ t0 z0 cp sm : ℝ}
    (ha : 0 < a) (hτ : 0 < τ) (ht : 0 ≤ t0)
    (hR : 0 < axialRadiusLower (d + 1) a τ t0 z0) (hcp : cp ^ 2 < 1) (hsm1 : sm ≤ 1)
    (hsm : ∀ ξ ∈ OmegaS (a • u) t0 z0, sm ≤ (u ⬝ᵥ sphPt (a • u + τ • ξ)) ^ 2)
    (C G : Set ((Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)))
    (hCm : MeasurableSet C) (hGm : MeasurableSet G)
    (hCs : ∀ p ∈ C, p.swap ∈ C) (hGs : ∀ p ∈ G, p.swap ∈ G)
    (hGΩ : G ⊆ OmegaS (a • u) t0 z0 ×ˢ OmegaS (a • u) t0 z0)
    {kE ko ks lam₀ : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks) (hl₀ : 0 ≤ lam₀)
    (hmode : ∀ p ∈ G ∩ C, ModeBounds (jac A₁ A₂ (sphPt (a • u + τ • p.1)))
      (jac A₁ A₂ (sphPt (a • u + τ • p.2))) kE ko ks cp
      (sphPt (a • u + τ • p.1)) (sphPt (a • u + τ • p.2)))
    (hwide : ∀ p ∈ G, p ∉ C →
      opN ((BJ A₁ A₂ (a • u) τ p.1)ᵀ * BJ A₁ A₂ (a • u) τ p.2) ≤ ((d + 1 : ℕ) : ℝ) * lam₀)
    {W Pp : ℝ} (hW0 : 0 ≤ W) (hW : ∀ ξ ∈ OmegaS (a • u) t0 z0, wN (a • u) τ ξ ≤ W)
    (hPp : ∀ ξ, (stdGauss (Fin (d + 1))).real
      {ξ' | ξ' ∈ OmegaS (a • u) t0 z0 ∧ (ξ, ξ') ∉ C} ≤ Pp)
    (v : Fin m → ℝ) :
    ∫ ξ, (OmegaS (a • u) t0 z0).indicator (wN (a • u) τ) ξ *
        normSq (vecMul v (BJ A₁ A₂ (a • u) τ ξ)) ∂stdGauss (Fin (d + 1)) ≤
      (((d + 1 : ℕ) : ℝ) * min
          (sharpK kE ko ks ((axialPlaneUpper (d + 1) a τ t0 z0 * (1 - sm) + 1 / (d : ℝ)) /
            (1 - cp ^ 2))) (ta_lam kE ko ks) *
          (∫ ξ, wN (a • u) τ ξ ∂stdGauss (Fin (d + 1))) +
        ((d + 1 : ℕ) : ℝ) * lam₀ * W * Pp +
        √(√(((stdGauss (Fin (d + 1))).prod (stdGauss (Fin (d + 1)))).real
          (Gᶜ ∩ OmegaS (a • u) t0 z0 ×ˢ OmegaS (a • u) t0 z0)) * A4 A₁ A₂ (a • u) τ)) *
        normSq v := by
  classical
  haveI : IsProbabilityMeasure (stdGauss (Fin (d + 1))) := by unfold stdGauss; infer_instance
  set μ := stdGauss (Fin (d + 1)) with hμ
  set c : Fin (d + 1) → ℝ := a • u with hc
  set Ω := OmegaS c t0 z0 with hΩd
  set w := wN c τ with hwd
  set B := BJ A₁ A₂ c τ with hBd
  set X : (Fin (d + 1) → ℝ) → Fin (d + 1) → ℝ := fun ξ => sphPt (c + τ • ξ) with hXd
  set wt := Ω.indicator w with hwtd
  set χ := (axialPlaneUpper (d + 1) a τ t0 z0 * (1 - sm) + 1 / (d : ℝ)) / (1 - cp ^ 2)
    with hχd
  set nR : ℝ := ((d + 1 : ℕ) : ℝ) with hnR
  have hn0 : 0 ≤ nR := Nat.cast_nonneg _
  have hΩm : MeasurableSet Ω := measurableSet_OmegaS c t0 z0
  have hwm : Measurable w := measurable_wN c τ
  have hw0 : ∀ ξ, 0 ≤ w ξ := wN_nonneg c τ
  have hwi : Integrable w μ := integrable_wN (by omega) c hτ
  have hwtm : Measurable wt := hwm.indicator hΩm
  have hwt0 : ∀ ξ, 0 ≤ wt ξ := fun ξ => indicator_nonneg (fun _ _ => hw0 _) ξ
  have hwtle : ∀ ξ, wt ξ ≤ w ξ := fun ξ => indicator_le_self' (fun _ _ => hw0 _) ξ
  have hwti : Integrable wt μ := hwi.indicator hΩm
  have hwt2 : Integrable (fun ξ => wt ξ ^ 2) μ := by
    refine Integrable.mono' (integrable_wN2 (by omega) c hτ) (hwtm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hwt0 ξ) (hwtle ξ) 2
  have hwtΩ : ∀ ξ ∈ Ω, wt ξ = w ξ := fun ξ hξ => indicator_of_mem hξ _
  have hχ : 0 ≤ χ := chi_nonneg hR hcp hsm1
  have hK0 : 0 ≤ sharpK kE ko ks χ := sharpK_nonneg hkE hko hks hχ
  have hL0 : 0 ≤ ta_lam kE ko ks := ta_lam_nonneg hkE hks
  have hEw0 : 0 ≤ ∫ ξ, w ξ ∂μ := integral_nonneg hw0
  have hPp0 : 0 ≤ Pp := (measureReal_nonneg).trans (hPp 0)
  have hXm : Measurable X := measurable_sphPt.comp (by fun_prop)
  have hXu : ∀ ξ, normSq (X ξ) = 1 := fun ξ => normSq_sphPt (by omega) _
  set R : ℝ := nR * min (sharpK kE ko ks χ) (ta_lam kE ko ks) * (∫ ξ, w ξ ∂μ) +
    nR * lam₀ * W * Pp with hRd
  have hR0 : 0 ≤ R := by
    have : 0 ≤ min (sharpK kE ko ks χ) (ta_lam kE ko ks) := le_min hK0 hL0
    exact add_nonneg (mul_nonneg (mul_nonneg hn0 this) hEw0)
      (mul_nonneg (mul_nonneg (mul_nonneg hn0 hl₀) hW0) hPp0)
  have hgood : ∀ v : Fin m → ℝ,
      (∫ p in G, wt p.1 * wt p.2 *
        ((B p.1 *ᵥ vecMul v (B p.1)) ⬝ᵥ (B p.2 *ᵥ vecMul v (B p.2))) ∂μ.prod μ) ≤
        R * ∫ ξ, wt ξ * normSq (vecMul v (B ξ)) ∂μ := by
    intro v
    set f : (Fin (d + 1) → ℝ) → Fin (d + 1) → ℝ := fun ξ => vecMul v (B ξ) with hfd
    set ft : (Fin (d + 1) → ℝ) → Fin (d + 1) → ℝ := fun ξ => √(wt ξ) • f ξ with hftd
    have hfm : ∀ j, Measurable (fun ξ => f ξ j) := by
      intro j
      show Measurable (fun ξ => ∑ i, v i * B ξ i j)
      exact Finset.measurable_sum _ fun i _ => measurable_const.mul
        (measurable_BJ_entry A₁ A₂ c τ i j)
    have hftm : Measurable ft := by
      apply Measurable.of_eval
      intro j
      show Measurable (fun ξ => √(wt ξ) * f ξ j)
      exact hwtm.sqrt.mul (hfm j)
    have hfperp : ∀ ξ, X ξ ⬝ᵥ f ξ = 0 := fun ξ => dot_vecMul_jacT A₁ A₂ (hXu ξ) v
    have hft : ∀ ξ, X ξ ⬝ᵥ ft ξ = 0 := by
      intro ξ
      simp only [hftd, dotProduct_smul, hfperp ξ, smul_zero]
    have hnft : ∀ ξ, normSq (ft ξ) = wt ξ * normSq (f ξ) := fun ξ =>
      normSq_smul_sqrt (hwt0 ξ) (f ξ)
    have hnrmft : ∀ ξ, nrm (ft ξ) = √(wt ξ) * nrm (f ξ) := fun ξ => nrm_smul_sqrt _ _
    have hFm : Measurable (fun ξ => normSq (ft ξ)) := by
      unfold normSq; fun_prop
    have hQ : ∫ ξ, normSq (ft ξ) ∂μ = ∫ ξ, wt ξ * normSq (f ξ) ∂μ :=
      integral_congr_ae (ae_of_all _ hnft)
    have hFi : Integrable (fun ξ => normSq (ft ξ)) μ := by
      have hl := integrable_level A₁ A₂ c (by omega) hτ Ω hΩm v
      exact hl.congr (ae_of_all _ fun ξ => (hnft ξ).symm)
    set H := G ∩ C with hHd
    have hHm : MeasurableSet H := hGm.inter hCm
    have hHΩ : H ⊆ Ω ×ˢ Ω := fun p hp => hGΩ hp.1
    have hHs : ∀ p ∈ H, p.swap ∈ H := fun p hp => ⟨hGs p hp.1, hCs p hp.2⟩
    set Dset := G \ C with hDsetd
    have hDm : MeasurableSet Dset := hGm.diff hCm
    have hDs : ∀ p ∈ Dset, p.swap ∈ Dset := fun p hp =>
      ⟨hGs p hp.1, fun h => hp.2 (by simpa using hCs _ h)⟩
    have hcH : ∀ p ∈ H, (X p.1 ⬝ᵥ X p.2) ^ 2 ≤ cp ^ 2 := fun p hp => (hmode p hp).1
    -- the three pair factors
    set Af := fullPairFactor w ft H with hAfd
    set Cf := tangentPairFactor w X ft H with hCfd
    set Df := fullPairFactor wt ft Dset with hDfd
    have hAm : Measurable Af := by
      apply Measurable.indicator _ hHm
      apply (hwm.comp measurable_snd).sqrt.mul
      unfold nrm normSq
      fun_prop
    have hCm' : Measurable Cf := by
      apply Measurable.indicator _ hHm
      apply (hwm.comp measurable_snd).sqrt.mul
      unfold eTan dotProduct
      fun_prop
    have hDfm : Measurable Df := by
      apply Measurable.indicator _ hDm
      apply (hwtm.comp measurable_snd).sqrt.mul
      unfold nrm normSq
      fun_prop
    have hden : 0 < 1 - cp ^ 2 := by linarith
    have hAsq : ∀ p, Af p ^ 2 ≤ normSq (ft p.1) * w p.2 := by
      intro p
      rw [hAfd, fullPairFactor_sq w ft H hw0]
      by_cases hp : p ∈ H
      · rw [indicator_of_mem hp]; exact le_of_eq (mul_comm _ _)
      · rw [indicator_of_notMem hp]; exact mul_nonneg (normSq_nonneg _) (hw0 _)
    have hCsq : ∀ p, Cf p ^ 2 ≤ (normSq (ft p.1) * w p.2) / (1 - cp ^ 2) := by
      intro p
      rw [hCfd, tangentPairFactor_sq w X ft H hw0]
      by_cases hp : p ∈ H
      · rw [indicator_of_mem hp]
        have hdot := pow_le_pow_left₀ (abs_nonneg _) (abs_dot_le_nrm (X p.2) (ft p.1)) 2
        rw [sq_abs, mul_pow, nrm_sq, nrm_sq, hXu, one_mul] at hdot
        have he := (tangent_pair_sq (hft p.1) hcp (hcH p hp)).trans
          (div_le_div_of_nonneg_right hdot hden.le)
        have h := mul_le_mul_of_nonneg_left he (hw0 p.2)
        convert h using 1 <;> ring
      · rw [indicator_of_notMem hp]
        exact div_nonneg (mul_nonneg (normSq_nonneg _) (hw0 _)) hden.le
    have hDsq : ∀ p, Df p ^ 2 ≤ normSq (ft p.1) * w p.2 := by
      intro p
      rw [hDfd, fullPairFactor_sq wt ft Dset hwt0]
      by_cases hp : p ∈ Dset
      · rw [indicator_of_mem hp, mul_comm]
        exact mul_le_mul_of_nonneg_left (hwtle _) (normSq_nonneg _)
      · rw [indicator_of_notMem hp]; exact mul_nonneg (normSq_nonneg _) (hw0 _)
    have hFw : Integrable (fun p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ) =>
        normSq (ft p.1) * w p.2) (μ.prod μ) := hFi.mul_prod hwi
    have hAi : Integrable (fun p => Af p ^ 2) (μ.prod μ) := by
      refine Integrable.mono' hFw (hAm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun p => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hAsq p
    have hCi : Integrable (fun p => Cf p ^ 2) (μ.prod μ) := by
      refine Integrable.mono' (hFw.div_const (1 - cp ^ 2)) (hCm'.pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hCsq p
    have hDi : Integrable (fun p => Df p ^ 2) (μ.prod μ) := by
      refine Integrable.mono' hFw (hDfm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun p => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hDsq p
    have hsw : ∀ (g : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ) → ℝ), Measurable g →
        Integrable (fun p => g p ^ 2) (μ.prod μ) →
        Measurable (fun p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ) => g p.swap) ∧
          Integrable (fun p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ) => g p.swap ^ 2)
            (μ.prod μ) :=
      fun _ hg hgi => ⟨hg.comp measurable_swap, hgi.swap⟩
    obtain ⟨hAsm, hAsi⟩ := hsw _ hAm hAi
    obtain ⟨hCsm, hCsi⟩ := hsw _ hCm' hCi
    obtain ⟨hDsm, hDsi⟩ := hsw _ hDfm hDi
    have iAA := integrable_mul_of_sq hAm hAsm hAi hAsi
    have iCA := integrable_mul_of_sq hCm' hAsm hCi hAsi
    have iAC := integrable_mul_of_sq hAm hCsm hAi hCsi
    have iCC := integrable_mul_of_sq hCm' hCsm hCi hCsi
    have iDD := integrable_mul_of_sq hDfm hDsm hDi hDsi
    have hA0 : ∀ p, 0 ≤ Af p := fun p => indicator_nonneg
      (fun q _ => mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg _)) p
    have hC0 : ∀ p, 0 ≤ Cf p := fun p => indicator_nonneg
      (fun q _ => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) p
    have hD0 : ∀ p, 0 ≤ Df p := fun p => indicator_nonneg
      (fun q _ => mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg _)) p
    -- the integrand on good pairs
    set T : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ) → ℝ := G.indicator (fun p =>
      wt p.1 * wt p.2 * ((B p.1 *ᵥ f p.1) ⬝ᵥ (B p.2 *ᵥ f p.2))) with hTd
    have hBfm : ∀ i, Measurable (fun ξ => (B ξ *ᵥ f ξ) i) := by
      intro i
      show Measurable (fun ξ => ∑ j, B ξ i j * f ξ j)
      exact Finset.measurable_sum _ fun j _ => (measurable_BJ_entry A₁ A₂ c τ i j).mul (hfm j)
    have hTm : Measurable T := by
      apply Measurable.indicator _ hGm
      refine ((hwtm.comp measurable_fst).mul (hwtm.comp measurable_snd)).mul ?_
      show Measurable (fun p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ) =>
        ∑ i, (B p.1 *ᵥ f p.1) i * (B p.2 *ᵥ f p.2) i)
      exact Finset.measurable_sum _ fun i _ =>
        ((hBfm i).comp measurable_fst).mul ((hBfm i).comp measurable_snd)
    -- pointwise values of the factors
    have hvalC : ∀ p ∈ G, p ∈ C →
        Af p * Af p.swap = wt p.1 * wt p.2 * (nrm (f p.1) * nrm (f p.2)) ∧
        Cf p * Af p.swap = wt p.1 * wt p.2 * (|eTan (X p.1) (X p.2) ⬝ᵥ f p.1| * nrm (f p.2)) ∧
        Af p * Cf p.swap = wt p.1 * wt p.2 * (nrm (f p.1) * |eTan (X p.2) (X p.1) ⬝ᵥ f p.2|) ∧
        Cf p * Cf p.swap = wt p.1 * wt p.2 *
          (|eTan (X p.1) (X p.2) ⬝ᵥ f p.1| * |eTan (X p.2) (X p.1) ⬝ᵥ f p.2|) ∧
        Df p * Df p.swap = 0 := by
      intro p hpG hpC
      have hp1 : p.1 ∈ Ω := (hGΩ hpG).1
      have hp2 : p.2 ∈ Ω := (hGΩ hpG).2
      have s1 : √(wt p.1) * √(wt p.1) = wt p.1 := Real.mul_self_sqrt (hwt0 _)
      have s2 : √(wt p.2) * √(wt p.2) = wt p.2 := Real.mul_self_sqrt (hwt0 _)
      have e1 : w p.1 = wt p.1 := (hwtΩ _ hp1).symm
      have e2 : w p.2 = wt p.2 := (hwtΩ _ hp2).symm
      have et1 : |eTan (X p.1) (X p.2) ⬝ᵥ ft p.1| =
          √(wt p.1) * |eTan (X p.1) (X p.2) ⬝ᵥ f p.1| := by
        simp only [hftd, dotProduct_smul, smul_eq_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      have et2 : |eTan (X p.2) (X p.1) ⬝ᵥ ft p.2| =
          √(wt p.2) * |eTan (X p.2) (X p.1) ⬝ᵥ f p.2| := by
        simp only [hftd, dotProduct_smul, smul_eq_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hpH : p ∈ H := ⟨hpG, hpC⟩
      have hsH : p.swap ∈ H := hHs p hpH
      have hpD : p ∉ Dset := fun h => h.2 hpC
      have hA1 : Af p = √(wt p.2) * (√(wt p.1) * nrm (f p.1)) := by
        simp only [hAfd, fullPairFactor, indicator_of_mem hpH, hnrmft, e2]
      have hA2 : Af p.swap = √(wt p.1) * (√(wt p.2) * nrm (f p.2)) := by
        simp only [hAfd, fullPairFactor, indicator_of_mem hsH, hnrmft, Prod.fst_swap,
          Prod.snd_swap, e1]
      have hC1 : Cf p = √(wt p.2) * (√(wt p.1) * |eTan (X p.1) (X p.2) ⬝ᵥ f p.1|) := by
        simp only [hCfd, tangentPairFactor, indicator_of_mem hpH, e2]
        rw [et1]
      have hC2 : Cf p.swap = √(wt p.1) * (√(wt p.2) * |eTan (X p.2) (X p.1) ⬝ᵥ f p.2|) := by
        simp only [hCfd, tangentPairFactor, indicator_of_mem hsH, Prod.fst_swap,
          Prod.snd_swap, e1]
        rw [et2]
      have hD1 : Df p = 0 := by simp only [hDfd, fullPairFactor, indicator_of_notMem hpD]
      refine ⟨?_, ?_, ?_, ?_, by rw [hD1, zero_mul]⟩
      · rw [hA1, hA2]; exact sq4 s1 s2
      · rw [hC1, hA2]; exact sq4 s1 s2
      · rw [hA1, hC2]; exact sq4 s1 s2
      · rw [hC1, hC2]; exact sq4 s1 s2
    have hvalD : ∀ p ∈ G, p ∉ C →
        Af p = 0 ∧ Cf p = 0 ∧ Af p.swap = 0 ∧ Cf p.swap = 0 ∧
        Df p * Df p.swap = wt p.1 * wt p.2 * (nrm (f p.1) * nrm (f p.2)) := by
      intro p hpG hpC
      have s1 : √(wt p.1) * √(wt p.1) = wt p.1 := Real.mul_self_sqrt (hwt0 _)
      have s2 : √(wt p.2) * √(wt p.2) = wt p.2 := Real.mul_self_sqrt (hwt0 _)
      have hpH : p ∉ H := fun h => hpC h.2
      have hsH : p.swap ∉ H := fun h => hpH (by simpa using hHs _ h)
      have hpD : p ∈ Dset := ⟨hpG, hpC⟩
      have hsD : p.swap ∈ Dset := hDs p hpD
      refine ⟨by simp only [hAfd, fullPairFactor, indicator_of_notMem hpH],
        by simp only [hCfd, tangentPairFactor, indicator_of_notMem hpH],
        by simp only [hAfd, fullPairFactor, indicator_of_notMem hsH],
        by simp only [hCfd, tangentPairFactor, indicator_of_notMem hsH], ?_⟩
      have hD1 : Df p = √(wt p.2) * (√(wt p.1) * nrm (f p.1)) := by
        simp only [hDfd, fullPairFactor, indicator_of_mem hpD, hnrmft]
      have hD2 : Df p.swap = √(wt p.1) * (√(wt p.2) * nrm (f p.2)) := by
        simp only [hDfd, fullPairFactor, indicator_of_mem hsD, hnrmft, Prod.fst_swap,
          Prod.snd_swap]
      rw [hD1, hD2]; exact sq4 s1 s2
    -- pointwise bounds
    have hw12 : ∀ p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ), 0 ≤ wt p.1 * wt p.2 :=
      fun p => mul_nonneg (hwt0 _) (hwt0 _)
    have hBf : ∀ ξ, B ξ *ᵥ f ξ = jac A₁ A₂ (X ξ) *ᵥ f ξ := fun ξ =>
      jacT_mulVec_of_perp A₁ A₂ (hfperp ξ)
    have hwideP : ∀ p ∈ G, p ∉ C → |(B p.1 *ᵥ f p.1) ⬝ᵥ (B p.2 *ᵥ f p.2)| ≤
        nR * lam₀ * (nrm (f p.1) * nrm (f p.2)) := by
      intro p hpG hpC
      rw [ms_bil]
      exact (ms_abs_bil_le_opN _ _ _).trans
        (mul_le_mul_of_nonneg_right (hwide p hpG hpC) (mul_nonneg (nrm_nonneg _) (nrm_nonneg _)))
    have P1 : ∀ p, |T p| ≤ nR * (kE * (Af p * Af p.swap) +
        ko * (Cf p * Af p.swap + Af p * Cf p.swap) + ks * (Cf p * Cf p.swap)) +
        nR * lam₀ * (Df p * Df p.swap) := by
      intro p
      have hpos : 0 ≤ nR * (kE * (Af p * Af p.swap) +
          ko * (Cf p * Af p.swap + Af p * Cf p.swap) + ks * (Cf p * Cf p.swap)) +
          nR * lam₀ * (Df p * Df p.swap) := by
        have a1 := hA0 p; have a2 := hA0 p.swap; have c1 := hC0 p; have c2 := hC0 p.swap
        have d1 := hD0 p; have d2 := hD0 p.swap
        exact add_nonneg (mul_nonneg hn0 (add_nonneg (add_nonneg (mul_nonneg hkE (mul_nonneg a1 a2))
          (mul_nonneg hko (add_nonneg (mul_nonneg c1 a2) (mul_nonneg a1 c2))))
          (mul_nonneg hks (mul_nonneg c1 c2)))) (mul_nonneg (mul_nonneg hn0 hl₀) (mul_nonneg d1 d2))
      by_cases hpG : p ∈ G
      · rw [hTd, indicator_of_mem hpG, abs_mul, abs_of_nonneg (hw12 p)]
        by_cases hpC : p ∈ C
        · obtain ⟨h1, h2, h3, h4, h5⟩ := hvalC p hpG hpC
          obtain ⟨hcc, hE, hO1, hO2, hS⟩ := hmode p ⟨hpG, hpC⟩
          have hc1 : (X p.1 ⬝ᵥ X p.2) ^ 2 < 1 := lt_of_le_of_lt hcc hcp
          have modes := pair_four_modes (hXu p.1) (hXu p.2) hc1 (jac A₁ A₂ (X p.1))
            (jac A₁ A₂ (X p.2)) (mul_nonneg hn0 hkE) (mul_nonneg hn0 hko) (mul_nonneg hn0 hks)
            hE hO1 hO2 hS (hfperp p.1) (hfperp p.2)
          rw [hBf p.1, hBf p.2, h1, h2, h3, h4, h5]
          refine (mul_le_mul_of_nonneg_left modes (hw12 p)).trans (le_of_eq ?_)
          ring
        · obtain ⟨h1, h2, h3, h4, h5⟩ := hvalD p hpG hpC
          rw [h1, h2, h3, h4, h5]
          refine (mul_le_mul_of_nonneg_left (hwideP p hpG hpC) (hw12 p)).trans (le_of_eq ?_)
          ring
      · rw [hTd, indicator_of_notMem hpG, abs_zero]; exact hpos
    have P2 : ∀ p, |T p| ≤ nR * ta_lam kE ko ks * (Af p * Af p.swap) +
        nR * lam₀ * (Df p * Df p.swap) := by
      intro p
      have hpos : 0 ≤ nR * ta_lam kE ko ks * (Af p * Af p.swap) +
          nR * lam₀ * (Df p * Df p.swap) :=
        add_nonneg (mul_nonneg (mul_nonneg hn0 hL0) (mul_nonneg (hA0 p) (hA0 p.swap)))
          (mul_nonneg (mul_nonneg hn0 hl₀) (mul_nonneg (hD0 p) (hD0 p.swap)))
      by_cases hpG : p ∈ G
      · rw [hTd, indicator_of_mem hpG, abs_mul, abs_of_nonneg (hw12 p)]
        by_cases hpC : p ∈ C
        · obtain ⟨h1, h2, h3, h4, h5⟩ := hvalC p hpG hpC
          obtain ⟨hcc, hE, hO1, hO2, hS⟩ := hmode p ⟨hpG, hpC⟩
          have hc1 : (X p.1 ⬝ᵥ X p.2) ^ 2 < 1 := lt_of_le_of_lt hcc hcp
          have hop : opN ((B p.1)ᵀ * B p.2) ≤ nR * ta_lam kE ko ks :=
            (ms_opN_n (hXu p.1) (hXu p.2) hc1 (jac A₁ A₂ (X p.1)) (jac A₁ A₂ (X p.2))
              hkE hko hks hE hO1 hO2 hS).trans (le_of_eq (by unfold ta_lam; ring))
          have hb : |(B p.1 *ᵥ f p.1) ⬝ᵥ (B p.2 *ᵥ f p.2)| ≤
              nR * ta_lam kE ko ks * (nrm (f p.1) * nrm (f p.2)) := by
            rw [ms_bil]
            exact (ms_abs_bil_le_opN _ _ _).trans
              (mul_le_mul_of_nonneg_right hop (mul_nonneg (nrm_nonneg _) (nrm_nonneg _)))
          rw [h1, h5]
          refine (mul_le_mul_of_nonneg_left hb (hw12 p)).trans (le_of_eq ?_)
          ring
        · obtain ⟨h1, h2, h3, h4, h5⟩ := hvalD p hpG hpC
          rw [h1, h3, h5]
          refine (mul_le_mul_of_nonneg_left (hwideP p hpG hpC) (hw12 p)).trans (le_of_eq ?_)
          ring
      · rw [hTd, indicator_of_notMem hpG, abs_zero]; exact hpos
    -- integrability of the majorants and of T
    have iCAAC : Integrable (fun p => Cf p * Af p.swap + Af p * Cf p.swap) (μ.prod μ) :=
      iCA.add iAC
    have iY : Integrable (fun p => kE * (Af p * Af p.swap) +
        ko * (Cf p * Af p.swap + Af p * Cf p.swap)) (μ.prod μ) :=
      (iAA.const_mul kE).add (iCAAC.const_mul ko)
    have iX : Integrable (fun p => nR * (kE * (Af p * Af p.swap) +
        ko * (Cf p * Af p.swap + Af p * Cf p.swap) + ks * (Cf p * Cf p.swap))) (μ.prod μ) :=
      (iY.add (iCC.const_mul ks)).const_mul nR
    have iR1 : Integrable (fun p => nR * (kE * (Af p * Af p.swap) +
        ko * (Cf p * Af p.swap + Af p * Cf p.swap) + ks * (Cf p * Cf p.swap)) +
        nR * lam₀ * (Df p * Df p.swap)) (μ.prod μ) :=
      iX.add (iDD.const_mul (nR * lam₀))
    have hTi : Integrable T (μ.prod μ) :=
      Integrable.mono' iR1 hTm.aestronglyMeasurable
        (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact P1 p)
    have e1 : ∫ p, (nR * (kE * (Af p * Af p.swap) +
        ko * (Cf p * Af p.swap + Af p * Cf p.swap) + ks * (Cf p * Cf p.swap)) +
        nR * lam₀ * (Df p * Df p.swap)) ∂μ.prod μ =
        nR * (kE * (∫ p, Af p * Af p.swap ∂μ.prod μ) +
          ko * ((∫ p, Cf p * Af p.swap ∂μ.prod μ) + ∫ p, Af p * Cf p.swap ∂μ.prod μ) +
          ks * (∫ p, Cf p * Cf p.swap ∂μ.prod μ)) +
        nR * lam₀ * (∫ p, Df p * Df p.swap ∂μ.prod μ) := by
      rw [integral_add iX (iDD.const_mul _), integral_const_mul, integral_const_mul,
        integral_add iY (iCC.const_mul _), integral_add (iAA.const_mul _)
        (iCAAC.const_mul _), integral_const_mul, integral_const_mul,
        integral_const_mul, integral_add iCA iAC]
    have e2 : ∫ p, (nR * ta_lam kE ko ks * (Af p * Af p.swap) +
        nR * lam₀ * (Df p * Df p.swap)) ∂μ.prod μ =
        nR * ta_lam kE ko ks * (∫ p, Af p * Af p.swap ∂μ.prod μ) +
        nR * lam₀ * (∫ p, Df p * Df p.swap ∂μ.prod μ) := by
      rw [integral_add (iAA.const_mul _) (iDD.const_mul _), integral_const_mul,
        integral_const_mul]
    have hT1 := integral_mono hTi iR1 (fun p => (le_abs_self _).trans (P1 p))
    have iR2 : Integrable (fun p => nR * ta_lam kE ko ks * (Af p * Af p.swap) +
        nR * lam₀ * (Df p * Df p.swap)) (μ.prod μ) :=
      (iAA.const_mul (nR * ta_lam kE ko ks)).add (iDD.const_mul (nR * lam₀))
    have hT2 := integral_mono hTi iR2 (fun p => (le_abs_self _).trans (P2 p))
    rw [e1] at hT1
    rw [e2] at hT2
    -- the gain inequalities
    set Ew := ∫ ξ, w ξ ∂μ with hEwd
    set Q := ∫ ξ, normSq (ft ξ) ∂μ with hQd
    have hQ0 : 0 ≤ Q := integral_nonneg fun _ => normSq_nonneg _
    have g1 : kE * (∫ p, Af p * Af p.swap ∂μ.prod μ) +
        ko * ((∫ p, Cf p * Af p.swap ∂μ.prod μ) + ∫ p, Af p * Cf p.swap ∂μ.prod μ) +
        ks * (∫ p, Cf p * Cf p.swap ∂μ.prod μ) ≤ (Ew * Q) * sharpK kE ko ks χ := by
      unfold sharpK
      exact omega_integrated_gain (by omega) u hu ha hτ ht hR hcp hsm1 ft hftm hFi hft hsm
        H hHm hHΩ hcH hkE hko hks
    have g2 : ∫ p, Af p * Af p.swap ∂μ.prod μ ≤ Ew * Q := by
      have h : 1 * (∫ p, Af p * Af p.swap ∂μ.prod μ) +
          0 * ((∫ p, Cf p * Af p.swap ∂μ.prod μ) + ∫ p, Af p * Cf p.swap ∂μ.prod μ) +
          0 * (∫ p, Cf p * Cf p.swap ∂μ.prod μ) ≤ (Ew * Q) * (1 + 2 * 0 * √χ + 0 * χ) :=
        omega_integrated_gain (by omega) u hu ha hτ ht hR hcp hsm1 ft hftm hFi hft hsm
          H hHm hHΩ hcH zero_le_one le_rfl le_rfl
      have e3 : (Ew * Q) * (1 + 2 * 0 * √χ + 0 * χ) = Ew * Q := by ring
      linarith
    have hWP0 : 0 ≤ W * Pp := mul_nonneg hW0 hPp0
    have hrowD : ∀ ξ, ∫ ξ', Df (ξ, ξ') ^ 2 ∂μ ≤ W * Pp * normSq (ft ξ) := by
      intro ξ
      have hsec : MeasurableSet {ξ' | ξ' ∈ Ω ∧ (ξ, ξ') ∉ C} :=
        hΩm.inter (measurable_prodMk_left hCm).compl
      have hi1 : Integrable ({ξ' | ξ' ∈ Ω ∧ (ξ, ξ') ∉ C}.indicator (fun _ => (1 : ℝ))) μ :=
        (integrable_const (1 : ℝ)).indicator hsec
      have hb : ∀ ξ', Df (ξ, ξ') ^ 2 ≤ (normSq (ft ξ) * W) *
          {ξ' | ξ' ∈ Ω ∧ (ξ, ξ') ∉ C}.indicator (fun _ => (1 : ℝ)) ξ' := by
        intro ξ'
        rw [hDfd, fullPairFactor_sq wt ft Dset hwt0]
        by_cases hp : (ξ, ξ') ∈ Dset
        · have hm : ξ' ∈ {ξ' | ξ' ∈ Ω ∧ (ξ, ξ') ∉ C} := ⟨(hGΩ hp.1).2, hp.2⟩
          rw [indicator_of_mem hp, indicator_of_mem hm, mul_one, mul_comm]
          have h1 : wt ξ' ≤ W := (hwtΩ _ hm.1).trans_le (hW _ hm.1)
          exact mul_le_mul_of_nonneg_left h1 (normSq_nonneg _)
        · rw [indicator_of_notMem hp]
          exact mul_nonneg (mul_nonneg (normSq_nonneg _) hW0)
            (indicator_nonneg (fun _ _ => zero_le_one) _)
      have hm := integral_mono_of_nonneg (ae_of_all _ fun ξ' => sq_nonneg (Df (ξ, ξ')))
        (hi1.const_mul (normSq (ft ξ) * W)) (ae_of_all _ hb)
      have e4 : ∫ ξ', {ξ' | ξ' ∈ Ω ∧ (ξ, ξ') ∉ C}.indicator (fun _ => (1 : ℝ)) ξ' ∂μ =
          μ.real {ξ' | ξ' ∈ Ω ∧ (ξ, ξ') ∉ C} := integral_indicator_one hsec
      rw [integral_const_mul, e4] at hm
      refine hm.trans ?_
      have := mul_le_mul_of_nonneg_left (hPp ξ) (mul_nonneg (normSq_nonneg (ft ξ)) hW0)
      linarith
    have g3 : ∫ p, Df p * Df p.swap ∂μ.prod μ ≤ W * Pp * Q := by
      have h := integrated_modes_of_rows μ Df (fun _ => 0) (fun ξ => normSq (ft ξ)) hDfm
        measurable_const hDi (by simp) hFi (fun _ => normSq_nonneg _) hWP0 le_rfl
        zero_le_one le_rfl le_rfl hrowD (by intro x; simp)
      have e3 : (W * Pp * Q) * (1 + 2 * 0 * √0 + 0 * 0) = W * Pp * Q := by ring
      simp only [zero_mul, mul_zero, integral_zero, add_zero, one_mul] at h
      linarith
    -- conclusion
    have hfin1 : ∫ p, T p ∂μ.prod μ ≤ nR * (Ew * Q * sharpK kE ko ks χ) +
        nR * lam₀ * (W * Pp * Q) := by
      refine hT1.trans ?_
      have := mul_le_mul_of_nonneg_left g1 hn0
      have := mul_le_mul_of_nonneg_left g3 (mul_nonneg hn0 hl₀)
      linarith
    have hfin2 : ∫ p, T p ∂μ.prod μ ≤ nR * ta_lam kE ko ks * (Ew * Q) +
        nR * lam₀ * (W * Pp * Q) := by
      refine hT2.trans ?_
      have := mul_le_mul_of_nonneg_left g2 (mul_nonneg hn0 hL0)
      have := mul_le_mul_of_nonneg_left g3 (mul_nonneg hn0 hl₀)
      linarith
    rw [← hQ, ← integral_indicator hGm]
    show ∫ p, T p ∂μ.prod μ ≤ R * Q
    rw [hRd]
    rcases min_cases (sharpK kE ko ks χ) (ta_lam kE ko ks) with ⟨hm, -⟩ | ⟨hm, -⟩
    · rw [hm]; exact hfin1.trans (le_of_eq (by ring))
    · rw [hm]; exact hfin2.trans (le_of_eq (by ring))
  have key := schur_integrated μ B (measurable_BJ_entry A₁ A₂ c τ) (fun ξ => opN (B ξ))
    (measurable_opN_BJ A₁ A₂ c) (fun ξ => le_rfl) (opN_BJ_le A₁ A₂ c (by omega)) wt hwtm hwt0
    hwti hwt2 Ω hΩm (fun ξ hξ => indicator_of_notMem hξ _) G hGm hR0 hgood v
  refine key.trans (mul_le_mul_of_nonneg_right ?_ (normSq_nonneg _))
  have hA : ∫ ξ, wt ξ ^ 2 * opN (B ξ) ^ 4 ∂μ ≤ A4 A₁ A₂ c τ := by
    refine integral_mono ((hwt2.mul_const ((opN A₂ * opN A₁) ^ 4)).mono' ?_ ?_)
      (integrable_wN2_opN4 A₁ A₂ c (by omega) hτ) (fun ξ => ?_)
    · exact ((hwtm.pow_const 2).mul
        ((measurable_opN_BJ A₁ A₂ c).pow_const 4)).aestronglyMeasurable
    · refine ae_of_all _ fun ξ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (opN_nonneg _)
        (opN_BJ_le A₁ A₂ c (by omega) ξ) 4) (sq_nonneg _)
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hwt0 ξ) (hwtle ξ) 2) (by positivity)
  exact add_le_add le_rfl (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hA (Real.sqrt_nonneg _)))

end BstLean.Part238
