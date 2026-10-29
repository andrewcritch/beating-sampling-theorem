import BstLean.Part241Integral
import BstLean.Part169Red

/-! Conditional-pass bias with a variable split and a variable bias floor. -/
namespace BstLean.Part241
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part161

variable {n : ℕ}

/-- The full conditional location mean uses the caller's split. -/
noncomputable def fullF (c : Ret n) (split : SplitData n) (a : Ix n) : ℝ :=
  √(eR c) * split.lamb a

/-- The variance term is the difference between the full energy and residual scale.
Its variance interpretation is a separate analytic supply. -/
noncomputable def varianceTerm (c : Ret n) (split : SplitData n) (a : Ix n) : ℝ :=
  wbR c a - fullF c split a ^ 2 - split.Sb a / (2 / (n : ℝ))

lemma measurable_fullF (c : Ret n) (split : SplitData n) :
    Measurable (fullF c split) := split.mlamb.const_mul _

lemma measurable_varianceTerm (c : Ret n) (split : SplitData n) :
    Measurable (varianceTerm c split) :=
  ((measurable_wbR c).sub ((measurable_fullF c split).pow_const 2)).sub
    (split.mSb.div_const _)

/-- The same conditional passes give the free-epsilon bias root.
All averages use muI n, restricted to the same kept bulk. -/
theorem conditional_pass_bias (hn : 0 < n) (c : Ret n) (split : SplitData n) (he : 0 < eR c)
    {χ d ε vmax aw af Hf Cv : ℝ} (hd : 1 / 5 ≤ d) (hε1 : ε < 1) (hT : 0 < ε - vmax / d)
    (haw : 0 < aw) (haf : 0 < af) (hHf : 0 < Hf) (hCv : 0 < Cv)
    (hSbd : ∀ a ∈ (keptIx (paperDesignP n) c split), 2 / (n : ℝ) * d ≤ split.Sb a)
    (hc : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * χ)
    (hVm : ∀ a ∈ (keptIx (paperDesignP n) c split), |varianceTerm c split a| ≤ vmax)
    (iW2 : IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 2) (keptIx (paperDesignP n) c
      split) (muI n))
    (iW6 : IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 6) (keptIx (paperDesignP n) c
      split) (muI n))
    (iW8 : IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 8) (keptIx (paperDesignP n) c
      split) (muI n))
    (iF2 : IntegrableOn (fun a => ((n : ℝ) * (fullF c split a - ftR c a)) ^ 2) (keptIx (paperDesignP
      n) c split) (muI n))
    (iF4 : IntegrableOn (fun a => ((n : ℝ) * (fullF c split a - ftR c a)) ^ 4) (keptIx (paperDesignP
      n) c split) (muI n))
    (iF8 : IntegrableOn (fun a => ((n : ℝ) * (fullF c split a - ftR c a)) ^ 8) (keptIx (paperDesignP
      n) c split) (muI n))
    (if4 : IntegrableOn (fun a => fullF c split a ^ 4) (keptIx (paperDesignP n) c split) (muI n))
    (if24 : IntegrableOn (fun a => fullF c split a ^ 24) (keptIx (paperDesignP n) c split) (muI n))
    (ifF2 : IntegrableOn (fun a => fullF c split a ^ 2 * ((n : ℝ) * (fullF c split a - ftR c a)) ^
      2) (keptIx (paperDesignP n) c split)
      (muI n))
    (ifF6 : IntegrableOn (fun a => fullF c split a ^ 6 * ((n : ℝ) * (fullF c split a - ftR c a)) ^
      6) (keptIx (paperDesignP n) c split)
      (muI n))
    (iV : IntegrableOn (fun a => ((n : ℝ) * varianceTerm c split a) ^ 2) (keptIx (paperDesignP n) c
      split) (muI n))
    (hW8 : ∫ a in (keptIx (paperDesignP n) c split), ((n : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI n ≤ aw
      ^ 8)
    (hF8 : ∫ a in (keptIx (paperDesignP n) c split), ((n : ℝ) * (fullF c split a - ftR c a)) ^ 8
      ∂muI n ≤ af ^ 8)
    (hf4 : ∫ a in (keptIx (paperDesignP n) c split), fullF c split a ^ 4 ∂muI n ≤ Hf ^ 4)
    (hf24 : ∫ a in (keptIx (paperDesignP n) c split), fullF c split a ^ 24 ∂muI n ≤ Hf ^ 24)
    (hV : ∫ a in (keptIx (paperDesignP n) c split), ((n : ℝ) * varianceTerm c split a) ^ 2 ∂muI n ≤
      Cv ^ 2)
     :
    BIAS_hyp (paperDesignP n) c split (biasRoot n χ d ε vmax aw af Hf Cv) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have hse : 0 < √(eR c) := Real.sqrt_pos.mpr he
  -- the integrand of `BIAS_hyp` in the abstract form
  have hS : ∀ a, split.Sb a = 2 / (n : ℝ) * (wbR c a - fullF c split a ^ 2 - varianceTerm c split a)
    := by
    intro a; unfold varianceTerm; field_simp; ring
  have hfun : (fun a => hellG2 n ((split.lamb a -
        ((paperDesignP n).mix c (latC (paperDesignP n) c a)).1) ^ 2 * normSq c.2.1.2)
        (split.Sb a) ((paperDesignP n).mix c (latC (paperDesignP n) c a)).2) =
      fun a => hellG2 n ((fullF c split a / √(eR c) - ftR c a / √(eR c)) ^ 2 * normSq c.2.1.2)
        (2 / (n : ℝ) * (wbR c a - fullF c split a ^ 2 - varianceTerm c split a))
        (2 / (n : ℝ) * max (1 / 5) (wtR c a - ftR c a ^ 2)) := by
    funext a
    rw [← hS a, mixP_eq]
    have e1 : split.lamb a = fullF c split a / √(eR c) := by
      unfold fullF; field_simp
    rw [e1]
    rfl
  have hint := free_epsilon_price (muI n)
    (measurableSet_keptSet _ split.mgood (measurableSet_bulkIx _ c) _)
    (by have := measureReal_le_one (μ := muI n) (s := (keptIx (paperDesignP n) c split)); exact
      this) n hn hγ he hd
    (normSq_nonneg _) hc hε1 hT haw haf hHf hCv (measurable_fullF c split) (measurable_ftR c)
    (measurable_wbR c) (measurable_wtR c) (measurable_varianceTerm c split)
    (fun a ha => (hS a) ▸ hSbd a ha) hVm iW2 iW6 iW8 iF2 iF4 iF8 if4 if24 ifF2 ifF6 iV
    hW8 hF8 hf4 hf24 hV
  unfold BIAS_hyp biasRoot
  have hle : ∫ a in keptIx (paperDesignP n) c split, hellG2 n ((split.lamb a -
        ((paperDesignP n).mix c (latC (paperDesignP n) c a)).1) ^ 2 * normSq c.2.1.2)
        (split.Sb a) ((paperDesignP n).mix c (latC (paperDesignP n) c a)).2 ∂muI n ≤
      squaredPrice n χ d ε vmax aw af Hf Cv := by
    rw [hfun]; exact hint
  exact Real.sqrt_le_sqrt hle

end BstLean.Part241
