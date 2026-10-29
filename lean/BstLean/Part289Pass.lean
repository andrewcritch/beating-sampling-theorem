import BstLean.Part289Design
import BstLean.Part289Bias
import BstLean.Part241Root

/-! The floor-parametric bias junction for the existing conditional passes. -/
namespace BstLean.Part289
open Real MeasureTheory BstLean.Part130 BstLean.Part157 BstLean.Part161
open BstLean.Part169 BstLean.Part241 BstLean.Part228
variable {n : ℕ}

noncomputable def idealDesignFloor (n : ℕ) (s₀ : ℝ) : Design n :=
  paperDesignFloor n s₀ passF passW measurable_passF measurable_passW

theorem idealDesignFloor_one_fifth (n : ℕ) : idealDesignFloor n (1 / 5) = paperDesignP n := rfl

theorem statedDesign2_even (hn : 8 ≤ n) (he : Even n) :
    statedDesign2 n = idealDesignFloor n (scaleFloor n) := by
  have ha : Part272.a1St (n := n) = a1Bar :=
    funext fun c => funext fun s => Part272.a1St_even hn he c s
  have he' : Part272.e1St (n := n) = e1Bar :=
    funext fun c => funext fun s => Part272.e1St_even hn he c s
  have hf : Part272.passFSt (n := n) = passF := by
    funext c g
    simp only [Part272.passFSt, passF, Part272.fPass_eq_G, ha, he']
  have hw : Part272.passWSt (n := n) = passW := by
    funext c g
    simp only [Part272.passWSt, passW, Part272.wPass_eq_G, ha, he']
  unfold statedDesign2 idealDesignFloor
  congr 1 <;> assumption

theorem idealDesignFloor_kept (s₀ : ℝ) (c : Ret n) (split : SplitData n) :
    keptIx (idealDesignFloor n s₀) c split = keptIx (paperDesignP n) c split := rfl

theorem idealDesignFloor_mix (s₀ : ℝ) (c : Ret n) (a : Ix n) :
    (idealDesignFloor n s₀).mix c (latC (idealDesignFloor n s₀) c a) =
      (ftR c a / √(eR c), 2 / (n : ℝ) * max s₀ (wtR c a - ftR c a ^ 2)) := rfl

/-- The moment functions and kept set remain the Part 241 functions and set.
The only changed admissibility condition is `s₀ ≤ d`. -/
structure PassInputsFloor (s₀ : ℝ) (c : Ret n) (split : SplitData n)
    (χ d ε vmax aw af Hf Cv : ℝ) : Prop where
  hs₀ : 0 < s₀
  he : 0 < eR c
  hd : s₀ ≤ d
  hε1 : ε < 1
  hT : 0 < ε - vmax / d
  hSbd : ∀ a ∈ keptIx (paperDesignP n) c split, 2 / (n : ℝ) * d ≤ split.Sb a
  hc : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * χ
  hVm : ∀ a ∈ keptIx (paperDesignP n) c split, |varianceTerm c split a| ≤ vmax
  moments : BiasMoments (muI n) (keptIx (paperDesignP n) c split) n
    (fullF c split) (ftR c) (wbR c) (wtR c) (varianceTerm c split) aw af Hf Cv

theorem bias_of_passInputsFloor (hn : 0 < n) (s₀ : ℝ) (c : Ret n) (split : SplitData n)
    {χ d ε vmax aw af Hf Cv : ℝ} (P : PassInputsFloor s₀ c split χ d ε vmax aw af Hf Cv) :
    BIAS_hyp (idealDesignFloor n s₀) c split (biasRoot n χ d ε vmax aw af Hf Cv) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have hse : 0 < √(eR c) := Real.sqrt_pos.mpr P.he
  have hS : ∀ a, split.Sb a =
      2 / (n : ℝ) * (wbR c a - fullF c split a ^ 2 - varianceTerm c split a) := by
    intro a; unfold varianceTerm; field_simp; ring
  have hfun : (fun a => hellG2 n ((split.lamb a -
      ((idealDesignFloor n s₀).mix c (latC (idealDesignFloor n s₀) c a)).1) ^ 2 * normSq c.2.1.2)
      (split.Sb a) ((idealDesignFloor n s₀).mix c (latC (idealDesignFloor n s₀) c a)).2) =
    fun a => hellG2 n ((fullF c split a / √(eR c) - ftR c a / √(eR c)) ^ 2 * normSq c.2.1.2)
      (2 / (n : ℝ) * (wbR c a - fullF c split a ^ 2 - varianceTerm c split a))
      (2 / (n : ℝ) * max s₀ (wtR c a - ftR c a ^ 2)) := by
    funext a
    rw [← hS a, idealDesignFloor_mix]
    have e1 : split.lamb a = fullF c split a / √(eR c) := by
      unfold fullF; field_simp
    rw [e1]
  unfold BIAS_hyp
  rw [hfun, idealDesignFloor_kept]
  exact free_epsilon_root_floor (muI n)
    (measurableSet_keptSet _ split.mgood (measurableSet_bulkIx _ c) _)
    (measureReal_le_one (μ := muI n)) hn P.hs₀ hγ P.he P.hd (normSq_nonneg _) P.hc
    P.hε1 P.hT P.moments (fun a ha => (hS a) ▸ P.hSbd a ha) P.hVm

/-- Existing pass inputs can also be reused with any positive floor below their cutoff. -/
theorem PassInputs.toFloor (s₀ : ℝ) (c : Ret n) (split : SplitData n)
    {χ d ε vmax aw af Hf Cv : ℝ} (P : Part241.PassInputs c split χ d ε vmax aw af Hf Cv)
    (hs₀ : 0 < s₀) (hd : s₀ ≤ d) : PassInputsFloor s₀ c split χ d ε vmax aw af Hf Cv := by
  refine ⟨hs₀, P.he, hd, P.hε1, P.hT, P.hSbd, P.hc, P.hVm, ?_⟩
  exact ⟨measurable_fullF c split, measurable_ftR c, measurable_wbR c,
    measurable_wtR c, measurable_varianceTerm c split, P.haw, P.haf, P.hHf, P.hCv,
    P.iW2, P.iW6, P.iW8, P.iF2, P.iF4, P.iF8, P.if4, P.if24, P.ifF2, P.ifF6, P.iV,
    P.hW8, P.hF8, P.hf4, P.hf24, P.hV⟩

theorem conditional_pass_root_floor (hn : 2 ≤ n) (s₀ t : ℝ) (c : Ret n)
    (split : SplitData n) (hc : c.1.2 ≠ 0) {χ d ε vmax aw af Hf Cv hfl tl tu : ℝ}
    (P : PassInputsFloor s₀ c split χ d ε vmax aw af Hf Cv)
    (hF : FLUCT_hyp (idealDesignFloor n s₀) t c split hfl)
    (hT : BulkChernoffDomain (idealDesignFloor n s₀) c tl tu) :
    |√(QStand (idealDesignFloor n s₀) t c) - √(qTilde (idealDesignFloor n s₀) t c)| ≤
      hfl + biasRoot n χ d ε vmax aw af Hf Cv + bulkTailRoot (idealDesignFloor n s₀) c tl tu :=
  repla_root_of_split hn (idealDesignFloor n s₀) t c hc hT.tau_pos split hF
    (bias_of_passInputsFloor (by omega) s₀ c split P)
    (tail_hyp_chernoff (idealDesignFloor n s₀) c hT)

end BstLean.Part289

/-- info: 'BstLean.Part289.bias_of_passInputsFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.bias_of_passInputsFloor
/-- info: 'BstLean.Part289.conditional_pass_root_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.conditional_pass_root_floor
