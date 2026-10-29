import BstLean.Part72Final

/-!
# Part 72: the specification form `MomCtl`, and Part 71 as a corollary

* `part72_momctl`: Theorem 4's conclusion for every `μ` with `MomCtl n μ d k w A E`
  (sphere support; P1 for `2i ≤ k`; the feature-operator inequality `FeatOp n d μ A`; the
  coordinate mean `≤ E/n`), threshold `N72 d k w (Fop d A) E ε`.
* `chiLaw_momCtl`: `ChiLaw n μ K → MomCtl n μ d k (wChi K) (WFchi K (CSH d)) ((1+|K|)·cG 2)`,
  with the constants Part 71 uses.
* `N72_chi`: the Part 72 threshold at these constants equals Part 71's `N59chi d k K ε`.
* `part71_general'`: Part 71's headline theorem, re-derived from `part72_momctl`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part72

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part71
open BstLean.Part59
open BstLean.Part63
open BstLean.Part66 (tO)
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (Mono frob Tens TSymm heavyCount)
open BstLean.Part53 (cG)

variable {n d : ℕ}

/-- **Theorem 4 under the specification's moment conditions `MomCtl`.** -/
theorem part72_momctl (k d : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (w : ℕ → ℝ) (A E ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hA : 0 < A) (hE : 0 ≤ E) (hε : 0 < ε) :
    100 ≤ N72 d k w (Fop d A) E ε ∧ ∀ n : ℕ, N72 d k w (Fop d A) E ε ≤ n →
      ∃ pg : Prog (In59 n d k) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d k → ℝ, pg.eval v () = g0Q n d k (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d k ε ∧
      ∀ μ : Measure (Fin n → ℝ), MomCtl n μ d k w A E →
        ∀ c : Mono n k → ℝ, TopNZ k c →
          stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
            ε ^ 2 * varP μ k c (unitOfD Z) <
              (BP μ k c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) := by
  obtain ⟨h100, h⟩ := part72_general k d hd hk w (Fop d A) E ε hw hE hε
  refine ⟨h100, fun n hn => ?_⟩
  obtain ⟨pg, h1, h2, h3, h4, h5⟩ := h n hn
  have hn1 : 1 ≤ n := le_trans (by norm_num) (h100.trans hn)
  exact ⟨pg, h1, h2, h3, h4, fun μ hμ => h5 μ (momCtl_good hn1 hd hA hμ)⟩

/-- `ChiLaw` gives `MomCtl` with the constants of Part 71. -/
lemma chiLaw_momCtl (hn : 1 ≤ n) (k : ℕ) {μ : Measure (Fin n → ℝ)} {K : ℝ} (hμ : ChiLaw n μ K) :
    MomCtl n μ d k (wChi K) (WFchi K (CSH d)) ((1 + |K|) * cG 2) :=
  ⟨chiLaw_sph hμ, fun i hi _ => devW_chi hn hμ i hi,
    featOp_chi hn hμ (sphereFourth71 d), chi_coord_mean hn (chiLaw_abs hμ)⟩

lemma mainG_Fop (d k : ℕ) (WF : ℝ) : mainG k (Fop d WF) = mainW d k WF := by
  unfold mainG mainW Fop
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- At the Part 71 constants, the Part 72 threshold is Part 71's threshold. -/
theorem N72_chi (d k : ℕ) (K ε : ℝ) :
    N72 d k (wChi K) (Fop d (WFchi K (CSH d))) ((1 + |K|) * cG 2) ε = N59chi d k K ε := by
  unfold N72 N72t N59chi N59chit Nfail72 Nfail71 C1_72 C1_71 C2_72 C2_71 n2_72 n2_71 CE72 CE71
  rw [mainG_Fop]
  rfl

/-- **Part 71's Theorem 4χ, re-derived from `part72_momctl`.** -/
theorem part71_general' (k d : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (K ε : ℝ) (hε : 0 < ε) :
    100 ≤ N59chi d k K ε ∧ ∀ n : ℕ, N59chi d k K ε ≤ n → ∃ pg : Prog (In59 n d k) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d k → ℝ, pg.eval v () = g0Q n d k (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d k ε ∧
      ∀ μ : Measure (Fin n → ℝ), ChiLaw n μ K →
        ∀ c : Mono n k → ℝ, TopNZ k c →
          stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
            ε ^ 2 * varP μ k c (unitOfD Z) <
              (BP μ k c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) := by
  have hA : 0 < WFchi K (CSH d) := WFchi_pos K _ (CSH_pos d)
  have hE : 0 ≤ (1 + |K|) * cG 2 := by unfold cG; positivity
  obtain ⟨h100, h⟩ := part72_momctl k d hd hk (wChi K) _ _ ε (wChi_nonneg K) hA hE hε
  rw [N72_chi] at h100 h
  refine ⟨h100, fun n hn => ?_⟩
  obtain ⟨pg, h1, h2, h3, h4, h5⟩ := h n hn
  have hn1 : 1 ≤ n := le_trans (by norm_num) (h100.trans hn)
  exact ⟨pg, h1, h2, h3, h4, fun μ hμ => h5 μ (chiLaw_momCtl hn1 k hμ)⟩

end BstLean.Part72
