import BstLean.Part291UniformTI

namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part199 (OverlapGuard)
open BstLean.Part238
open BstLean.Part153 (nuA)
open BstLean.Part255 (Parameters Valid delta)

structure LowTISupply (n : ℕ) (p : Parameters) (lo hi : ℝ) : Prop where
  valid : Valid p
  wide_num : BstLean.Part246.ta_num_sharp n p.wlo p.whi p.wE p.o p.wS
    (BstLean.Part263.maskSlack n) 46
  core_num : BstLean.Part246.ta_num_sharp n p.clo p.chi p.cE p.o p.cS
    (BstLean.Part263.maskSlack n) 46
  wide_guard : ∀ θ ∈ Icc lo hi, OverlapGuard n θ lowWideWindow p.wlo p.whi
  core_guard : ∀ θ ∈ Icc lo hi, OverlapGuard n θ lowCoreWindow p.clo p.chi
  wide_radius : ∀ θ ∈ Icc lo hi, BstLean.Part199.radiusMinus n θ lowWideWindow ≤ p.wRadius
  core_radius : ∀ θ ∈ Icc lo hi, BstLean.Part199.radiusMinus n θ lowCoreWindow ≤ p.cRadius

noncomputable def lowSchurEvent (n : ℕ) (p : Parameters) (lo hi : ℝ) : Set (AgFam n) :=
  SharpCovEvent n lowWideWindow lowCoreWindow lo hi p.wLam p.cE p.o p.cS p.chi
    (delta / 0.00025)

theorem lowSchurEvent_measurable (n : ℕ) (p : Parameters) (lo hi : ℝ) :
    MeasurableSet (lowSchurEvent n p lo hi) := measurableSet_SharpCovEvent _ _ _ _ _ _ _ _ _ _

/-- The established TI theorem pays 65 exp(-46), not 25 exp(-46).
The conditional Schur event still costs exactly 1/4000. -/
theorem lowSchurEvent_charge {n : ℕ} (hn : 8000 ≤ n) {p : Parameters} {lo hi : ℝ}
    (S : LowTISupply n p lo hi) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real {a | ((c,τ),a) ∉ lowSchurEvent n p lo hi} ≤ (0.00025 : ℝ) := by
  have hw : TI3_hyp n p.wlo p.whi p.wE p.o p.wS delta := by
    rw [← BstLean.Part263.delta_eq (by omega : 1 ≤ n)]
    exact BstLean.Part246.ta_TI3_sharp (by omega) S.valid.wlo_nonneg S.valid.whi_lt
      (BstLean.Part263.maskSlack_nonneg n) (by norm_num) S.wide_num
  have hc : TI3_hyp n p.clo p.chi p.cE p.o p.cS delta := by
    rw [← BstLean.Part263.delta_eq (by omega : 1 ≤ n)]
    exact BstLean.Part246.ta_TI3_sharp (by omega) S.valid.clo_nonneg S.valid.chi_lt
      (BstLean.Part263.maskSlack_nonneg n) (by norm_num) S.core_num
  have hw' : TI_hyp n p.wlo p.whi p.wLam delta :=
    TI_hyp_mono S.valid.wide_lam le_rfl
      (BstLean.Part244.TI_hyp_of_TI3 (by omega) S.valid.wE_nonneg S.valid.o_nonneg
        S.valid.wS_nonneg (pow_lt_one₀ S.valid.whi_nonneg S.valid.whi_lt (by norm_num)) hw)
  exact SharpCovEvent_charge (by omega) lowWideWindow lowCoreWindow lowWindows_order
    S.valid.cE_nonneg S.valid.o_nonneg S.valid.cS_nonneg
    (pow_lt_one₀ S.valid.chi_nonneg S.valid.chi_lt (by norm_num))
    (S.valid.core_lam.trans S.valid.lam_order) (by unfold delta; positivity) (by norm_num)
    S.wide_guard S.core_guard hw' hc c hτ

theorem overlapGuard_widen {n : ℕ} {θ lo hi lo' hi' : ℝ} {w : BstLean.Part199.Window}
    (H : OverlapGuard n θ w lo hi) (hl0 : 0 ≤ lo') (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    OverlapGuard n θ w lo' hi' := by
  rcases H with ⟨h0,h1,h2,h3,h4,h5,h6⟩
  have hr := BstLean.Part199.radiusPlus_nonneg (n := n) h0 w
  refine ⟨h0,h1,h2,h3,?_,?_,?_⟩
  · exact hl0
  · nlinarith
  · nlinarith

end BstLean.BlueprintLow
