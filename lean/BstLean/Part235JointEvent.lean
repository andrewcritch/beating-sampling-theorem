import BstLean.Part235Charge
import BstLean.Part235Cells

/-! Part 235: the actual common core/wide covariance event with one payment. -/
namespace BstLean.Part235
open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part153 (nuA)
open BstLean.Part199

def jointBadSet (n : ℕ) (w₀ w₁ : Window) (lam₀ lam₁ : ℝ) :
    Set (AgFam n × ((Fin n → ℝ) × (Fin n → ℝ))) :=
  badSet n w₀.t w₀.z w₀.pair lam₀ ∪ badSet n w₁.t w₁.z w₁.pair lam₁

theorem measurableSet_jointBadSet (n : ℕ) (w₀ w₁ : Window) (lam₀ lam₁ : ℝ) :
    MeasurableSet (jointBadSet n w₀ w₁ lam₀ lam₁) :=
  (measurableSet_badSet _ _ _ _).union (measurableSet_badSet _ _ _ _)

noncomputable def jointBadMass (n : ℕ) (w₀ w₁ : Window) (lam₀ lam₁ : ℝ)
    (k : AgFam n) : ℝ :=
  ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real
    (Prod.mk k ⁻¹' jointBadSet n w₀ w₁ lam₀ lam₁)

theorem measurable_jointBadMass (n : ℕ) (w₀ w₁ : Window) (lam₀ lam₁ : ℝ) :
    Measurable (jointBadMass n w₀ w₁ lam₀ lam₁) := by
  haveI : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  exact (measurable_measure_prodMk_left
    (measurableSet_jointBadSet n w₀ w₁ lam₀ lam₁)).ennreal_toReal

/-- The fixed input pair uses its core class when it belongs to the core. -/
theorem joint_pair_charge {n : ℕ} (hn : 1 ≤ n) (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {lam₀ lam₁ δ lo₀ hi₀ lo₁ hi₁ : ℝ} (hlam : lam₁ ≤ lam₀) (hδ : 0 ≤ δ)
    (hTI₀ : TI_hyp n lo₀ hi₀ lam₀ δ) (hTI₁ : TI_hyp n lo₁ hi₁ lam₁ δ)
    (c : Fin n → ℝ) (τ : ℝ)
    (hg₀ : ∀ p ∈ GammaS c w₀.t w₀.z w₀.pair,
      lo₀ ≤ sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ∧
      sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ≤ hi₀)
    (hg₁ : ∀ p ∈ GammaS c w₁.t w₁.z w₁.pair,
      lo₁ ≤ sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ∧
      sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ≤ hi₁)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    (nuA n).real {a | (((c, τ), a), p) ∈ jointBadSet n w₀ w₁ lam₀ lam₁} ≤ δ := by
  by_cases hp₁ : p ∈ GammaS c w₁.t w₁.z w₁.pair
  · obtain ⟨hl, hu⟩ := hg₁ p hp₁
    refine (measureReal_mono (fun a ha => ?_) (measure_ne_top _ _)).trans
      (hTI₁ _ _ (normSq_sphPt hn _) (normSq_sphPt hn _) hl hu)
    rcases ha with ha | ha
    · exact (mul_le_mul_of_nonneg_left hlam (Nat.cast_nonneg n)).trans_lt ha.2
    · exact ha.2
  · by_cases hp₀ : p ∈ GammaS c w₀.t w₀.z w₀.pair
    · obtain ⟨hl, hu⟩ := hg₀ p hp₀
      refine (measureReal_mono (fun a ha => ?_) (measure_ne_top _ _)).trans
        (hTI₀ _ _ (normSq_sphPt hn _) (normSq_sphPt hn _) hl hu)
      rcases ha with ha | ha
      · exact ha.2
      · exact False.elim (hp₁ ha.1)
    · have he : {a | (((c, τ), a), p) ∈ jointBadSet n w₀ w₁ lam₀ lam₁} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro a ha
        rcases ha with ha | ha
        · exact hp₀ ha.1
        · exact hp₀ (gamma_subset c h10 ha.1)
      rw [he, measureReal_empty]
      exact hδ

def JointCovEvent (n : ℕ) (w₀ w₁ : Window) (θlo θhi lam₀ lam₁ cutoff : ℝ) :
    Set (AgFam n) :=
  {k | thetaC k.1.1 k.1.2 ∉ Set.Icc θlo θhi} ∪
    {k | jointBadMass n w₀ w₁ lam₀ lam₁ k ≤ cutoff}

theorem measurableSet_JointCovEvent (n : ℕ) (w₀ w₁ : Window)
    (θlo θhi lam₀ lam₁ cutoff : ℝ) :
    MeasurableSet (JointCovEvent n w₀ w₁ θlo θhi lam₀ lam₁ cutoff) := by
  have hm : MeasurableSet {k : AgFam n | thetaC k.1.1 k.1.2 ∈ Set.Icc θlo θhi} :=
    (measurableSet_le measurable_const measurable_thetaC_key').inter
      (measurableSet_le measurable_thetaC_key' measurable_const)
  exact hm.compl.union (measurableSet_le
    (measurable_jointBadMass n w₀ w₁ lam₀ lam₁) measurable_const)

/-- The actual union of both failure sets costs epsilon, rather than two epsilon. -/
theorem JointCovEvent_charge {n : ℕ} (hn : 1 ≤ n) (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {θlo θhi lo₀ hi₀ lo₁ hi₁ lam₀ lam₁ δ ε : ℝ}
    (hlam : lam₁ ≤ lam₀) (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hg₀ : ∀ θ ∈ Set.Icc θlo θhi, OverlapGuard n θ w₀ lo₀ hi₀)
    (hg₁ : ∀ θ ∈ Set.Icc θlo θhi, OverlapGuard n θ w₁ lo₁ hi₁)
    (hTI₀ : TI_hyp n lo₀ hi₀ lam₀ δ) (hTI₁ : TI_hyp n lo₁ hi₁ lam₁ δ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real {a | ((c, τ), a) ∉
      JointCovEvent n w₀ w₁ θlo θhi lam₀ lam₁ (δ / ε)} ≤ ε := by
  classical
  haveI : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  haveI : IsProbabilityMeasure (nuA n) := by
    unfold nuA BstLean.Part130.gaussMat; infer_instance
  by_cases hw : thetaC c τ ∈ Set.Icc θlo θhi
  · let S : Set ((Matrix (Fin (mA n)) (Fin n) ℝ ×
        Matrix (Fin (mA n)) (Fin (mA n)) ℝ) ×
        ((Fin n → ℝ) × (Fin n → ℝ))) :=
      {q | (((c, τ), q.1), q.2) ∈ jointBadSet n w₀ w₁ lam₀ lam₁}
    have hS : MeasurableSet S :=
      (measurable_const.prodMk measurable_fst |>.prodMk measurable_snd)
        (measurableSet_jointBadSet n w₀ w₁ lam₀ lam₁)
    have h := pair_mass_charge (nuA n) ((stdGauss (Fin n)).prod (stdGauss (Fin n)))
      S hS hδ hε (joint_pair_charge hn w₀ w₁ h10 hlam hδ hTI₀ hTI₁ c τ
        (fun p hp => overlap_of_guard (by omega) hτ w₀ (hg₀ _ hw) hp)
        (fun p hp => overlap_of_guard (by omega) hτ w₁ (hg₁ _ hw) hp))
    refine (measureReal_mono (fun a ha => ?_) (measure_ne_top _ _)).trans h
    change δ / ε < jointBadMass n w₀ w₁ lam₀ lam₁ ((c, τ), a)
    exact lt_of_not_ge (fun hb => ha (Or.inr hb))
  · have he : {a | ((c, τ), a) ∉
        JointCovEvent n w₀ w₁ θlo θhi lam₀ lam₁ (δ / ε)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact ha (Or.inl hw)
    rw [he, measureReal_empty]
    exact hε.le

/-- Retained-data integration preserves the same single payment. -/
theorem JointCovEvent_ret_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτ : TauWorld D)
    (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {θlo θhi lo₀ hi₀ lo₁ hi₁ lam₀ lam₁ δ ε : ℝ}
    (hlam : lam₁ ≤ lam₀) (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hg₀ : ∀ θ ∈ Set.Icc θlo θhi, OverlapGuard n θ w₀ lo₀ hi₀)
    (hg₁ : ∀ θ ∈ Set.Icc θlo θhi, OverlapGuard n θ w₁ lo₁ hi₁)
    (hTI₀ : TI_hyp n lo₀ hi₀ lam₀ δ) (hTI₁ : TI_hyp n lo₁ hi₁ lam₁ δ) :
    (retDist D.toCentres).real
      (agentEv D (JointCovEvent n w₀ w₁ θlo θhi lam₀ lam₁ (δ / ε)))ᶜ ≤ ε := by
  rw [agentEv_compl]
  exact retDist_agent_charge D hτ
    (measurableSet_JointCovEvent n w₀ w₁ θlo θhi lam₀ lam₁ (δ / ε)) hε.le
    (fun c τ hτ => JointCovEvent_charge hn w₀ w₁ h10 hlam hδ hε hg₀ hg₁ hTI₀ hTI₁ c hτ)

end BstLean.Part235
