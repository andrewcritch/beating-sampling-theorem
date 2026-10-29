import BstLean.Part238TI3

/-! Part 238: the joint wide/mode covariance event with one payment, its retained-data charge,
and the transfer of the sharp assembly to the network interface `COV_at`. -/
namespace BstLean.Part238
open MeasureTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part157 BstLean.Part160 BstLean.Part182
  BstLean.Part208
open BstLean.Part199 (Window radiusMinus pairFailure commonGood measurableSet_pairFailure
  measurableSet_commonGood commonGood_swap commonGood_exception OverlapGuard overlap_of_guard
  gamma_subset cov_of_scalar)
open BstLean.Part150 (thetaC)
open BstLean.Part153 (nrm nuA Xi4 projT jacT)
open BstLean.Part151 (jac)

variable {n : ℕ}

/-- The joint failure set: wide operator failures on wide pairs, and mode failures on core pairs. -/
def sharpBadSet (n : ℕ) (w₀ w₁ : Window) (lam₀ kE ko ks cp : ℝ) :
    Set (AgFam n × ((Fin n → ℝ) × (Fin n → ℝ))) :=
  badSet n w₀.t w₀.z w₀.pair lam₀ ∪ modeBadSet n w₁ kE ko ks cp

theorem measurableSet_sharpBadSet (w₀ w₁ : Window) (lam₀ kE ko ks cp : ℝ) :
    MeasurableSet (sharpBadSet n w₀ w₁ lam₀ kE ko ks cp) :=
  (measurableSet_badSet _ _ _ _).union (measurableSet_modeBadSet _ _ _ _ _)

noncomputable def sharpBadMass (n : ℕ) (w₀ w₁ : Window) (lam₀ kE ko ks cp : ℝ)
    (k : AgFam n) : ℝ :=
  ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real
    (Prod.mk k ⁻¹' sharpBadSet n w₀ w₁ lam₀ kE ko ks cp)

theorem measurable_sharpBadMass (w₀ w₁ : Window) (lam₀ kE ko ks cp : ℝ) :
    Measurable (sharpBadMass n w₀ w₁ lam₀ kE ko ks cp) := by
  haveI : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  exact (measurable_measure_prodMk_left
    (measurableSet_sharpBadSet w₀ w₁ lam₀ kE ko ks cp)).ennreal_toReal

/-- Mode separation: the three mode bounds imply the operator pair bound `n λ₁`. -/
theorem modeBounds_opN {m : ℕ} {A₁ : Matrix (Fin m) (Fin n) ℝ} {A₂ : Matrix (Fin m) (Fin m) ℝ}
    {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    {kE ko ks cp : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks) (hcp : cp ^ 2 < 1)
    (h : ModeBounds (jac A₁ A₂ x) (jac A₁ A₂ x') kE ko ks cp x x') :
    opN ((jacT A₁ A₂ x)ᵀ * jacT A₁ A₂ x') ≤ (n : ℝ) * ta_lam kE ko ks := by
  obtain ⟨hcc, hE, hO1, hO2, hS⟩ := h
  exact (ms_opN_n hx hx' (lt_of_le_of_lt hcc hcp) (jac A₁ A₂ x) (jac A₁ A₂ x')
    hkE hko hks hE hO1 hO2 hS).trans (le_of_eq (by unfold ta_lam; ring))

/-- The fixed input pair uses the mode hypothesis on core pairs and the wide operator
hypothesis on the other wide pairs. There is no sum over the two classes. -/
theorem sharp_pair_charge (hn : 1 ≤ n) (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {lam₀ kE ko ks cp δ lo₀ hi₀ lo₁ : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hcp : cp ^ 2 < 1) (hlam : ta_lam kE ko ks ≤ lam₀) (hδ : 0 ≤ δ)
    (hTI₀ : TI_hyp n lo₀ hi₀ lam₀ δ) (hTI₁ : TI3_hyp n lo₁ cp kE ko ks δ)
    (c : Fin n → ℝ) (τ : ℝ)
    (hg₀ : ∀ p ∈ GammaS c w₀.t w₀.z w₀.pair,
      lo₀ ≤ sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ∧
      sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ≤ hi₀)
    (hg₁ : ∀ p ∈ GammaS c w₁.t w₁.z w₁.pair,
      lo₁ ≤ sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ∧
      sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ≤ cp)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    (nuA n).real {a | (((c, τ), a), p) ∈ sharpBadSet n w₀ w₁ lam₀ kE ko ks cp} ≤ δ := by
  by_cases hp₁ : p ∈ GammaS c w₁.t w₁.z w₁.pair
  · obtain ⟨hl, hu⟩ := hg₁ p hp₁
    refine (measureReal_mono (fun a ha => ?_) (measure_ne_top _ _)).trans
      (hTI₁ _ _ (normSq_sphPt hn _) (normSq_sphPt hn _) hl hu)
    show ¬ ModeBounds _ _ kE ko ks cp _ _
    intro hmb
    rcases ha with ha | ha
    · have hop := modeBounds_opN (normSq_sphPt hn _) (normSq_sphPt hn _) hkE hko hks hcp hmb
      have hbad := ha.2
      unfold pairBad at hbad
      have := mul_le_mul_of_nonneg_left hlam (Nat.cast_nonneg n)
      linarith
    · exact ha.2 hmb
  · by_cases hp₀ : p ∈ GammaS c w₀.t w₀.z w₀.pair
    · obtain ⟨hl, hu⟩ := hg₀ p hp₀
      refine (measureReal_mono (fun a ha => ?_) (measure_ne_top _ _)).trans
        (hTI₀ _ _ (normSq_sphPt hn _) (normSq_sphPt hn _) hl hu)
      rcases ha with ha | ha
      · exact ha.2
      · exact False.elim (hp₁ ha.1)
    · have he : {a | (((c, τ), a), p) ∈ sharpBadSet n w₀ w₁ lam₀ kE ko ks cp} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro a ha
        rcases ha with ha | ha
        · exact hp₀ ha.1
        · exact hp₀ (gamma_subset c h10 ha.1)
      rw [he, measureReal_empty]
      exact hδ

/-- **The sharp covariance event**: outside the retained `θ` window, or joint failure mass at most
the cutoff. -/
def SharpCovEvent (n : ℕ) (w₀ w₁ : Window) (θlo θhi lam₀ kE ko ks cp cutoff : ℝ) :
    Set (AgFam n) :=
  {k | thetaC k.1.1 k.1.2 ∉ Set.Icc θlo θhi} ∪
    {k | sharpBadMass n w₀ w₁ lam₀ kE ko ks cp k ≤ cutoff}

theorem measurableSet_SharpCovEvent (w₀ w₁ : Window) (θlo θhi lam₀ kE ko ks cp cutoff : ℝ) :
    MeasurableSet (SharpCovEvent n w₀ w₁ θlo θhi lam₀ kE ko ks cp cutoff) := by
  have hm : MeasurableSet {k : AgFam n | thetaC k.1.1 k.1.2 ∈ Set.Icc θlo θhi} :=
    (measurableSet_le measurable_const measurable_thetaC_key').inter
      (measurableSet_le measurable_thetaC_key' measurable_const)
  exact hm.compl.union (measurableSet_le
    (measurable_sharpBadMass w₀ w₁ lam₀ kE ko ks cp) measurable_const)

/-- **One payment** for the joint wide/mode event at fixed retained values. -/
theorem SharpCovEvent_charge (hn : 1 ≤ n) (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {θlo θhi lo₀ hi₀ lo₁ lam₀ kE ko ks cp δ ε : ℝ}
    (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks) (hcp : cp ^ 2 < 1)
    (hlam : ta_lam kE ko ks ≤ lam₀) (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hg₀ : ∀ θ ∈ Set.Icc θlo θhi, OverlapGuard n θ w₀ lo₀ hi₀)
    (hg₁ : ∀ θ ∈ Set.Icc θlo θhi, OverlapGuard n θ w₁ lo₁ cp)
    (hTI₀ : TI_hyp n lo₀ hi₀ lam₀ δ) (hTI₁ : TI3_hyp n lo₁ cp kE ko ks δ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real {a | ((c, τ), a) ∉
      SharpCovEvent n w₀ w₁ θlo θhi lam₀ kE ko ks cp (δ / ε)} ≤ ε := by
  classical
  haveI : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  haveI : IsProbabilityMeasure (nuA n) := by
    unfold nuA BstLean.Part130.gaussMat; infer_instance
  by_cases hw : thetaC c τ ∈ Set.Icc θlo θhi
  · let S : Set ((Matrix (Fin (mA n)) (Fin n) ℝ ×
        Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × ((Fin n → ℝ) × (Fin n → ℝ))) :=
      {q | (((c, τ), q.1), q.2) ∈ sharpBadSet n w₀ w₁ lam₀ kE ko ks cp}
    have hS : MeasurableSet S :=
      (measurable_const.prodMk measurable_fst |>.prodMk measurable_snd)
        (measurableSet_sharpBadSet w₀ w₁ lam₀ kE ko ks cp)
    have h := BstLean.Part235.pair_mass_charge (nuA n)
      ((stdGauss (Fin n)).prod (stdGauss (Fin n))) S hS hδ hε
      (sharp_pair_charge hn w₀ w₁ h10 hkE hko hks hcp hlam hδ hTI₀ hTI₁ c τ
        (fun p hp => overlap_of_guard (by omega) hτ w₀ (hg₀ _ hw) hp)
        (fun p hp => overlap_of_guard (by omega) hτ w₁ (hg₁ _ hw) hp))
    refine (measureReal_mono (fun a ha => ?_) (measure_ne_top _ _)).trans h
    change δ / ε < sharpBadMass n w₀ w₁ lam₀ kE ko ks cp ((c, τ), a)
    exact lt_of_not_ge (fun hb => ha (Or.inr hb))
  · have he : {a | ((c, τ), a) ∉
        SharpCovEvent n w₀ w₁ θlo θhi lam₀ kE ko ks cp (δ / ε)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact ha (Or.inl hw)
    rw [he, measureReal_empty]
    exact hε.le

/-- Retained-data integration keeps the single payment. -/
theorem SharpCovEvent_ret_charge (hn : 1 ≤ n) (D : Design n) (hτ : TauWorld D)
    (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {θlo θhi lo₀ hi₀ lo₁ lam₀ kE ko ks cp δ ε : ℝ}
    (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks) (hcp : cp ^ 2 < 1)
    (hlam : ta_lam kE ko ks ≤ lam₀) (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hg₀ : ∀ θ ∈ Set.Icc θlo θhi, OverlapGuard n θ w₀ lo₀ hi₀)
    (hg₁ : ∀ θ ∈ Set.Icc θlo θhi, OverlapGuard n θ w₁ lo₁ cp)
    (hTI₀ : TI_hyp n lo₀ hi₀ lam₀ δ) (hTI₁ : TI3_hyp n lo₁ cp kE ko ks δ) :
    (retDist D.toCentres).real
      (agentEv D (SharpCovEvent n w₀ w₁ θlo θhi lam₀ kE ko ks cp (δ / ε)))ᶜ ≤ ε := by
  rw [agentEv_compl]
  exact retDist_agent_charge D hτ
    (measurableSet_SharpCovEvent w₀ w₁ θlo θhi lam₀ kE ko ks cp (δ / ε)) hε.le
    (fun c τ hτ => SharpCovEvent_charge hn w₀ w₁ h10 hkE hko hks hcp hlam hδ hε hg₀ hg₁
      hTI₀ hTI₁ c hτ)

/-- On the joint event, the sharp assembly holds with exceptional mass `2e^{-t₁²/2} + 2b`. -/
theorem Dq_sharp_joint {n : ℕ} (hn : 6 ≤ n)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c u : Fin n → ℝ) {a τ : ℝ} (hcau : c = a • u) (ha : 0 < a) (hu : normSq u = 1)
    (hτ : 0 < τ) (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {kE ko ks lam₀ cp sm M b : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hl₀ : 0 ≤ lam₀) (hM : 0 ≤ M) (hθ : thetaC c τ < 1)
    (hr₀ : radiusMinus n (thetaC c τ) w₀ < 1) (hr₁ : radiusMinus n (thetaC c τ) w₁ < 1)
    (hR : 0 < axialRadiusLower n a τ w₁.t w₁.z) (hcp : cp ^ 2 < 1) (hsm1 : sm ≤ 1)
    (hsm : ∀ ξ ∈ OmegaS c w₁.t w₁.z, sm ≤ (u ⬝ᵥ sphPt (c + τ • ξ)) ^ 2)
    (hb : sharpBadMass n w₀ w₁ lam₀ kE ko ks cp ((c, τ), (A₁, A₂)) ≤ b)
    (hX : Xi4 A₁ A₂ c τ ≤ M * (2 / (n : ℝ)) / n) (v : Fin (mA n) → ℝ) :
    Dq A₁ A₂ c τ v ≤
      sharpScalar n (thetaC c τ) w₀ w₁
        (min (sharpK kE ko ks (chiCore n a τ w₁.t w₁.z sm cp)) (ta_lam kE ko ks))
        lam₀ (1 - 4 * thetaC c τ / n)⁻¹ M
        (2 * exp (-w₀.pair ^ 2 / 2) + 2 * b) * (2 / (n : ℝ)) / n * normSq v := by
  have hn0 : 0 < n := by omega
  let B := pairFailure A₁ A₂ c τ w₀ lam₀ ∪ modeFailure A₁ A₂ c τ w₁ kE ko ks cp
  have hBm : MeasurableSet B :=
    (measurableSet_pairFailure A₁ A₂ c τ w₀ lam₀).union
      (measurableSet_modeFailure A₁ A₂ c τ w₁ kE ko ks cp)
  let G := commonGood c w₀ B
  have hB : ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real B ≤ b := hb
  apply Dq_core_wide_sharp hn A₁ A₂ c u hcau ha hu hτ w₀ w₁ h10 hkE hko hks hl₀ hM hθ hr₀ hr₁
    hR hcp hsm1 hsm G (measurableSet_commonGood c w₀ hBm)
    (fun p hp => commonGood_swap c w₀ B p.1 p.2 hp)
    (fun p hp => ⟨hp.1.1, hp.1.2.1⟩)
    (fun p hp hp₁ => by
      by_contra hno
      exact hp.2 (Or.inl (Or.inr ⟨hp₁, hno⟩)))
    (fun p hp _ => by
      apply not_lt.mp
      intro hbad
      exact hp.2 (Or.inl (Or.inl ⟨hp.1, hbad⟩)))
    (commonGood_exception hn0 c w₀ hBm hB) hX v

/-- **Network transfer.** The sharp scalar, the retained `θ` window, the joint event, and the
fourth-moment bound imply the existing covariance interface `COV_at D k N`. -/
theorem cov_at_sharp {n : ℕ} (hn : 6 ≤ n) (D : Design n) (k : Ret n)
    (hτ : 0 < D.tau0 k) (u : Fin n → ℝ) {a : ℝ} (hcau : k.1.2 = a • u) (ha : 0 < a)
    (hu : normSq u = 1) (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {θlo θhi kE ko ks lam₀ cp sm M b N : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hl₀ : 0 ≤ lam₀) (hM : 0 ≤ M)
    (hw : thetaC k.1.2 (D.tau0 k) ∈ Set.Icc θlo θhi) (hθhi : θhi < 1)
    (hr₀ : radiusMinus n (thetaC k.1.2 (D.tau0 k)) w₀ < 1)
    (hr₁ : radiusMinus n (thetaC k.1.2 (D.tau0 k)) w₁ < 1)
    (hR : 0 < axialRadiusLower n a (D.tau0 k) w₁.t w₁.z) (hcp : cp ^ 2 < 1) (hsm1 : sm ≤ 1)
    (hsm : ∀ ξ ∈ OmegaS k.1.2 w₁.t w₁.z, sm ≤ (u ⬝ᵥ sphPt (k.1.2 + D.tau0 k • ξ)) ^ 2)
    (hX : Xi4 k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) ≤ M * (2 / (n : ℝ)) / n)
    (hC : ((k.1.2, D.tau0 k), (k.2.1.1.1, k.2.1.1.2)) ∈
      SharpCovEvent n w₀ w₁ θlo θhi lam₀ kE ko ks cp b)
    (hN : sharpScalar n (thetaC k.1.2 (D.tau0 k)) w₀ w₁
        (min (sharpK kE ko ks (chiCore n a (D.tau0 k) w₁.t w₁.z sm cp)) (ta_lam kE ko ks))
        lam₀ (1 - 4 * thetaC k.1.2 (D.tau0 k) / n)⁻¹ M
        (2 * exp (-w₀.pair ^ 2 / 2) + 2 * b) ≤ N) : COV_at D k N := by
  have hb : sharpBadMass n w₀ w₁ lam₀ kE ko ks cp
      ((k.1.2, D.tau0 k), (k.2.1.1.1, k.2.1.1.2)) ≤ b := by
    rcases hC with hC | hC
    · exact absurd hw hC
    · exact hC
  refine cov_of_scalar hn D k hτ hN (fun v => ?_)
  exact Dq_sharp_joint hn k.2.1.1.1 k.2.1.1.2 k.1.2 u hcau ha hu hτ w₀ w₁ h10 hkE hko hks hl₀
    hM (hw.2.trans_lt hθhi) hr₀ hr₁ hR hcp hsm1 hsm hb hX v

end BstLean.Part238
