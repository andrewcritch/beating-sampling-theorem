import BstLean.Part238Event

/-! Part 238: the fixed-pair three-mode TI hypothesis, its single Fubini–Markov charge,
and the sharp assembly on the resulting events. -/
namespace BstLean.Part238
open MeasureTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part160 BstLean.Part182 BstLean.Part208
open BstLean.Part199 (Window radiusMinus pairFailure commonGood measurableSet_pairFailure
  measurableSet_commonGood commonGood_swap commonGood_exception)
open BstLean.Part150 (thetaC)
open BstLean.Part153 (nrm nuA Xi4)
open BstLean.Part151 (jac)

variable {n : ℕ}

/-- **The three-mode two-input hypothesis.** For every fixed pair of unit inputs with
`cm ≤ x·x' ≤ cp`, the Agent weights violate one of the three TI mode bounds (or the overlap cap)
with probability at most `δ`. Paper: the conclusion of Lemma `t7:p04:ti`. -/
def TI3_hyp (n : ℕ) (cm cp kE ko ks δ : ℝ) : Prop :=
  ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 → cm ≤ x ⬝ᵥ x' → x ⬝ᵥ x' ≤ cp →
    (nuA n).real {θ | ¬ ModeBounds (jac θ.1 θ.2 x) (jac θ.1 θ.2 x') kE ko ks cp x x'} ≤ δ

/-- The mode failures of one fixed Agent family. -/
def modeFailure (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (w : Window) (kE ko ks cp : ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | (((c, τ), (A₁, A₂)), p) ∈ modeBadSet n w kE ko ks cp}

theorem measurableSet_modeFailure (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ) (w : Window)
    (kE ko ks cp : ℝ) : MeasurableSet (modeFailure A₁ A₂ c τ w kE ko ks cp) :=
  measurable_prodMk_left (measurableSet_modeBadSet w kE ko ks cp)

/-- The mode-failure pair mass at one family `((c, τ), (A₁, A₂))`. -/
noncomputable def modeBadMass (n : ℕ) (w : Window) (kE ko ks cp : ℝ) (k : AgFam n) : ℝ :=
  ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real (Prod.mk k ⁻¹' modeBadSet n w kE ko ks cp)

theorem measurable_modeBadMass (w : Window) (kE ko ks cp : ℝ) :
    Measurable (modeBadMass n w kE ko ks cp) := by
  haveI : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  exact (measurable_measure_prodMk_left (measurableSet_modeBadSet w kE ko ks cp)).ennreal_toReal

/-- **The mode event and its charge.** If every core pair has overlap in `[cm, cp]` and the
three-mode hypothesis holds, the mode-failure pair mass exceeds `δ/ε` with probability at most `ε`.
The charge is paid once, after integration over the input pair. -/
theorem modeEvent_charge (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (w : Window)
    {kE ko ks cm cp δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hgeo : ∀ p ∈ GammaS c w.t w.z w.pair,
      cm ≤ sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ∧
        sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ≤ cp)
    (hTI : TI3_hyp n cm cp kE ko ks δ) :
    (nuA n).real {θ | δ / ε < modeBadMass n w kE ko ks cp ((c, τ), θ)} ≤ ε := by
  haveI : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  haveI : IsProbabilityMeasure (nuA n) := by
    unfold nuA BstLean.Part130.gaussMat; infer_instance
  set S : Set ((Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) ×
      ((Fin n → ℝ) × (Fin n → ℝ))) :=
    {q | (((c, τ), q.1), q.2) ∈ modeBadSet n w kE ko ks cp} with hS
  have hSm : MeasurableSet S := by
    have hf : Measurable (fun q : (Matrix (Fin (mA n)) (Fin n) ℝ ×
        Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        (((c, τ), q.1), q.2)) :=
      ((measurable_const.prodMk measurable_fst)).prodMk measurable_snd
    exact hf (measurableSet_modeBadSet w kE ko ks cp)
  have h := BstLean.Part235.pair_mass_charge (nuA n)
    ((stdGauss (Fin n)).prod (stdGauss (Fin n))) S hSm hδ hε (fun p => by
      by_cases hp : p ∈ GammaS c w.t w.z w.pair
      · obtain ⟨h1, h2⟩ := hgeo p hp
        refine (measureReal_mono (fun θ hθ => ?_) (measure_ne_top _ _)).trans
          (hTI _ _ (normSq_sphPt hn _) (normSq_sphPt hn _) h1 h2)
        exact hθ.2
      · have he : (fun a => (a, p)) ⁻¹' S = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro θ hθ
          exact hp hθ.1
        rw [he, measureReal_empty]
        exact hδ)
  exact h

/-- **Sharp assembly on the events.** On the wide operator event (bad mass at most `b₀`) and the
mode event (mode-failure mass at most `bₘ`), the common good set removes both failures in both
orientations. The sharp formula holds with exceptional mass `2e^{-t₁²/2} + 2(b₀ + bₘ)`. -/
theorem Dq_sharp_events {n : ℕ} (hn : 6 ≤ n)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c u : Fin n → ℝ) {a τ : ℝ} (hcau : c = a • u) (ha : 0 < a) (hu : normSq u = 1)
    (hτ : 0 < τ) (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {kE ko ks lam₀ cp sm M b₀ bm : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hl₀ : 0 ≤ lam₀) (hM : 0 ≤ M) (hθ : thetaC c τ < 1)
    (hr₀ : radiusMinus n (thetaC c τ) w₀ < 1) (hr₁ : radiusMinus n (thetaC c τ) w₁ < 1)
    (hR : 0 < axialRadiusLower n a τ w₁.t w₁.z) (hcp : cp ^ 2 < 1) (hsm1 : sm ≤ 1)
    (hsm : ∀ ξ ∈ OmegaS c w₁.t w₁.z, sm ≤ (u ⬝ᵥ sphPt (c + τ • ξ)) ^ 2)
    (hb₀ : badMass n w₀.t w₀.z w₀.pair lam₀ ((c, τ), (A₁, A₂)) ≤ b₀)
    (hbm : modeBadMass n w₁ kE ko ks cp ((c, τ), (A₁, A₂)) ≤ bm)
    (hX : Xi4 A₁ A₂ c τ ≤ M * (2 / (n : ℝ)) / n) (v : Fin (mA n) → ℝ) :
    Dq A₁ A₂ c τ v ≤
      sharpScalar n (thetaC c τ) w₀ w₁
        (min (sharpK kE ko ks (chiCore n a τ w₁.t w₁.z sm cp)) (ta_lam kE ko ks))
        lam₀ (1 - 4 * thetaC c τ / n)⁻¹ M
        (2 * exp (-w₀.pair ^ 2 / 2) + 2 * (b₀ + bm)) * (2 / (n : ℝ)) / n * normSq v := by
  have hn0 : 0 < n := by omega
  let B := pairFailure A₁ A₂ c τ w₀ lam₀ ∪ modeFailure A₁ A₂ c τ w₁ kE ko ks cp
  have hBm : MeasurableSet B :=
    (measurableSet_pairFailure A₁ A₂ c τ w₀ lam₀).union
      (measurableSet_modeFailure A₁ A₂ c τ w₁ kE ko ks cp)
  let G := commonGood c w₀ B
  have hb : ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real B ≤ b₀ + bm :=
    (measureReal_union_le _ _).trans (add_le_add hb₀ hbm)
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
    (commonGood_exception hn0 c w₀ hBm hb) hX v

end BstLean.Part238
