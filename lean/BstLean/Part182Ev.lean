import BstLean.Part182Def
import BstLean.Part160Event

/-!
# Part 182 (file `Ev`): the covariance event `E_cov` and its Markov charge from the two-input hypothesis

No proof is left open; no `native_decide` or `axiom` is used.

Paper source: Proposition `t7:p04:certificate` (proof, first paragraph): "Let `𝒢_A` be the
symmetric subset of `Γ₀` where the appropriate pair bounds hold. … Fubini gives
`E_A P_{ξ,ξ'}(Γ₀ \ 𝒢_A) ≤ δ₂`. Define `E_cov` by this mass being at most `δ₂/ε_M`. Markov gives its
stated charge."

* `badSet n t0 z0 t1 lam`: the set of `(((c, τ), (A₁, A₂)), (ξ, ξ'))` with `(ξ, ξ') ∈ Γ(c)` and the
  pair bound `n λ` failing at `x = sphPt (c + τξ)`, `x' = sphPt (c + τξ')`. Measurable
  (`measurableSet_badSet`).
* `badMass`: the `ξ ⊗ ξ'` mass of its section; `SCov n t0 z0 t1 lam M = {badMass ≤ M}`
  (`measurableSet_SCov`).
* **`SCov_charge`**: if every pair of `Γ(c)` has `cm ≤ x·x' ≤ cp` and `TI_hyp n cm cp lam δ`, then
  `Pr_{A₁,A₂}(badMass > δ/ε) ≤ ε`.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part160
open BstLean.Part153 (nrm jacT nuA)

variable {n : ℕ}

lemma measurable_uC : Measurable (uC (n := n)) := by
  unfold uC nrm normSq
  fun_prop

lemma measurable_perpC_joint :
    Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => perpC q.1 q.2) := by
  unfold perpC
  have hu : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => uC q.1) :=
    measurable_uC.comp measurable_fst
  have hd : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => uC q.1 ⬝ᵥ q.2) := by
    unfold dotProduct
    refine Finset.measurable_sum _ fun i _ => ?_
    exact ((measurable_pi_apply i).comp hu).mul ((measurable_pi_apply i).comp measurable_snd)
  exact measurable_snd.sub (hd.smul hu)

lemma measurable_dot {α : Type*} [MeasurableSpace α] {f g : α → Fin n → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun a => f a ⬝ᵥ g a) := by
  unfold dotProduct
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hf).mul ((measurable_pi_apply i).comp hg)

lemma measurable_normSq' {α : Type*} [MeasurableSpace α] {f : α → Fin n → ℝ}
    (hf : Measurable f) : Measurable (fun a => normSq (f a)) := by
  unfold normSq
  exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hf).pow_const 2

lemma measurable_tmul {α : Type*} [MeasurableSpace α] {p q r : ℕ}
    {f : α → Matrix (Fin p) (Fin q) ℝ} {g : α → Matrix (Fin p) (Fin r) ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun a => (f a)ᵀ * g a) := by
  have hc : Continuous (fun z : Matrix (Fin p) (Fin q) ℝ × Matrix (Fin p) (Fin r) ℝ =>
      z.1ᵀ * z.2) := continuous_fst.matrix_transpose.matrix_mul continuous_snd
  exact hc.measurable.comp (hf.prodMk hg)

/-- `Ω(c)` is jointly measurable in `(c, ξ)`. -/
lemma measurableSet_OmegaS_joint (t0 z0 : ℝ) :
    MeasurableSet {q : (Fin n → ℝ) × (Fin n → ℝ) | q.2 ∈ OmegaS q.1 t0 z0} := by
  have hd : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => uC q.1 ⬝ᵥ q.2) :=
    measurable_dot (measurable_uC.comp measurable_fst) measurable_snd
  have hN : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => normSq q.2) :=
    measurable_normSq' measurable_snd
  refine (measurableSet_le hd.abs measurable_const).inter
    ((measurableSet_le measurable_const hN).inter (measurableSet_le hN measurable_const))

/-- The joint bad set of the covariance event. -/
def badSet (n : ℕ) (t0 z0 t1 lam : ℝ) : Set (AgFam n × ((Fin n → ℝ) × (Fin n → ℝ))) :=
  {q | q.2 ∈ GammaS q.1.1.1 t0 z0 t1 ∧
    pairBad q.1.2.1 q.1.2.2 lam (sphPt (q.1.1.1 + q.1.1.2 • q.2.1))
      (sphPt (q.1.1.1 + q.1.1.2 • q.2.2))}

lemma measurableSet_badSet (t0 z0 t1 lam : ℝ) : MeasurableSet (badSet n t0 z0 t1 lam) := by
  -- the pieces
  have hc : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) => q.1.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_fst)
  have hτ : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) => q.1.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_fst)
  have hA : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) => q.1.2) :=
    measurable_snd.comp measurable_fst
  have h1 : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) => q.2.1) :=
    measurable_fst.comp measurable_snd
  have h2 : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) => q.2.2) :=
    measurable_snd.comp measurable_snd
  have hO := measurableSet_OmegaS_joint (n := n) t0 z0
  have hO1 : MeasurableSet {q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) |
      q.2.1 ∈ OmegaS q.1.1.1 t0 z0} := (hc.prodMk h1) hO
  have hO2 : MeasurableSet {q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) |
      q.2.2 ∈ OmegaS q.1.1.1 t0 z0} := (hc.prodMk h2) hO
  have hp1 : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) => perpC q.1.1.1 q.2.1) :=
    measurable_perpC_joint.comp (hc.prodMk h1)
  have hp2 : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) => perpC q.1.1.1 q.2.2) :=
    measurable_perpC_joint.comp (hc.prodMk h2)
  have hG3 : MeasurableSet {q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) |
      |perpC q.1.1.1 q.2.1 ⬝ᵥ perpC q.1.1.1 q.2.2| ≤ t1 * gPlus n z0} :=
    measurableSet_le (measurable_dot hp1 hp2).abs measurable_const
  have hx1 : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      sphPt (q.1.1.1 + q.1.1.2 • q.2.1)) :=
    measurable_sphPt.comp (hc.add (hτ.smul h1))
  have hx2 : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      sphPt (q.1.1.1 + q.1.1.2 • q.2.2)) :=
    measurable_sphPt.comp (hc.add (hτ.smul h2))
  have hJ1 : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      jacT q.1.2.1 q.1.2.2 (sphPt (q.1.1.1 + q.1.1.2 • q.2.1))) :=
    by
      have h := (BstLean.Part153.measurable_jacT_joint (n := n) (m := mA n) (m₂ := mA n)).comp
        (hA.prodMk hx1)
      simpa only [Function.comp_def] using h
  have hJ2 : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      jacT q.1.2.1 q.1.2.2 (sphPt (q.1.1.1 + q.1.1.2 • q.2.2))) :=
    by
      have h := (BstLean.Part153.measurable_jacT_joint (n := n) (m := mA n) (m₂ := mA n)).comp
        (hA.prodMk hx2)
      simpa only [Function.comp_def] using h
  have hM := measurable_tmul hJ1 hJ2
  have hB : MeasurableSet {q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) |
      pairBad q.1.2.1 q.1.2.2 lam (sphPt (q.1.1.1 + q.1.1.2 • q.2.1))
        (sphPt (q.1.1.1 + q.1.1.2 • q.2.2))} := by
    unfold pairBad
    exact measurableSet_lt measurable_const (opN_continuous.measurable.comp hM)
  have e : badSet n t0 z0 t1 lam =
      ({q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) | q.2.1 ∈ OmegaS q.1.1.1 t0 z0} ∩
        ({q | q.2.2 ∈ OmegaS q.1.1.1 t0 z0} ∩
          {q | |perpC q.1.1.1 q.2.1 ⬝ᵥ perpC q.1.1.1 q.2.2| ≤ t1 * gPlus n z0})) ∩
      {q | pairBad q.1.2.1 q.1.2.2 lam (sphPt (q.1.1.1 + q.1.1.2 • q.2.1))
        (sphPt (q.1.1.1 + q.1.1.2 • q.2.2))} := by
    ext q
    simp only [badSet, GammaS, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [e]
  exact (hO1.inter (hO2.inter hG3)).inter hB

/-- The pair mass of the bad pairs at one `((c, τ), (A₁, A₂))`. -/
noncomputable def badMass (n : ℕ) (t0 z0 t1 lam : ℝ) (x : AgFam n) : ℝ :=
  ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real {p | (x, p) ∈ badSet n t0 z0 t1 lam}

/-- **The covariance event**: the pair mass of the bad pairs is at most `M`. -/
def SCov (n : ℕ) (t0 z0 t1 lam M : ℝ) : Set (AgFam n) :=
  {x | badMass n t0 z0 t1 lam x ≤ M}

lemma measurable_badMass (t0 z0 t1 lam : ℝ) : Measurable (badMass n t0 z0 t1 lam) := by
  unfold badMass Measure.real
  have hP : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  exact (measurable_measure_prodMk_left (measurableSet_badSet t0 z0 t1 lam)).ennreal_toReal

theorem measurableSet_SCov (t0 z0 t1 lam M : ℝ) : MeasurableSet (SCov n t0 z0 t1 lam M) :=
  measurableSet_le (measurable_badMass t0 z0 t1 lam) measurable_const

/-- **The charge of the covariance event** (Fubini and Markov): if every pair `(ξ, ξ') ∈ Γ(c)`
has `cm ≤ x·x' ≤ cp` (`x = sphPt (c + τξ)`) and the two-input hypothesis holds for `(cm, cp, λ, δ)`,
then `Pr_{A₁,A₂}(badMass > δ/ε) ≤ ε`. -/
theorem SCov_charge (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) {t0 z0 t1 lam cm cp δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hgeo : ∀ p ∈ GammaS c t0 z0 t1,
      cm ≤ sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ∧
        sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ≤ cp)
    (hTI : TI_hyp n cm cp lam δ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SCov n t0 z0 t1 lam (δ / ε)} ≤ ε := by
  classical
  have hP : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hPA : IsProbabilityMeasure (nuA n) := by
    unfold nuA BstLean.Part130.gaussMat; infer_instance
  set μ2 := (stdGauss (Fin n)).prod (stdGauss (Fin n)) with hμ2
  -- the section set in `(θ, p)`
  set S : Set ((Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) ×
      ((Fin n → ℝ) × (Fin n → ℝ))) := {q | (((c, τ), q.1), q.2) ∈ badSet n t0 z0 t1 lam} with hS
  have hSm : MeasurableSet S := by
    have hf : Measurable (fun q : (Matrix (Fin (mA n)) (Fin n) ℝ ×
        Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        (((c, τ), q.1), q.2)) :=
      ((measurable_const.prodMk measurable_fst)).prodMk measurable_snd
    exact hf (measurableSet_badSet t0 z0 t1 lam)
  -- Tonelli: `∫⁻ θ, μ2(S_θ) = ∫⁻ p, nuA(S^p) ≤ δ`
  have hT : ∫⁻ θ, μ2 (Prod.mk θ ⁻¹' S) ∂(nuA n) ≤ ENNReal.ofReal δ := by
    rw [← Measure.prod_apply hSm, Measure.prod_apply_symm hSm]
    calc ∫⁻ p, (nuA n) ((fun θ => (θ, p)) ⁻¹' S) ∂μ2
        ≤ ∫⁻ _p, ENNReal.ofReal δ ∂μ2 := by
          refine lintegral_mono fun p => ?_
          by_cases hp : p ∈ GammaS c t0 z0 t1
          · obtain ⟨h1, h2⟩ := hgeo p hp
            have hb := hTI _ _ (normSq_sphPt hn _) (normSq_sphPt hn _) h1 h2
            have e : (fun θ => (θ, p)) ⁻¹' S ⊆ {θ | pairBad θ.1 θ.2 lam
                (sphPt (c + τ • p.1)) (sphPt (c + τ • p.2))} := by
              intro θ hθ
              exact hθ.2
            refine (measure_mono e).trans ?_
            rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
            exact ENNReal.ofReal_le_ofReal hb
          · have e : (fun θ => (θ, p)) ⁻¹' S = ∅ := by
              ext θ
              simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
              intro hθ
              exact hp hθ.1
            rw [e, measure_empty]
            exact bot_le
      _ = ENNReal.ofReal δ := by
          rw [lintegral_const, measure_univ, mul_one]
  -- Markov
  have hset : {θ | ((c, τ), θ) ∉ SCov n t0 z0 t1 lam (δ / ε)} =
      {θ | ENNReal.ofReal (δ / ε) < μ2 (Prod.mk θ ⁻¹' S)} := by
    ext θ
    simp only [SCov, badMass, Set.mem_setOf_eq, not_le]
    have e : {p | (((c, τ), θ), p) ∈ badSet n t0 z0 t1 lam} = Prod.mk θ ⁻¹' S := rfl
    rw [e, ← hμ2]
    constructor
    · intro h
      have h0 : 0 ≤ δ / ε := div_nonneg hδ hε.le
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ2 (Prod.mk θ ⁻¹' S))]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt h0 h)).2 h
    · intro h
      have := ENNReal.toReal_strict_mono (measure_ne_top μ2 _) h
      rwa [ENNReal.toReal_ofReal (div_nonneg hδ hε.le)] at this
  rw [hset]
  have hmeas : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => μ2 (Prod.mk θ ⁻¹' S)) :=
    measurable_measure_prodMk_left hSm
  by_cases hδ0 : δ = 0
  · -- then the mass is zero almost surely
    subst hδ0
    have hz : ∫⁻ θ, μ2 (Prod.mk θ ⁻¹' S) ∂(nuA n) = 0 := by
      simpa using hT
    have hae := (lintegral_eq_zero_iff hmeas).1 hz
    have h0 : (nuA n) {θ | ENNReal.ofReal (0 / ε) < μ2 (Prod.mk θ ⁻¹' S)} = 0 := by
      refine measure_mono_null (fun θ hθ => ?_) (ae_iff.1 hae)
      simp only [Set.mem_setOf_eq, zero_div, ENNReal.ofReal_zero] at hθ ⊢
      exact ne_of_gt hθ
    rw [Measure.real, h0, ENNReal.toReal_zero]
    exact hε.le
  have hδp : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
  have hpos : ENNReal.ofReal (δ / ε) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact div_pos hδp hε
  have hmk := mul_meas_ge_le_lintegral₀ (μ := nuA n) hmeas.aemeasurable (ENNReal.ofReal (δ / ε))
  have hsub : {θ | ENNReal.ofReal (δ / ε) < μ2 (Prod.mk θ ⁻¹' S)} ⊆
      {θ | ENNReal.ofReal (δ / ε) ≤ μ2 (Prod.mk θ ⁻¹' S)} := fun θ h => le_of_lt (show ENNReal.ofReal (δ / ε) < μ2 (Prod.mk θ ⁻¹' S) from h)
  have h1 : ENNReal.ofReal (δ / ε) * (nuA n) {θ | ENNReal.ofReal (δ / ε) < μ2 (Prod.mk θ ⁻¹' S)} ≤
      ENNReal.ofReal δ := by
    refine le_trans ?_ (hmk.trans hT)
    gcongr
  have h1' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg hδ hε.le),
    ENNReal.toReal_ofReal hδ] at h1'
  rw [Measure.real]
  set X := ((nuA n) {θ | ENNReal.ofReal (δ / ε) < μ2 (Prod.mk θ ⁻¹' S)}).toReal
  have hq : 0 < δ / ε := div_pos hδp hε
  have : X ≤ δ / (δ / ε) := by rw [le_div_iff₀ hq]; linarith
  rwa [div_div_cancel₀ hδp.ne'] at this

end BstLean.Part182

open BstLean.Part182 in
#print axioms SCov_charge
open BstLean.Part182 in
#print axioms measurableSet_SCov
