import BstLean.Part144Joint2
import BstLean.Part144StructT

/-!
# Part 144, the joint step with no event on `τ`, all widths

Role: `delegations/statements/p144-spec.md`, item 2.

* **`sampleFailsT_of`**: with a lower bound `Tl ≤ Φ̄(t0)`, `κ = φ(t0)/(2t0)`, `A = 2(Tl + κ·t0²)`,
  `b = 2κ·k/4` (the block bound with both signs), `α = 2A(k − 1)/k`, `β = A³k/(4b²)`,
  `2 ≤ k ≤ 4t0²`, and `C_m`, `v₀` with
  `A − b ≤ C_m`, `2A/k ≤ C_m`, `α < C_m`, `0 ≤ v₀ ≤ 1`, `(A − b)(C_m − α) ≤ 2β·C_m·v₀`,
  `β ≤ (C_m − α)(1 − v₀)²`: `Pr(|ĝ_k − B| > sd/2) ≥ (A − b) − C_m·e²/c²`.
  Tonelli over the last row of `F` (the block bound in the tangent form), then over the inputs
  (the moments of `Part144Moment`), then over the networks (the kernel bound `‖kD − c‖₂ ≤ e`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part144

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139
  BstLean.Part142

variable {N mW n mA mF : ℕ}

/-- **The mean of `k` exact samples fails, all widths, no event on `τ`.** With a lower bound
`Tl ≤ Φ̄(t0)`, `κ = φ(t0)/(2t0)`, `A = 2(Tl + κ·t0²)`, `b = 2κ·k/4`, `α = 2A(k − 1)/k`,
`β = A³k/(4b²)`, for `2 ≤ k ≤ 4t0²`, `2(Φ̄(t0) + κ·t0²) ≤ Φ̄(1)`, and `C_m`, `v₀` with
`A − b ≤ C_m`, `2A/k ≤ C_m`,
`α < C_m`, `0 ≤ v₀ ≤ 1`, `(A − b)(C_m − α) ≤ 2β·C_m·v₀`, `β ≤ (C_m − α)(1 − v₀)²`:
if `‖kD − c‖₂ ≤ e` and `c > 0`, then `Pr(|ĝ_k − B| > sd/2) ≥ (A − b) − C_m·e²/c²`.
(`C_m` can be taken about `α + β + (A − b)`.) -/
theorem sampleFailsT_of (hn : 1 ≤ n) (hN : 1 ≤ N) (hmF : 1 ≤ mF) {k : ℕ} (hk2 : 2 ≤ k) {c e : ℝ}
    (hc : 0 < c)
    (hD : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF => kD ω - c) e) {t0 Tl Cm v0 : ℝ}
    (ht0 : 0 < t0) (hTl0 : 0 ≤ Tl) (hTl : Tl ≤ (gaussianReal 0 1).real (Ioi t0))
    (hA1 : 2 * ((gaussianReal 0 1).real (Ioi t0) + gaussianPDFReal 0 1 t0 / (2 * t0) * t0 ^ 2) ≤
      (gaussianReal 0 1).real (Ioi 1))
    (hk4 : (k : ℝ) ≤ 4 * t0 ^ 2)
    (hC1 : (2 * (Tl + gaussianPDFReal 0 1 t0 / (2 * t0) * t0 ^ 2)) -
      2 * (gaussianPDFReal 0 1 t0 / (2 * t0) * ((k : ℝ) / 4)) ≤ Cm)
    (hC2 : 2 * (2 * (Tl + gaussianPDFReal 0 1 t0 / (2 * t0) * t0 ^ 2)) / (k : ℝ) ≤ Cm)
    (hCα : 2 * (2 * (Tl + gaussianPDFReal 0 1 t0 / (2 * t0) * t0 ^ 2)) * ((k : ℝ) - 1) /
      (k : ℝ) < Cm)
    (hv0 : 0 ≤ v0) (hv1 : v0 ≤ 1)
    (hav : ((2 * (Tl + gaussianPDFReal 0 1 t0 / (2 * t0) * t0 ^ 2)) -
        2 * (gaussianPDFReal 0 1 t0 / (2 * t0) * ((k : ℝ) / 4))) *
        (Cm - 2 * (2 * (Tl + gaussianPDFReal 0 1 t0 / (2 * t0) * t0 ^ 2)) * ((k : ℝ) - 1) /
          (k : ℝ)) ≤
      2 * ((2 * (Tl + gaussianPDFReal 0 1 t0 / (2 * t0) * t0 ^ 2)) ^ 3 * (k : ℝ) /
        (4 * (2 * (gaussianPDFReal 0 1 t0 / (2 * t0) * ((k : ℝ) / 4))) ^ 2)) * Cm * v0)
    (hβ : (2 * (Tl + gaussianPDFReal 0 1 t0 / (2 * t0) * t0 ^ 2)) ^ 3 * (k : ℝ) /
        (4 * (2 * (gaussianPDFReal 0 1 t0 / (2 * t0) * ((k : ℝ) / 4))) ^ 2) ≤
      (Cm - 2 * (2 * (Tl + gaussianPDFReal 0 1 t0 / (2 * t0) * t0 ^ 2)) * ((k : ℝ) - 1) / (k : ℝ)) *
        (1 - v0) ^ 2) :
    ((2 * (Tl + gaussianPDFReal 0 1 t0 / (2 * t0) * t0 ^ 2)) -
          2 * (gaussianPDFReal 0 1 t0 / (2 * t0) * ((k : ℝ) / 4))) - Cm * e ^ 2 / c ^ 2 ≤
      ((lawT N mW n mA mF).prod (uniK k N)).real (failSet k) := by
  have hk : 1 ≤ k := by omega
  have := uniK_prob hN k
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  set κ : ℝ := gaussianPDFReal 0 1 t0 / (2 * t0) with hκ
  have hφ : 0 < gaussianPDFReal 0 1 t0 := by
    rw [BstLean.Part131.pdf_eq]; positivity
  have hκ0 : 0 < κ := by positivity
  set Ac : ℝ := 2 * (Tl + κ * t0 ^ 2) with hAc
  set b : ℝ := 2 * (κ * ((k : ℝ) / 4)) with hb
  have hA0 : 0 ≤ Ac := by positivity
  have hApos : 0 < Ac := by positivity
  have hb0 : 0 < b := by positivity
  have hAb : 0 ≤ Ac - b := by
    have : κ * ((k : ℝ) / 4) ≤ κ * t0 ^ 2 := mul_le_mul_of_nonneg_left (by linarith) hκ0.le
    rw [hAc, hb]; linarith
  have hbA : b ≤ Ac := by linarith
  set CN : ℝ := Cm with hCN
  have hCN0 : 0 ≤ CN := by linarith
  set ν := (lawT N mW n mA mF).prod (uniK k N) with hν
  set T := lawT N mW n mA mF with hTd
  have mS := measurableSet_failSet (mW := mW) (n := n) (mA := mA) (mF := mF) hN k
  set f : Trip N mW n mA mF × (Fin k → Fin N → ℝ) → ℝ≥0∞ := (failSet k).indicator 1 with hf
  have mf : Measurable f := measurable_one.indicator mS
  set Fq : Trip N mW n mA mF → ℝ≥0∞ := fun t => ∫⁻ us, f (t, us) ∂uniK k N with hFq
  have mFq : Measurable Fq := mf.lintegral_prod_right'
  have eR : ν (failSet k) = ∫⁻ t, Fq t ∂T := by
    rw [hν, ← lintegral_indicator_one mS, lintegral_prod _ mf.aemeasurable]
  -- the lower bound, a function of `(W, A, F₁, F₂)`
  set Lr : Trip N mW n mA mF → ℝ :=
    fun t => (Ac - b) - CN / c ^ 2 * QD c ((t.1, t.2.1, t.2.1, t.2.2) : Rest N mW n mA mF)
    with hLr
  have mLr : Measurable Lr := measurable_const.sub ((measurable_QDT hN c).const_mul _)
  set gL : Trip N mW n mA mF → ℝ≥0∞ := fun t => ENNReal.ofReal (Lr t) with hgL
  have mgL : Measurable gL := ENNReal.measurable_ofReal.comp mLr
  -- the innermost step
  have h5 : ∀ (W : MlpParam N mW n) (A : MlpParam n mA n) (F₁ : Matrix (Fin mF) (Fin n) ℝ)
      (F₂ : Matrix (Fin mF) (Fin mF) ℝ),
      ∫⁻ F₃, gL (W, A, F₁, F₂, F₃) ∂gaussMat 1 mF (2 / (mF : ℝ)) ≤
        ∫⁻ F₃, Fq (W, A, F₁, F₂, F₃) ∂gaussMat 1 mF (2 / (mF : ℝ)) := by
    intro W A F₁ F₂
    have hconst : ∀ F₃ : Matrix (Fin 1) (Fin mF) ℝ,
        gL (W, A, F₁, F₂, F₃) = gL (W, A, F₁, F₂, 0) := by
      intro F₃
      simp only [hgL, hLr]
      rw [QD_F3 c W A A F₁ F₂ F₃ 0]
    simp_rw [hconst]
    rw [lintegral_const, measure_univ, mul_one]
    -- swap the two integrals
    have mpair : Measurable (fun q : Matrix (Fin 1) (Fin mF) ℝ × (Fin k → Fin N → ℝ) =>
        (((W, A, F₁, F₂, q.1), q.2) : Trip N mW n mA mF × (Fin k → Fin N → ℝ))) :=
      (measurable_const.prodMk (measurable_const.prodMk (measurable_const.prodMk
        (measurable_const.prodMk measurable_fst)))).prodMk measurable_snd
    have hsw : ∫⁻ F₃, Fq (W, A, F₁, F₂, F₃) ∂gaussMat 1 mF (2 / (mF : ℝ)) =
        ∫⁻ us, ∫⁻ F₃, f ((W, A, F₁, F₂, F₃), us) ∂gaussMat 1 mF (2 / (mF : ℝ)) ∂uniK k N := by
      simp only [hFq]
      exact lintegral_lintegral_swap
        (f := fun (F₃ : Matrix (Fin 1) (Fin mF) ℝ) (us : Fin k → Fin N → ℝ) =>
          f ((W, A, F₁, F₂, F₃), us)) (mf.comp mpair).aemeasurable
    rw [hsw]
    have hin : ∀ us : Fin k → Fin N → ℝ,
        ∫⁻ F₃, f ((W, A, F₁, F₂, F₃), us) ∂gaussMat 1 mF (2 / (mF : ℝ)) =
          (gaussMat 1 mF (2 / (mF : ℝ)))
            {F₃ | sdn W A (F₁, F₂, F₃) / 2 <
              |gMean k W A (F₁, F₂, F₃) us - Bn W A (F₁, F₂, F₃)|} := by
      intro us
      have hsl : MeasurableSet {F₃ : Matrix (Fin 1) (Fin mF) ℝ |
          ((W, A, F₁, F₂, F₃), us) ∈ failSet k} :=
        mS.preimage (f := fun F₃ : Matrix (Fin 1) (Fin mF) ℝ =>
          (((W, A, F₁, F₂, F₃), us) : Trip N mW n mA mF × (Fin k → Fin N → ℝ)))
          ((measurable_const.prodMk (measurable_const.prodMk (measurable_const.prodMk
            (measurable_const.prodMk measurable_id)))).prodMk measurable_const)
      have e : (fun F₃ : Matrix (Fin 1) (Fin mF) ℝ => f ((W, A, F₁, F₂, F₃), us)) =
          {F₃ : Matrix (Fin 1) (Fin mF) ℝ |
            ((W, A, F₁, F₂, F₃), us) ∈ failSet k}.indicator 1 := by
        funext F₃
        by_cases h : (((W, A, F₁, F₂, F₃), us) : Trip N mW n mA mF × (Fin k → Fin N → ℝ)) ∈
            failSet k
        · rw [hf, Set.indicator_of_mem h, Set.indicator_of_mem
            (show F₃ ∈ {F₃ : Matrix (Fin 1) (Fin mF) ℝ | ((W, A, F₁, F₂, F₃), us) ∈ failSet k}
              from h)]
          rfl
        · rw [hf, Set.indicator_of_notMem h, Set.indicator_of_notMem
            (show F₃ ∉ {F₃ : Matrix (Fin 1) (Fin mF) ℝ | ((W, A, F₁, F₂, F₃), us) ∈ failSet k}
              from h)]
      rw [e, lintegral_indicator_one hsl]
      rfl
    simp_rw [hin]
    have hτ0 := tauR_nonneg hN W A F₁ F₂
    have hLr0 : Lr (W, A, F₁, F₂, 0) =
        (Ac - b) - CN / c ^ 2 * QD c ((W, A, A, F₁, F₂, 0) : Rest N mW n mA mF) := rfl
    have hgv : gL (W, A, F₁, F₂, 0) = ENNReal.ofReal (Lr (W, A, F₁, F₂, 0)) := rfl
    rw [hgv]
    by_cases hGm : 0 < tauR W A F₁ F₂ ∧ tauR W A F₁ F₂ ≤ 2 * c
    · obtain ⟨hτpos, hτhi⟩ := hGm
      obtain ⟨hB, hI⟩ := lip_intT hn hN W A F₁ F₂ hmF hk2 A (0 : Matrix (Fin 1) (Fin mF) ℝ)
        hApos hb0 hbA hc hτpos hC1 hC2 hCα hv0 hv1 hav hβ
      have hpt : ∀ us : Fin k → Fin N → ℝ,
          ENNReal.ofReal ((Ac - b * tauR W A F₁ F₂ / c) +
            b * tauR W A F₁ F₂ / c ^ 2 * (xR k W A F₁ F₂ us - c) -
            Ac / c ^ 2 * (xR k W A F₁ F₂ us - c) ^ 2 -
            Ac ^ 3 * (k : ℝ) ^ 2 / (4 * (b * tauR W A F₁ F₂) ^ 2) * wR k W A F₁ F₂ us) ≤
          (gaussMat 1 mF (2 / (mF : ℝ)))
            {F₃ | sdn W A (F₁, F₂, F₃) / 2 <
              |gMean k W A (F₁, F₂, F₃) us - Bn W A (F₁, F₂, F₃)|} := by
        intro us
        have hc2 := cond_lipT hn hN W A F₁ F₂ hmF hk us ht0 hc hTl0 hTl hA1 hk4 hτpos hτhi
        rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
        exact hc2
      by_cases hLpos : Lr (W, A, F₁, F₂, 0) ≤ 0
      · rw [ENNReal.ofReal_of_nonpos hLpos]
        exact bot_le
      · have hLp : 0 < Lr (W, A, F₁, F₂, 0) := not_le.mp hLpos
        refine le_trans ?_ (lintegral_mono hpt)
        refine le_trans ?_ (ofReal_integral_le_lintegral (hB.integrable _))
        refine ENNReal.ofReal_le_ofReal ?_
        have hI' : Lr (W, A, F₁, F₂, 0) ≤ max 0 (∫ us, ((Ac - b * tauR W A F₁ F₂ / c) +
            b * tauR W A F₁ F₂ / c ^ 2 * (xR k W A F₁ F₂ us - c) -
            Ac / c ^ 2 * (xR k W A F₁ F₂ us - c) ^ 2 -
            Ac ^ 3 * (k : ℝ) ^ 2 / (4 * (b * tauR W A F₁ F₂) ^ 2) * wR k W A F₁ F₂ us)
            ∂uniK k N) := by
          refine le_trans (le_of_eq ?_) hI
          rw [hLr0, hCN]
          ring
        rcases le_max_iff.mp hI' with h0 | h0
        · exact absurd h0 (not_le.mpr hLp)
        · exact h0
    · -- `τ = 0` or `τ > 2c`: `(τ − c)² ≥ c²`, so the lower bound is `≤ 0`
      have hq := QD_ge hn hN W A F₁ F₂ hmF A (0 : Matrix (Fin 1) (Fin mF) ℝ) c
      have h1 : 0 ≤ (2 / (mF : ℝ)) ^ 2 * radV (uniformSphere N) (zU W A F₁ F₂) / 2 := by
        have : 0 ≤ radV (uniformSphere N) (zU W A F₁ F₂) := by
          unfold radV; exact integral_nonneg fun _ => sq_nonneg _
        positivity
      have h2 : 0 ≤ fR W A F₁ F₂ ^ 2 := sq_nonneg _
      have h3 : c ^ 2 ≤ (tauR W A F₁ F₂ - c) ^ 2 := by
        by_cases hz : 0 < tauR W A F₁ F₂
        · have hbig : 2 * c < tauR W A F₁ F₂ := by
            by_contra hcon
            exact hGm ⟨hz, not_lt.mp hcon⟩
          nlinarith
        · have hz0 : tauR W A F₁ F₂ = 0 := le_antisymm (not_lt.mp hz) hτ0
          rw [hz0]; ring_nf; exact le_refl _
      have hQc : c ^ 2 ≤ QD c ((W, A, A, F₁, F₂, 0) : Rest N mW n mA mF) := by linarith
      have hK0' : 0 ≤ CN / c ^ 2 := by positivity
      have h5 : Lr (W, A, F₁, F₂, 0) ≤ 0 := by
        rw [hLr0]
        have h7 : CN / c ^ 2 * c ^ 2 ≤
            CN / c ^ 2 * QD c ((W, A, A, F₁, F₂, 0) : Rest N mW n mA mF) :=
          mul_le_mul_of_nonneg_left hQc hK0'
        have e8 : CN / c ^ 2 * c ^ 2 = CN := by field_simp
        have h9 : Ac - b ≤ CN := by rw [hCN]; exact hC1
        linarith
      rw [ENNReal.ofReal_of_nonpos h5]
      exact bot_le
  have mT5 : ∀ (W : MlpParam N mW n) (A : MlpParam n mA n) (F₁ : Matrix (Fin mF) (Fin n) ℝ),
      Measurable (fun y : Matrix (Fin mF) (Fin mF) ℝ × Matrix (Fin 1) (Fin mF) ℝ =>
        ((W, A, F₁, y) : Trip N mW n mA mF)) := fun W A F₁ =>
    measurable_const.prodMk (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have mT4 : ∀ (W : MlpParam N mW n) (A : MlpParam n mA n),
      Measurable (fun y : MlpParam n mF 1 => ((W, A, y) : Trip N mW n mA mF)) := fun W A =>
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have mT3 : ∀ W : MlpParam N mW n,
      Measurable (fun y : MlpParam n mA n × MlpParam n mF 1 =>
        ((W, y) : Trip N mW n mA mF)) := fun W =>
    measurable_const.prodMk measurable_id
  have h4 : ∀ (W : MlpParam N mW n) (A : MlpParam n mA n) (F₁ : Matrix (Fin mF) (Fin n) ℝ),
      ∫⁻ y, gL (W, A, F₁, y)
          ∂((gaussMat mF mF (2 / (mF : ℝ))).prod (gaussMat 1 mF (2 / (mF : ℝ)))) ≤
        ∫⁻ y, Fq (W, A, F₁, y)
          ∂((gaussMat mF mF (2 / (mF : ℝ))).prod (gaussMat 1 mF (2 / (mF : ℝ)))) :=
    fun W A F₁ => lintegral_prod_mono'
      (f := fun y => gL (W, A, F₁, y)) (g := fun y => Fq (W, A, F₁, y))
      (mgL.comp (mT5 W A F₁)) (mFq.comp (mT5 W A F₁)) (fun F₂ => h5 W A F₁ F₂)
  have h3 : ∀ (W : MlpParam N mW n) (A : MlpParam n mA n),
      ∫⁻ y, gL (W, A, y) ∂mlpGauss n mF 1 ≤ ∫⁻ y, Fq (W, A, y) ∂mlpGauss n mF 1 :=
    fun W A => lintegral_prod_mono'
      (f := fun y => gL (W, A, y)) (g := fun y => Fq (W, A, y))
      (mgL.comp (mT4 W A)) (mFq.comp (mT4 W A)) (fun F₁ => h4 W A F₁)
  have h2 : ∀ W : MlpParam N mW n,
      ∫⁻ y, gL (W, y) ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) ≤
        ∫⁻ y, Fq (W, y) ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) :=
    fun W => lintegral_prod_mono'
      (f := fun y => gL (W, y)) (g := fun y => Fq (W, y))
      (mgL.comp (mT3 W)) (mFq.comp (mT3 W)) (fun A => h3 W A)
  have h1 : ∫⁻ t, gL t ∂T ≤ ∫⁻ t, Fq t ∂T := by
    rw [hTd]; unfold lawT
    exact lintegral_prod_mono' mgL mFq h2
  -- the integral of the lower bound: pointwise `ofReal (A − b) − ofReal (C_m·QD/c²) ≤ gL`
  set vv : Trip N mW n mA mF → ℝ≥0∞ := fun t =>
    ENNReal.ofReal (CN / c ^ 2 * QD c ((t.1, t.2.1, t.2.1, t.2.2) : Rest N mW n mA mF)) with hvv
  have mvv : Measurable vv :=
    ENNReal.measurable_ofReal.comp ((measurable_QDT hN c).const_mul _)
  have hK0 : 0 ≤ CN / c ^ 2 := by positivity
  have hpw : ∀ t, ENNReal.ofReal (Ac - b) - vv t ≤ gL t := by
    intro t
    simp only [hgL, hvv, hLr]
    rw [ENNReal.ofReal_sub _ (mul_nonneg hK0 (QD_nonneg c _))]
  have hvI : ∫⁻ t, vv t ∂T ≤ ENNReal.ofReal (CN / c ^ 2 * e ^ 2) := lintegral_QD_le hN hD hK0
  have h6 : ENNReal.ofReal (Ac - b) - ENNReal.ofReal (CN / c ^ 2 * e ^ 2) ≤
      ν (failSet k) := by
    rw [eR]
    refine le_trans ?_ h1
    refine le_trans ?_ (lintegral_mono hpw)
    refine le_trans ?_ (lintegral_sub_le vv (fun _ => ENNReal.ofReal (Ac - b)) mvv)
    rw [lintegral_const, measure_univ, mul_one]
    exact tsub_le_tsub_left hvI _
  have h7 := ENNReal.toReal_mono (measure_ne_top ν (failSet k)) h6
  have h8 := ENNReal.le_toReal_sub (a := ENNReal.ofReal (Ac - b))
    (b := ENNReal.ofReal (CN / c ^ 2 * e ^ 2)) ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hAb, ENNReal.toReal_ofReal (by positivity)] at h8
  have h9 : (Ac - b) - CN / c ^ 2 * e ^ 2 ≤ ν.real (failSet k) := h8.trans h7
  have e12 : CN * e ^ 2 / c ^ 2 = CN / c ^ 2 * e ^ 2 := by ring
  rw [e12]
  exact h9

end BstLean.Part144

open BstLean.Part144 in
#print axioms sampleFailsT_of
