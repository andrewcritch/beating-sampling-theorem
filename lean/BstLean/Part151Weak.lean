import BstLean.Part151Cond
import BstLean.Part151Moment
import BstLean.Part151FStage
import BstLean.Part150Arith2

/-!
# Part 151, item 5: the mean of the conditional variance `V′` from the second-moment bounds of
Parts 149 and 150

Role: `delegations/statements/p151-spec.md`, item 5.

For a set `X` of values of `(W, (A₁, A₂))`, `EX k X` is the event `(W, (A₁, A₂)) ∈ X` as a set of
the fixed variables `((W, A, (F₁, F₂)), η)`. It does not use `F`.

* **`lint_vHat`** (the bridge): `E[1_X·V′] = E[1_X·(g − B′)²]`: the mean of the conditional
  variance on an event that does not use the last row of `F` is the second moment of the error.
* **`weakI`**: on the good event `X` of Part 150 (`goodX2 ∩ goodX3 ∩ goodX4`):
  `E[1_X·V′] ≤ IA`, where `IA` is a weighted sum of the four second-moment bounds of Parts 149
  and 150 (`errA2_lint`: the stage of `A` with the exact centre; `errB_lint`: the mean-field
  centre; `errH_lint`: the displacement of the centre `bh`; `sampH_lint`: the `k` forward passes
  of `F`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part139 (gamK)
open BstLean.Part141 (cenA tauWA gA measurable_gA)
open BstLean.Part145 (Gwin goodWAG GoodEv0 goodEvFR)
open BstLean.Part149
open BstLean.Part150

variable {k n : ℕ}

/-- The event `(W, (A₁, A₂)) ∈ X`, as a set of the fixed variables. -/
def EX (k : ℕ) (X : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))) : Set (Fix k n) :=
  {ω | (ω.1.1, thA ω.1.2.1) ∈ X}

/-- The same event as a set of all variables `((W, A, F), η)`. -/
def TXJ (k : ℕ) (X : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))) : Set (Joint k n) :=
  {p | (p.1.1, thA p.1.2.1) ∈ X}

lemma EX_meas {X : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (hX : MeasurableSet X) :
    MeasurableSet (EX k X) := by
  have hm : Measurable (fun ω : Fix k n => (ω.1.1, thA ω.1.2.1)) :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_thA.comp (measurable_fst.comp (measurable_snd.comp measurable_fst)))
  exact hm hX

lemma fixP_eq_map : fixP k n = (jointP k n).map restJ := by
  have h := congrArg (Measure.map Prod.fst) (joint_map (k := k) (n := n))
  rw [Measure.map_map measurable_fst (measurable_restJ.prodMk measurable_rowJ)] at h
  have e : (Prod.fst ∘ fun p : Joint k n => (restJ p, rowJ p)) = restJ := rfl
  rw [e] at h
  rw [h]; simp

/-- **The bridge.** For a measurable set `X` of values of `(W, (A₁, A₂))` and a measurable
centre map `bh`: `E[1_X·V′] = E[1_X·(g − B′)²]`, with `g = gSampH bh k`, `B′ = gA`,
`V′ = vHat bh k = t_F·|Δ̂′|²`. -/
theorem lint_vHat (hn : 1 ≤ n) {bh : CMap n} (hbh : Measurable bh)
    {X : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (hX : MeasurableSet X) :
    ∫⁻ ω in EX k X, ENNReal.ofReal (vHat bh k ω) ∂fixP k n =
      ∫⁻ p, ENNReal.ofReal ((TXJ k X).indicator
        (fun p => (gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - gA p.1.1 p.1.2.1 p.1.2.2) ^ 2) p)
        ∂jointP k n := by
  have hE := EX_meas (k := k) hX
  have hlin2 : Measurable (fun q : Fix k n × Row n => ENNReal.ofReal (linJ bh k q.1 q.2 ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((measurable_linJ hbh k).pow_const 2)
  set Fn : Fix k n × Row n → ℝ≥0∞ :=
    (EX k X ×ˢ (univ : Set (Row n))).indicator
      (fun q => ENNReal.ofReal (linJ bh k q.1 q.2 ^ 2)) with hFn
  have mFn : Measurable Fn := hlin2.indicator (hE.prod MeasurableSet.univ)
  have e1 : ∀ p : Joint k n, ENNReal.ofReal ((TXJ k X).indicator
      (fun p => (gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - gA p.1.1 p.1.2.1 p.1.2.2) ^ 2) p) =
      Fn (restJ p, rowJ p) := by
    intro p
    by_cases hp : p ∈ TXJ k X
    · have hp' : (restJ p, rowJ p) ∈ EX k X ×ˢ (univ : Set (Row n)) := ⟨hp, mem_univ _⟩
      rw [indicator_of_mem hp, hFn, indicator_of_mem hp', struct151 hn bh p]
    · have hp' : (restJ p, rowJ p) ∉ EX k X ×ˢ (univ : Set (Row n)) := fun h => hp h.1
      rw [indicator_of_notMem hp, hFn, indicator_of_notMem hp', ENNReal.ofReal_zero]
  simp_rw [e1]
  have e2 : ∫⁻ p, Fn (restJ p, rowJ p) ∂jointP k n = ∫⁻ q, Fn q ∂(fixP k n).prod (rowP n) := by
    rw [← joint_map, lintegral_map mFn (measurable_restJ.prodMk measurable_rowJ)]
  rw [e2, hFn, lintegral_indicator (hE.prod MeasurableSet.univ), ← Measure.prod_restrict,
    Measure.restrict_univ, lintegral_prod _ hlin2.aemeasurable]
  refine lintegral_congr fun ω => ?_
  unfold linJ vHat rowP
  exact (row_sq_lintegral (by positivity) _).symm

/-! ## The weighted sum of the four second-moment bounds -/

lemma sq_add_le_w {η : ℝ} (hη : 0 < η) (x y : ℝ) :
    (x + y) ^ 2 ≤ (1 + η) * x ^ 2 + (1 + 1 / η) * y ^ 2 := by
  have h : 0 ≤ (η * x - y) ^ 2 / η := by positivity
  have e : (1 + η) * x ^ 2 + (1 + 1 / η) * y ^ 2 - (x + y) ^ 2 = (η * x - y) ^ 2 / η := by
    field_simp
    ring
  linarith

/-- The good event of Part 150 for the centre `bh`, as a set of values of `(W, (A₁, A₂))`. -/
def goodX234 (n : ℕ) (Δmax ΔXmax εD εQ Dmax : ℝ) (bh : CMap n) (D4 : ℝ) :
    Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n)) :=
  (goodX2 (Gwin n) Δmax ΔXmax ∩ goodX3 (Gwin n) εD εQ Dmax) ∩ goodX4 bh D4

/-- The bound of `E[1_good·V′]`: a weighted sum of the second-moment bounds of the four steps
(exact centre; mean-field centre; displacement of the centre; `k` forward passes of `F`). -/
noncomputable def IA (n k : ℕ) (Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb εD π₀ yhi ζ₃ dQb ξ y4
    η₃ η₄ η₅ : ℝ) : ℝ :=
  (1 + η₅) * ((1 + η₄) * ((1 + η₃) *
      (2 / (n : ℝ) * EA2 (6662 / 10000) Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb) +
        (1 + 1 / η₃) * (2 / (n : ℝ) * (2 / (1 - yhi)) * xiB n εD π₀ ζ₃ dQb)) +
      (1 + 1 / η₄) * (2 / (n : ℝ) * (2 / (1 - y4)) * ξ)) +
    (1 + 1 / η₅) * (4 / (n : ℝ) / k)

/-- **The mean of the conditional variance on the good event of Part 150**:
`E[1_good·V′] ≤ IA`. The hypotheses on the parameters are those of
`displaceSamp150_formula` (Part 150). -/
theorem weakI (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    {Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb εD εQ π₀ Dmax ρhi yhi ζ₃ dQb : ℝ}
    (hP : POK2 (6662 / 10000) (6969 / 10000) Δmax ΔXmax r₁ r₂ w g)
    (hP3 : POK3 (6969 / 10000) Δmax εD εQ π₀ Dmax ρhi yhi) (hζ₃ : 0 < ζ₃)
    (hdQ : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dQ1 n (mA n) q ≤ dQb)
    (hQ0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dQ1 n (mA n) q)
    (hη : 0 < η) (hζ : 0 < ζ) (hζ₂ : 0 < ζ₂)
    (hΔK : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dK2 n (mA n) q ≤ ΔKb)
    (hK0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dK2 n (mA n) q)
    (hΔX : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dX2 n (mA n) q ≤ ΔXb)
    (hX0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dX2 n (mA n) q)
    (hδb : cF2o (mA n) ≤ δb)
    {bh : CMap n} (hbh : Measurable bh) {D4 y4 : ℝ} (hD4 : 0 < D4)
    (hy4 : (√yhi + D4) ^ 2 ≤ y4) (hy41 : y4 < 1) {ξ : ℝ} (hξ0 : 0 ≤ ξ)
    (hξ : DispOK n (Gwin n) εD εQ bh ξ) {η₃ η₄ η₅ : ℝ} (hη₃ : 0 < η₃) (hη₄ : 0 < η₄)
    (hη₅ : 0 < η₅) :
    ∫⁻ ω in EX k (goodX234 n Δmax ΔXmax εD εQ Dmax bh D4), ENNReal.ofReal (vHat bh k ω)
        ∂fixP k n ≤
      ENNReal.ofReal (IA n k Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb εD π₀ yhi ζ₃ dQb ξ y4
        η₃ η₄ η₅) := by
  have hn1 : 1 ≤ n := by omega
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  have hG := (goodEvFR hn).to0
  have hwin := winOK2_149 hn
  have hy1 : 0 < 1 - yhi := by linarith [hP3.hy1]
  have hy41' : 0 < 1 - y4 := by linarith
  -- the four bounds
  have hA := errA2_lint hn hG hwin hP hη hζ hζ₂ hΔK hK0 hΔX hX0 hδb
  have hB := errB_lint (ΔXmax := ΔXmax) hn hG hwin hP.hΔmax hP.hA1 hP.hA2 hP3 hζ₃ hdQ hQ0
  have hH := errH_lint (ΔXmax := ΔXmax) hn hG hwin hP.hΔmax hP.hA1 hP.hA2 hP3 hbh hD4.le hy4
    hy41 hξ0 hξ
  set X := goodX234 n Δmax ΔXmax εD εQ Dmax bh D4 with hXdef
  have mX : MeasurableSet X :=
    ((goodX2_meas hG hn1 Δmax ΔXmax).inter (goodX3_meas hG hn1 εD εQ Dmax)).inter
      (measurableSet_le (measurable_dispH hbh) measurable_const)
  have hb : ∀ x ∈ X, normSq (bh x) ≤ (mA n : ℝ) / n := by
    rintro ⟨W, θ⟩ ⟨⟨hx2, hx3⟩, hx4⟩
    have h := bh_len hn hwin hP.hΔmax hP.hA1 hP.hA2 hP3 bh hD4.le hy4 hx2 hx3 hx4
    have hd0 : (0 : ℝ) < (mA n : ℝ) / n := by positivity
    calc normSq (bh (W, θ)) ≤ (mA n : ℝ) / n * y4 := h
      _ ≤ (mA n : ℝ) / n * 1 := mul_le_mul_of_nonneg_left hy41.le hd0.le
      _ = _ := mul_one _
  have hS := sampH_lint hn1 hk hbh mX hb
  rw [lint_vHat hn1 hbh mX]
  -- pointwise domination
  set c2 : ℝ := (1 + η₅) * ((1 + η₄) * (1 + η₃)) with hc2
  set c3 : ℝ := (1 + η₅) * ((1 + η₄) * (1 + 1 / η₃)) with hc3
  set c4 : ℝ := (1 + η₅) * (1 + 1 / η₄) with hc4
  set c5 : ℝ := 1 + 1 / η₅ with hc5
  have hc20 : 0 ≤ c2 := by rw [hc2]; positivity
  have hc30 : 0 ≤ c3 := by rw [hc3]; positivity
  have hc40 : 0 ≤ c4 := by rw [hc4]; positivity
  have hc50 : 0 ≤ c5 := by rw [hc5]; positivity
  set SS : Joint k n → ℝ := fun p => (TXJ k X).indicator
    (fun p => (gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - gOutH bh p.1.1 p.1.2.1 p.1.2.2) ^ 2) p
    with hSS
  have hSS0 : ∀ p, 0 ≤ SS p := fun p => indicator_nonneg (fun _ _ => sq_nonneg _) _
  have hdom : ∀ p : Joint k n, (TXJ k X).indicator
      (fun p => (gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - gA p.1.1 p.1.2.1 p.1.2.2) ^ 2) p ≤
      c2 * dOut2 (Gwin n) Δmax ΔXmax p.1 + c3 * dOut3 (Gwin n) Δmax ΔXmax εD εQ Dmax p.1 +
        c4 * dOut4 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 p.1 + c5 * SS p := by
    intro p
    have n2 := dOut2_nonneg (Gwin n) Δmax ΔXmax p.1
    have n3 := dOut3_nonneg (Gwin n) Δmax ΔXmax εD εQ Dmax p.1
    have n4 := dOut4_nonneg (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 p.1
    have n5 := hSS0 p
    by_cases hp : p ∈ TXJ k X
    · have hp2 : p.1 ∈ goodT2 (Gwin n) Δmax ΔXmax := hp.1.1
      have hp23 : p.1 ∈ goodT23 (Gwin n) Δmax ΔXmax εD εQ Dmax := ⟨hp.1.1, hp.1.2⟩
      have hp234 : p.1 ∈ goodT234 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 := ⟨hp23, hp.2⟩
      rw [indicator_of_mem hp]
      simp only [hSS]
      unfold dOut2 dOut3 dOut4
      rw [indicator_of_mem hp2, indicator_of_mem hp23, indicator_of_mem hp234,
        indicator_of_mem hp]
      set s := gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - gOutH bh p.1.1 p.1.2.1 p.1.2.2
      set h4 := gOutH bh p.1.1 p.1.2.1 p.1.2.2 - gOutB p.1.1 p.1.2.1 p.1.2.2
      set h3 := gOutB p.1.1 p.1.2.1 p.1.2.2 - gOutA p.1.1 p.1.2.1 p.1.2.2
      set h2 := gOutA p.1.1 p.1.2.1 p.1.2.2 - gA p.1.1 p.1.2.1 p.1.2.2
      have e : gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - gA p.1.1 p.1.2.1 p.1.2.2 =
          ((h2 + h3) + h4) + s := by
        simp only [s, h4, h3, h2]; ring
      rw [e]
      have s1 := sq_add_le_w hη₃ h2 h3
      have s2 := sq_add_le_w hη₄ (h2 + h3) h4
      have s3 := sq_add_le_w hη₅ ((h2 + h3) + h4) s
      have p4 : (0 : ℝ) ≤ 1 + η₄ := by positivity
      have p5 : (0 : ℝ) ≤ 1 + η₅ := by positivity
      have t2 : (1 + η₄) * (h2 + h3) ^ 2 ≤
          (1 + η₄) * ((1 + η₃) * h2 ^ 2 + (1 + 1 / η₃) * h3 ^ 2) :=
        mul_le_mul_of_nonneg_left s1 p4
      have t3 : (1 + η₅) * ((h2 + h3) + h4) ^ 2 ≤
          (1 + η₅) * ((1 + η₄) * ((1 + η₃) * h2 ^ 2 + (1 + 1 / η₃) * h3 ^ 2) +
            (1 + 1 / η₄) * h4 ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) p5
      rw [hc2, hc3, hc4, hc5]
      linarith
    · rw [indicator_of_notMem hp]
      positivity
  -- integrate
  have m2 : Measurable (fun p : Joint k n => ENNReal.ofReal (dOut2 (Gwin n) Δmax ΔXmax p.1)) :=
    ENNReal.measurable_ofReal.comp ((measurable_dOut2 hG hn1 Δmax ΔXmax).comp measurable_fst)
  have m3 : Measurable (fun p : Joint k n =>
      ENNReal.ofReal (dOut3 (Gwin n) Δmax ΔXmax εD εQ Dmax p.1)) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_dOut3 hG hn1 Δmax ΔXmax εD εQ Dmax).comp measurable_fst)
  have m4 : Measurable (fun p : Joint k n =>
      ENNReal.ofReal (dOut4 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 p.1)) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_dOut4 hG hn1 Δmax ΔXmax εD εQ Dmax hbh D4).comp measurable_fst)
  have fstL : ∀ f : Trip n → ℝ≥0∞, Measurable f →
      ∫⁻ p : Joint k n, f p.1 ∂jointP k n = ∫⁻ t, f t ∂mlpTriple 2 n := by
    intro f hf
    unfold jointP
    have h := lintegral_prod (μ := mlpTriple 2 n) (ν := gamK k n)
      (fun p : Trip n × (Fin k → Fin n → ℝ) => f p.1) (hf.comp measurable_fst).aemeasurable
    rw [h]
    simp
  have i2 : ∫⁻ p : Joint k n, ENNReal.ofReal (dOut2 (Gwin n) Δmax ΔXmax p.1) ∂jointP k n ≤
      ENNReal.ofReal (2 / (n : ℝ) *
        EA2 (6662 / 10000) Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb) := by
    rw [fstL (fun t => ENNReal.ofReal (dOut2 (Gwin n) Δmax ΔXmax t))
      (ENNReal.measurable_ofReal.comp (measurable_dOut2 hG hn1 Δmax ΔXmax))]
    exact hA
  have i3 : ∫⁻ p : Joint k n, ENNReal.ofReal (dOut3 (Gwin n) Δmax ΔXmax εD εQ Dmax p.1)
      ∂jointP k n ≤ ENNReal.ofReal (2 / (n : ℝ) * (2 / (1 - yhi)) * xiB n εD π₀ ζ₃ dQb) := by
    rw [fstL (fun t => ENNReal.ofReal (dOut3 (Gwin n) Δmax ΔXmax εD εQ Dmax t))
      (ENNReal.measurable_ofReal.comp (measurable_dOut3 hG hn1 Δmax ΔXmax εD εQ Dmax))]
    exact hB
  have i4 : ∫⁻ p : Joint k n, ENNReal.ofReal (dOut4 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 p.1)
      ∂jointP k n ≤ ENNReal.ofReal (2 / (n : ℝ) * (2 / (1 - y4)) * ξ) := by
    rw [fstL (fun t => ENNReal.ofReal (dOut4 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 t))
      (ENNReal.measurable_ofReal.comp (measurable_dOut4 hG hn1 Δmax ΔXmax εD εQ Dmax hbh D4))]
    exact hH
  have i5 : ∫⁻ p : Joint k n, ENNReal.ofReal (SS p) ∂jointP k n ≤
      ENNReal.ofReal (4 / (n : ℝ) / k) := hS
  have hEA0 : 0 ≤ EA2 (6662 / 10000) Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb := by
    have hw := hP.hw
    have hg := hP.hg
    have := hP.hΔmax
    have := hP.hΔXmax
    have := hP.hr₁
    have hv : (0 : ℝ) ≤ 1 - 6662 / 10000 + Δmax := by linarith
    unfold EA2 Part149.kK2 Part149.kX2 Part149.kD2
    positivity
  have hxi0 : 0 ≤ xiB n εD π₀ ζ₃ dQb := by
    have h1 := hP3.hπ0
    have h2 : 0 < 1 - π₀ := by linarith [hP3.hπ1]
    have h3 := Kq_nonneg
    unfold xiB cQ3 cD3
    positivity
  calc ∫⁻ p, ENNReal.ofReal ((TXJ k X).indicator
        (fun p => (gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - gA p.1.1 p.1.2.1 p.1.2.2) ^ 2) p)
        ∂jointP k n
      ≤ ∫⁻ p : Joint k n, (ENNReal.ofReal c2 * ENNReal.ofReal (dOut2 (Gwin n) Δmax ΔXmax p.1) +
          (ENNReal.ofReal c3 * ENNReal.ofReal (dOut3 (Gwin n) Δmax ΔXmax εD εQ Dmax p.1) +
          (ENNReal.ofReal c4 *
              ENNReal.ofReal (dOut4 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 p.1) +
            ENNReal.ofReal c5 * ENNReal.ofReal (SS p)))) ∂jointP k n := by
        refine lintegral_mono fun p => ?_
        have n2 := dOut2_nonneg (Gwin n) Δmax ΔXmax p.1
        have n3 := dOut3_nonneg (Gwin n) Δmax ΔXmax εD εQ Dmax p.1
        have n4 := dOut4_nonneg (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 p.1
        have n5 := hSS0 p
        rw [← ENNReal.ofReal_mul hc20, ← ENNReal.ofReal_mul hc30, ← ENNReal.ofReal_mul hc40,
          ← ENNReal.ofReal_mul hc50, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ((hdom p).trans (le_of_eq ?_))
        ring
    _ = ENNReal.ofReal c2 * ∫⁻ p : Joint k n,
            ENNReal.ofReal (dOut2 (Gwin n) Δmax ΔXmax p.1) ∂jointP k n +
          (ENNReal.ofReal c3 * ∫⁻ p : Joint k n,
              ENNReal.ofReal (dOut3 (Gwin n) Δmax ΔXmax εD εQ Dmax p.1) ∂jointP k n +
          (ENNReal.ofReal c4 * ∫⁻ p : Joint k n,
              ENNReal.ofReal (dOut4 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 p.1) ∂jointP k n +
            ENNReal.ofReal c5 * ∫⁻ p : Joint k n, ENNReal.ofReal (SS p) ∂jointP k n)) := by
        rw [lintegral_add_left (m2.const_mul _), lintegral_add_left (m3.const_mul _),
          lintegral_add_left (m4.const_mul _), lintegral_const_mul _ m2,
          lintegral_const_mul _ m3, lintegral_const_mul _ m4,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal c2 * ENNReal.ofReal (2 / (n : ℝ) *
            EA2 (6662 / 10000) Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb) +
          (ENNReal.ofReal c3 *
              ENNReal.ofReal (2 / (n : ℝ) * (2 / (1 - yhi)) * xiB n εD π₀ ζ₃ dQb) +
          (ENNReal.ofReal c4 * ENNReal.ofReal (2 / (n : ℝ) * (2 / (1 - y4)) * ξ) +
            ENNReal.ofReal c5 * ENNReal.ofReal (4 / (n : ℝ) / k))) :=
        add_le_add (mul_le_mul' le_rfl i2) (add_le_add (mul_le_mul' le_rfl i3)
          (add_le_add (mul_le_mul' le_rfl i4) (mul_le_mul' le_rfl i5)))
    _ = _ := by
        rw [← ENNReal.ofReal_mul hc20, ← ENNReal.ofReal_mul hc30, ← ENNReal.ofReal_mul hc40,
          ← ENNReal.ofReal_mul hc50, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        unfold IA
        rw [hc2, hc3, hc4, hc5]
        ring

end BstLean.Part151
