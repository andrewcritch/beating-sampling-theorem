import BstLean.Part149Asm
import BstLean.Part149Pt2
import BstLean.Part149Mean2

/-!
# Part 149: the error of the stage of the Agent network, second route, integrated

Do not use `sorry`, `native_decide` or `axiom`.

Role: `delegations/statements/p149-spec.md`, items 3 and 4 with the rate `1/n`. The program and
its output `gOutA` are those of `Part149Asm`; only the proof changes (`Part149Stage2`,
`Part149Pt2`, `Part149Mean2`).

* `eX W θ`: the fluctuation of `X(γ) = ⟨a₂(x(γ)), b̄⟩` (three-point quantity).
* `goodX2`, `goodT2`: the good event (thresholds for the kernel error and for `eX`).
* `W_mean`: the mean of a kernel error over `W` on the good hidden event of `W`.
* `EA2`: the constant; `errA2_lint`: `E[1_good·(gOutA − gA)²] ≤ (2/n)·EA2`;
  `badT2_prob`: the probability of the bad event.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss hbar)
open BstLean.Part140 BstLean.Part141 BstLean.Part145

variable {n : ℕ}

/-- The fluctuation of `X(γ) = ⟨a₂(x(γ)), b̄⟩` at the stand-in inputs of `W`. -/
noncomputable def eX (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)) : ℝ :=
  errXc (cenA W) (tauWA W) θ

lemma eX_nonneg (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)) : 0 ≤ eX W θ :=
  integral_nonneg fun _ => sq_nonneg _

lemma measurable_eX :
    Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) => eX x.1 x.2) := by
  have t2 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) => cenA x.1) :=
    measurable_cenA.comp measurable_fst
  have t3 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) => tauWA x.1) :=
    measurable_tauWA.comp measurable_fst
  have t4 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) =>
      ((cenA x.1, tauWA x.1), x.2)) := (t2.prodMk t3).prodMk measurable_snd
  have t5 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) =>
      errXc (cenA x.1) (tauWA x.1) x.2) := by
    have h := (measurable_errXc (n := n) (m := mA n)).comp t4
    simp only [Function.comp_def] at h
    exact h
  exact t5

/-- The good event of `(W, A₁, A₂)`, second route. -/
def goodX2 (G : Set (HidParam (2 * n) (mW n))) (Δmax ΔXmax : ℝ) :
    Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n)) :=
  {x | x.1 ∈ goodWAG G ∧ eK x.1 x.2 ≤ ((mA n : ℝ) / n * Δmax) ^ 2 ∧
    eX x.1 x.2 ≤ ((mA n : ℝ) / n * ΔXmax) ^ 2}

/-- The good event as an event of `(W, A, F)`. -/
def goodT2 (G : Set (HidParam (2 * n) (mW n))) (Δmax ΔXmax : ℝ) :
    Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :=
  {t | (t.1, thA t.2.1) ∈ goodX2 G Δmax ΔXmax}

/-- `1_good·(gOutA − gA)²`, second route. -/
noncomputable def dOut2 (G : Set (HidParam (2 * n) (mW n))) (Δmax ΔXmax : ℝ)
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) : ℝ :=
  (goodT2 G Δmax ΔXmax).indicator
    (fun t => (gOutA t.1 t.2.1 t.2.2 - gA t.1 t.2.1 t.2.2) ^ 2) t

lemma goodX2_meas {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤ n)
    (Δmax ΔXmax : ℝ) : MeasurableSet (goodX2 G Δmax ΔXmax) := by
  have h1 : MeasurableSet {x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) |
      x.1 ∈ goodWAG G} := measurable_fst (goodWAG0_meas hG hn)
  have h2 : MeasurableSet {x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) |
      eK x.1 x.2 ≤ ((mA n : ℝ) / n * Δmax) ^ 2} := measurableSet_le measurable_eK measurable_const
  have h3 : MeasurableSet {x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) |
      eX x.1 x.2 ≤ ((mA n : ℝ) / n * ΔXmax) ^ 2} := measurableSet_le measurable_eX measurable_const
  exact h1.inter (h2.inter h3)

lemma goodT2_meas {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤ n)
    (Δmax ΔXmax : ℝ) : MeasurableSet (goodT2 G Δmax ΔXmax) :=
  measurable_WX (goodX2_meas hG hn Δmax ΔXmax)

lemma measurable_dOut2 {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤ n)
    (Δmax ΔXmax : ℝ) : Measurable (dOut2 G Δmax ΔXmax) :=
  ((measurable_gOutA.sub measurable_gA).pow_const 2).indicator (goodT2_meas hG hn Δmax ΔXmax)

lemma dOut2_nonneg (G : Set (HidParam (2 * n) (mW n))) (Δmax ΔXmax : ℝ)
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :
    0 ≤ dOut2 G Δmax ΔXmax t := Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

/-- The window hypothesis of the `W` stage, second route (the window of `q` is fixed). -/
def WinOK2 (n : ℕ) (G : Set (HidParam (2 * n) (mW n))) (alo ahi : ℝ) : Prop :=
  ∀ θ ∈ goodAG G, 0 < betaSq θ ∧ 0 < tauA n θ ∧ 462 / 1000 ≤ qTh θ ∧ qTh θ ≤ 527 / 1000 ∧
    alo ≤ kappa (kappa (qTh θ)) ∧ kappa (kappa (qTh θ)) ≤ ahi

/-! ## The mean of a kernel error over `W` -/

/-- **The mean over `W` of a quantity that depends on `W` through `(M₁, M₂)` and the centre
`M₃ b̃`**, on the good hidden event of `W`: the centre is a Gaussian vector `β·ξ`. -/
lemma W_mean (hn : 1 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {E : MlpParam (2 * n) (mW n) n → HidParam n (mA n) → ℝ}
    (mE : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) => E x.1 x.2))
    {Φ : HidParam (2 * n) (mW n) → (Fin n → ℝ) → HidParam n (mA n) → ℝ}
    (hΦ : ∀ (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)),
      E W θ = Φ (W.1, W.2.1) (W.2.2.mulVec (bA n (W.1, W.2.1))) θ)
    (mΦ : ∀ x, Measurable (fun q : (Fin n → ℝ) × HidParam n (mA n) => Φ x q.1 q.2))
    {Bd : ℝ} (hβ : ∀ x ∈ goodAG G, 0 < betaSq x)
    (hB : ∀ x ∈ goodAG G, ∀ β : ℝ, 0 < β → β ^ 2 = betaSq x →
      ∫⁻ ξ, (∫⁻ θ, ENNReal.ofReal (Φ x (β • ξ) θ) ∂hidGauss n (mA n)) ∂stdGauss (Fin n) ≤
        ENNReal.ofReal Bd) :
    ∫⁻ W, (goodWAG G).indicator
        (fun W => ∫⁻ θ, ENNReal.ofReal (E W θ) ∂hidGauss n (mA n)) W
        ∂mlpGauss (2 * n) (mW n) n ≤ ENNReal.ofReal Bd := by
  have mIK : Measurable (fun W : MlpParam (2 * n) (mW n) n =>
      ∫⁻ θ, ENNReal.ofReal (E W θ) ∂hidGauss n (mA n)) :=
    (ENNReal.measurable_ofReal.comp mE).lintegral_prod_right'
  have mg : Measurable (fun W : MlpParam (2 * n) (mW n) n => (goodWAG G).indicator
      (fun W => ∫⁻ θ, ENNReal.ofReal (E W θ) ∂hidGauss n (mA n)) W) :=
    mIK.indicator (goodWAG0_meas hG hn)
  have e0 : mlpGauss (2 * n) (mW n) n = (gaussMat (mW n) (2 * n) (2 / ((2 * n : ℕ) : ℝ))).prod
      ((gaussMat (mW n) (mW n) (2 / (mW n : ℝ))).prod (gaussMat n (mW n) (2 / (mW n : ℝ)))) := rfl
  rw [e0, lint_assoc3 _ _ _ mg]
  have key : ∀ x : HidParam (2 * n) (mW n),
      ∫⁻ M₃, (goodWAG G).indicator
        (fun W => ∫⁻ θ, ENNReal.ofReal (E W θ) ∂hidGauss n (mA n)) (x.1, x.2, M₃)
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)) ≤ ENNReal.ofReal Bd := by
    intro x
    by_cases hx : x ∈ goodAG G
    · have hmem : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((x.1, x.2, M₃) : MlpParam (2 * n) (mW n) n) ∈ goodWAG G := fun M₃ => hx
      simp only [Set.indicator_of_mem (hmem _)]
      set Ψ : (Fin n → ℝ) → ℝ≥0∞ := fun c =>
        ∫⁻ θ, ENNReal.ofReal (Φ x c θ) ∂hidGauss n (mA n) with hΨ
      have mΨ : Measurable Ψ := (ENNReal.measurable_ofReal.comp (mΦ x)).lintegral_prod_right'
      have e1 : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ∫⁻ θ, ENNReal.ofReal (E ((x.1, x.2, M₃) : MlpParam (2 * n) (mW n) n) θ)
            ∂hidGauss n (mA n) = Ψ (M₃.mulVec (bA n x)) := by
        intro M₃
        simp only [hΨ]
        refine lintegral_congr fun θ => ?_
        rw [hΦ]
      simp_rw [e1]
      set β : ℝ := Real.sqrt (2 / (mW n : ℝ)) * Real.sqrt (normSq (bA n x)) with hβd
      have hβ2 : β ^ 2 = betaSq x := by
        rw [hβd, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (normSq_nonneg _)]
        rfl
      have hβ0 : 0 < β := by
        have h0 : 0 ≤ β := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        have hb := hβ x hx
        rcases h0.lt_or_eq with h | h
        · exact h
        · rw [← h] at hβ2
          rw [← hβ2] at hb
          norm_num at hb
      have e2 : ∫⁻ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ, Ψ (M₃.mulVec (bA n x))
          ∂gaussMat n (mW n) (2 / (mW n : ℝ)) = ∫⁻ ξ, Ψ (β • ξ) ∂stdGauss (Fin n) := by
        rw [← lintegral_map mΨ (measurable_mulVec_right (bA n x)), gaussMat_mulVec,
          lintegral_map mΨ (measurable_const_smul _)]
      rw [e2]
      exact hB x hx β hβ0 hβ2
    · have hmem : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((x.1, x.2, M₃) : MlpParam (2 * n) (mW n) n) ∉ goodWAG G := fun M₃ => hx
      simp only [Set.indicator_of_notMem (hmem _)]
      simp
  calc ∫⁻ x, ∫⁻ M₃, (goodWAG G).indicator
        (fun W => ∫⁻ θ, ENNReal.ofReal (E W θ) ∂hidGauss n (mA n)) (x.1, x.2, M₃)
        ∂gaussMat n (mW n) (2 / (mW n : ℝ))
        ∂((gaussMat (mW n) (2 * n) (2 / ((2 * n : ℕ) : ℝ))).prod
          (gaussMat (mW n) (mW n) (2 / (mW n : ℝ))))
      ≤ ∫⁻ _x, ENNReal.ofReal Bd
        ∂((gaussMat (mW n) (2 * n) (2 / ((2 * n : ℕ) : ℝ))).prod
          (gaussMat (mW n) (mW n) (2 / (mW n : ℝ)))) := lintegral_mono key
    _ = _ := by simp

/-- The mean of the kernel error, second route. -/
lemma eK_mean2 (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {alo ahi : ℝ} (hwin : WinOK2 n G alo ahi) {ΔKb : ℝ}
    (hΔK : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dK2 n (mA n) q ≤ ΔKb)
    (hK0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dK2 n (mA n) q) :
    ∫⁻ W, (goodWAG G).indicator
        (fun W => ∫⁻ θ, ENNReal.ofReal (eK W θ) ∂hidGauss n (mA n)) W
        ∂mlpGauss (2 * n) (mW n) n ≤ ENNReal.ofReal (((mA n : ℝ) / n * ΔKb) ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hd : (0 : ℝ) ≤ (mA n : ℝ) / n := by positivity
  refine W_mean hn1 hG measurable_eK
    (Φ := fun x c θ => errKc ((mA n : ℝ) / n * kappa (kappa (qTh x))) c (tauA n x) θ)
    (fun W θ => rfl) (fun x => ?_) (fun x hx => (hwin x hx).1) (fun x hx β hβ0 hβ2 => ?_)
  · have h0 : Measurable (fun q : (Fin n → ℝ) × HidParam n (mA n) =>
        (((mA n : ℝ) / n * kappa (kappa (qTh x)), q.1, tauA n x), q.2)) :=
      (measurable_const.prodMk (measurable_fst.prodMk measurable_const)).prodMk measurable_snd
    have h2 := (measurable_errKc (n := n) (m := mA n)).comp h0
    simp only [Function.comp_def] at h2
    exact h2
  · obtain ⟨_, hτ, hq1, hq2, _, _⟩ := hwin x hx
    have hq1' : 462 / 1000 ≤ β ^ 2 / (β ^ 2 + tauA n x ^ 2) := by rw [hβ2]; exact hq1
    have hq2' : β ^ 2 / (β ^ 2 + tauA n x ^ 2) ≤ 527 / 1000 := by rw [hβ2]; exact hq2
    have hmean := errK_mean2 (m := mA n) hn1 hmA hβ0 hτ hq1' hq2'
    rw [hβ2] at hmean
    refine hmean.trans (ENNReal.ofReal_le_ofReal ?_)
    exact pow_le_pow_left₀ (mul_nonneg hd (hK0 _ hq1 hq2))
      (mul_le_mul_of_nonneg_left (hΔK _ hq1 hq2) hd) 2

/-- The mean of the fluctuation of `X`. -/
lemma eX_mean2 (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {alo ahi : ℝ} (hwin : WinOK2 n G alo ahi) {ΔXb : ℝ}
    (hΔX : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dX2 n (mA n) q ≤ ΔXb)
    (hX0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dX2 n (mA n) q) :
    ∫⁻ W, (goodWAG G).indicator
        (fun W => ∫⁻ θ, ENNReal.ofReal (eX W θ) ∂hidGauss n (mA n)) W
        ∂mlpGauss (2 * n) (mW n) n ≤ ENNReal.ofReal (((mA n : ℝ) / n * ΔXb) ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hd : (0 : ℝ) ≤ (mA n : ℝ) / n := by positivity
  refine W_mean hn1 hG measurable_eX
    (Φ := fun x c θ => errXc c (tauA n x) θ)
    (fun W θ => rfl) (fun x => ?_) (fun x hx => (hwin x hx).1) (fun x hx β hβ0 hβ2 => ?_)
  · have h0 : Measurable (fun q : (Fin n → ℝ) × HidParam n (mA n) =>
        ((q.1, tauA n x), q.2)) :=
      (measurable_fst.prodMk measurable_const).prodMk measurable_snd
    have h2 := (measurable_errXc (n := n) (m := mA n)).comp h0
    simp only [Function.comp_def] at h2
    exact h2
  · obtain ⟨_, hτ, hq1, hq2, _, _⟩ := hwin x hx
    have hq1' : 462 / 1000 ≤ β ^ 2 / (β ^ 2 + tauA n x ^ 2) := by rw [hβ2]; exact hq1
    have hq2' : β ^ 2 / (β ^ 2 + tauA n x ^ 2) ≤ 527 / 1000 := by rw [hβ2]; exact hq2
    have hmean := errX_mean2 (m := mA n) hn1 hmA hβ0 hτ hq1' hq2'
    rw [hβ2] at hmean
    refine hmean.trans (ENNReal.ofReal_le_ofReal ?_)
    exact pow_le_pow_left₀ (mul_nonneg hd (hX0 _ hq1 hq2))
      (mul_le_mul_of_nonneg_left (hΔX _ hq1 hq2) hd) 2

/-! ## The constants -/

/-- The hypotheses on the parameters, second route. -/
structure POK2 (alo ahi Δmax ΔXmax r₁ r₂ w g : ℝ) : Prop where
  halo1 : alo ≤ 1
  hΔmax : 0 < Δmax
  hΔXmax : 0 < ΔXmax
  hA1 : Δmax < alo
  hA2 : ahi + Δmax < 1
  hr₁ : 0 < r₁
  hr₁' : 1 ≤ r₁ ^ 2 * (alo - Δmax)
  hr₂ : 0 < r₂
  hr₂' : 1 ≤ r₂ ^ 2 * (1 - ahi - Δmax)
  hw : 0 < w
  hg : 0 < g
  hgw : (g + w) ^ 2 ≤ 1 - ahi - Δmax

/-- The coefficient of `Δ²` (kernel error). -/
noncomputable def kK2 (alo Δmax w η ζ₂ : ℝ) : ℝ :=
  (1 + 1 / η) * (2 * (1 - alo + Δmax)) * ((1 + ζ₂) / w ^ 4)

/-- The coefficient of `ΔX²` (fluctuation of `X`). -/
noncomputable def kX2 (alo Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ : ℝ) : ℝ :=
  (1 + η) * 2 * (r₁ ^ 2 + (1 + ζ) * (r₁ + 2 * r₂) ^ 2) +
    (1 + 1 / η) * (2 * (1 - alo + Δmax)) *
      ((r₂ ^ 2 + 3 / g ^ 2) * ((1 + ζ) * (r₁ + 2 * r₂) ^ 2) +
        (1 + 1 / ζ₂) * (r₁ ^ 2 * ΔXmax) ^ 2 / w ^ 4)

/-- The coefficient of `δ²` (diagonal error). -/
noncomputable def kD2 (alo Δmax r₂ g η ζ : ℝ) : ℝ :=
  ((1 + η) * 2 + (1 + 1 / η) * (2 * (1 - alo + Δmax)) * (r₂ ^ 2 + 3 / g ^ 2)) *
    ((1 + 1 / ζ) * r₂ ^ 2)

/-- The constant of the mean squared error of the stage of `A`, second route, in units `2/n`. -/
noncomputable def EA2 (alo Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb : ℝ) : ℝ :=
  kK2 alo Δmax w η ζ₂ * ΔKb ^ 2 + kX2 alo Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ * ΔXb ^ 2 +
    kD2 alo Δmax r₂ g η ζ * δb ^ 2

/-- The bound of `stagePt2` is at most a quadratic form in `(Δ, ΔX, δ)`. -/
lemma stage_lin2 {alo Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ Δ ΔX δ : ℝ} (hv : 0 ≤ 1 - alo + Δmax)
    (hη : 0 < η) (hζ : 0 < ζ) (hζ₂ : 0 < ζ₂) (hw : 0 < w) (hg : 0 < g)
    (hΔ0 : 0 ≤ Δ) (hΔX0 : 0 ≤ ΔX) (hΔX : ΔX ≤ ΔXmax) (hr₁ : 0 < r₁) :
    (1 + η) * (2 * (r₁ ^ 2 * ΔX ^ 2 + (r₁ * ΔX + r₂ * (δ + 2 * ΔX)) ^ 2)) +
        (1 + 1 / η) * (2 * (1 - alo + Δmax) *
          (r₂ ^ 2 * (r₁ * ΔX + r₂ * (δ + 2 * ΔX)) ^ 2 +
            (Δ + r₁ ^ 2 * ΔX ^ 2) ^ 2 / w ^ 4 +
            3 * (r₁ * ΔX + r₂ * (δ + 2 * ΔX)) ^ 2 / g ^ 2)) ≤
      kK2 alo Δmax w η ζ₂ * Δ ^ 2 + kX2 alo Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ * ΔX ^ 2 +
        kD2 alo Δmax r₂ g η ζ * δ ^ 2 := by
  unfold kK2 kX2 kD2
  set A0 : ℝ := (1 + η) * 2 with hA0
  set B0 : ℝ := (1 + 1 / η) * (2 * (1 - alo + Δmax)) with hB0
  have hA00 : 0 ≤ A0 := by rw [hA0]; positivity
  have hB00 : 0 ≤ B0 := by rw [hB0]; positivity
  set Sb : ℝ := (r₁ * ΔX + r₂ * (δ + 2 * ΔX)) ^ 2 with hSb
  set Sq : ℝ := (1 + ζ) * (r₁ + 2 * r₂) ^ 2 * ΔX ^ 2 + (1 + 1 / ζ) * r₂ ^ 2 * δ ^ 2 with hSq
  have h2 : Sb ≤ Sq := by
    have h3 := BstLean.Part133.L2le.sq_add_le (x := (r₁ + 2 * r₂) * ΔX) (y := r₂ * δ)
      (a := 1) (b := ζ) one_pos hζ
    have e3 : (r₁ * ΔX + r₂ * (δ + 2 * ΔX)) = (r₁ + 2 * r₂) * ΔX + r₂ * δ := by ring
    rw [hSb, hSq, e3]
    calc ((r₁ + 2 * r₂) * ΔX + r₂ * δ) ^ 2
        ≤ (1 + ζ / 1) * ((r₁ + 2 * r₂) * ΔX) ^ 2 + (1 + 1 / ζ) * (r₂ * δ) ^ 2 := h3
      _ = _ := by ring
  have hSb0 : 0 ≤ Sb := by rw [hSb]; positivity
  have h4 : (Δ + r₁ ^ 2 * ΔX ^ 2) ^ 2 ≤
      (1 + ζ₂) * Δ ^ 2 + (1 + 1 / ζ₂) * (r₁ ^ 2 * ΔXmax) ^ 2 * ΔX ^ 2 := by
    have h5 : r₁ ^ 2 * ΔX ^ 2 ≤ (r₁ ^ 2 * ΔXmax) * ΔX := by
      have : ΔX ^ 2 ≤ ΔXmax * ΔX := by nlinarith
      nlinarith [sq_nonneg r₁]
    have h6 : (Δ + r₁ ^ 2 * ΔX ^ 2) ^ 2 ≤ (Δ + (r₁ ^ 2 * ΔXmax) * ΔX) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h7 := BstLean.Part133.L2le.sq_add_le (x := Δ) (y := (r₁ ^ 2 * ΔXmax) * ΔX)
      (a := 1) (b := ζ₂) one_pos hζ₂
    refine h6.trans (h7.trans (le_of_eq ?_))
    ring
  have hw4 : 0 < w ^ 4 := by positivity
  have hg2 : 0 < g ^ 2 := by positivity
  have t1 : A0 * (r₁ ^ 2 * ΔX ^ 2 + Sb) ≤ A0 * (r₁ ^ 2 * ΔX ^ 2 + Sq) :=
    mul_le_mul_of_nonneg_left (by linarith) hA00
  have t2 : B0 * (r₂ ^ 2 * Sb + (Δ + r₁ ^ 2 * ΔX ^ 2) ^ 2 / w ^ 4 + 3 * Sb / g ^ 2) ≤
      B0 * (r₂ ^ 2 * Sq + ((1 + ζ₂) * Δ ^ 2 + (1 + 1 / ζ₂) * (r₁ ^ 2 * ΔXmax) ^ 2 * ΔX ^ 2) /
        w ^ 4 + 3 * Sq / g ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ hB00
    have a1 : r₂ ^ 2 * Sb ≤ r₂ ^ 2 * Sq := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    have a2 := div_le_div_of_nonneg_right h4 hw4.le
    have a3 : 3 * Sb / g ^ 2 ≤ 3 * Sq / g ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) hg2.le
    linarith
  have eL : (1 + η) * (2 * (r₁ ^ 2 * ΔX ^ 2 + Sb)) +
      (1 + 1 / η) * (2 * (1 - alo + Δmax) *
        (r₂ ^ 2 * Sb + (Δ + r₁ ^ 2 * ΔX ^ 2) ^ 2 / w ^ 4 + 3 * Sb / g ^ 2)) =
      A0 * (r₁ ^ 2 * ΔX ^ 2 + Sb) +
        B0 * (r₂ ^ 2 * Sb + (Δ + r₁ ^ 2 * ΔX ^ 2) ^ 2 / w ^ 4 + 3 * Sb / g ^ 2) := by
    rw [hA0, hB0]; ring
  have eR : B0 * ((1 + ζ₂) / w ^ 4) * Δ ^ 2 +
      (A0 * (r₁ ^ 2 + (1 + ζ) * (r₁ + 2 * r₂) ^ 2) +
        B0 * ((r₂ ^ 2 + 3 / g ^ 2) * ((1 + ζ) * (r₁ + 2 * r₂) ^ 2) +
          (1 + 1 / ζ₂) * (r₁ ^ 2 * ΔXmax) ^ 2 / w ^ 4)) * ΔX ^ 2 +
      (A0 + B0 * (r₂ ^ 2 + 3 / g ^ 2)) * ((1 + 1 / ζ) * r₂ ^ 2) * δ ^ 2 =
      A0 * (r₁ ^ 2 * ΔX ^ 2 + Sq) +
        B0 * (r₂ ^ 2 * Sq + ((1 + ζ₂) * Δ ^ 2 + (1 + 1 / ζ₂) * (r₁ ^ 2 * ΔXmax) ^ 2 * ΔX ^ 2) /
          w ^ 4 + 3 * Sq / g ^ 2) := by
    rw [hSq]
    field_simp
    ring
  rw [eL, eR]
  linarith

/-- The quadratic error bound as a function of the three kernel errors. -/
noncomputable def linB2 (n : ℕ) (k₁ k₂ k₃ : ℝ) (W : MlpParam (2 * n) (mW n) n)
    (θ : HidParam n (mA n)) : ℝ :=
  2 / (n : ℝ) * (k₁ * (eK W θ / ((mA n : ℝ) / n) ^ 2) + k₂ * (eX W θ / ((mA n : ℝ) / n) ^ 2) +
    k₃ * (eD W θ / ((mA n : ℝ) / n) ^ 2))

/-- The stage of `A` at fixed `(W, A₁, A₂)`, integrated over `(A₃, F)`, second route. -/
lemma errA2_key (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))}
    {alo ahi Δmax ΔXmax r₁ r₂ w g : ℝ} (hwin : WinOK2 n G alo ahi)
    (hP : POK2 alo ahi Δmax ΔXmax r₁ r₂ w g) {η ζ ζ₂ : ℝ} (hη : 0 < η) (hζ : 0 < ζ)
    (hζ₂ : 0 < ζ₂) (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)) :
    ∫⁻ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        ENNReal.ofReal (dOut2 G Δmax ΔXmax (W, (θ.1, θ.2, y.1), y.2))
        ∂((gaussMat n (mA n) (2 / (mA n : ℝ))).prod (mlpGauss n (mF n) 1)) ≤
      (goodWAG G).indicator
        (fun _ => ENNReal.ofReal (linB2 n (kK2 alo Δmax w η ζ₂)
          (kX2 alo Δmax ΔXmax r₁ r₂ w g η ζ ζ₂) (kD2 alo Δmax r₂ g η ζ) W θ)) W := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := BstLean.Part132.mF_ge hn; omega
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  have hd0 : (0 : ℝ) < (mA n : ℝ) / n := by positivity
  have hv₀0 : 0 ≤ 1 - alo + Δmax := by
    have := hP.halo1; have := hP.hΔmax
    linarith
  by_cases hx : (W, θ) ∈ goodX2 G Δmax ΔXmax
  · obtain ⟨hW, hK, hX⟩ := hx
    have hx' : (W, θ) ∈ goodX2 G Δmax ΔXmax := ⟨hW, hK, hX⟩
    rw [Set.indicator_of_mem hW]
    have hmem : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        ((W, (θ.1, θ.2, y.1), y.2) : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) ∈ goodT2 G Δmax ΔXmax := fun y => hx'
    have e : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        dOut2 G Δmax ΔXmax (W, (θ.1, θ.2, y.1), y.2) =
          (gT (stdGauss (Fin n)) (hA (cenA W) (tauWA W) θ) y -
            gO (bbar (cenA W) (tauWA W) θ) (tauOut (cenA W) (tauWA W) θ) y) ^ 2 := by
      intro y
      unfold dOut2
      rw [Set.indicator_of_mem (hmem y)]
      simp only []
      rw [gA_eq_gT hn1]
      show (gO (bbar (cenA W) (tauWA W) θ) (tauOut (cenA W) (tauWA W) θ) y -
        gT (stdGauss (Fin n)) (hA (cenA W) (tauWA W) θ) y) ^ 2 = _
      ring
    simp_rw [e]
    obtain ⟨_, _, _, _, hal, hah⟩ := hwin (W.1, W.2.1) hW
    have hK0 := eK_nonneg W θ
    have hD0 := eD_nonneg W θ
    have hX0 := eX_nonneg W θ
    have hΔ0 : 0 ≤ √(eK W θ) / ((mA n : ℝ) / n) := div_nonneg (Real.sqrt_nonneg _) hd0.le
    have hδ0 : 0 ≤ √(eD W θ) / ((mA n : ℝ) / n) := div_nonneg (Real.sqrt_nonneg _) hd0.le
    have hΔX0 : 0 ≤ √(eX W θ) / ((mA n : ℝ) / n) := div_nonneg (Real.sqrt_nonneg _) hd0.le
    have edΔ : (mA n : ℝ) / n * (√(eK W θ) / ((mA n : ℝ) / n)) = √(eK W θ) := by
      field_simp
    have edδ : (mA n : ℝ) / n * (√(eD W θ) / ((mA n : ℝ) / n)) = √(eD W θ) := by
      field_simp
    have edX : (mA n : ℝ) / n * (√(eX W θ) / ((mA n : ℝ) / n)) = √(eX W θ) := by
      field_simp
    have hΔle : √(eK W θ) / ((mA n : ℝ) / n) ≤ Δmax := by
      rw [div_le_iff₀ hd0, mul_comm]
      exact Real.sqrt_le_iff.mpr ⟨mul_nonneg hd0.le hP.hΔmax.le, hK⟩
    have hΔXle : √(eX W θ) / ((mA n : ℝ) / n) ≤ ΔXmax := by
      rw [div_le_iff₀ hd0, mul_comm]
      exact Real.sqrt_le_iff.mpr ⟨mul_nonneg hd0.le hP.hΔXmax.le, hX⟩
    have hK' : errKc ((mA n : ℝ) / n * kappa (kappa (qTh (W.1, W.2.1)))) (cenA W) (tauWA W) θ ≤
        ((mA n : ℝ) / n * (√(eK W θ) / ((mA n : ℝ) / n))) ^ 2 := by
      rw [edΔ, Real.sq_sqrt hK0]
      exact le_rfl
    have hD' : errDc (cenA W) (tauWA W) θ ≤
        ((mA n : ℝ) / n * (√(eD W θ) / ((mA n : ℝ) / n))) ^ 2 := by
      rw [edδ, Real.sq_sqrt hD0]
      exact le_rfl
    have hX' : ∫ γ, (∑ j, hA (cenA W) (tauWA W) θ γ j * bbar (cenA W) (tauWA W) θ j -
        normSq (bbar (cenA W) (tauWA W) θ)) ^ 2 ∂stdGauss (Fin n) ≤
        ((mA n : ℝ) / n * (√(eX W θ) / ((mA n : ℝ) / n))) ^ 2 := by
      rw [edX, Real.sq_sqrt hX0]
      exact le_rfl
    have hpt := stagePt2 (mF := mF n) hn1 hmA hmF (cenA W) (tauWA W) θ hal hah hP.hΔmax.le
      hP.hA1 hP.hA2 hP.hr₁ hP.hr₁' hP.hr₂ hP.hr₂' hP.hw hP.hg hP.hgw hη hΔ0 hΔle hΔX0 hδ0
      hK' hD' hX'
    refine hpt.trans (ENNReal.ofReal_le_ofReal ?_)
    unfold linB2
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hlin := stage_lin2 (alo := alo) (Δmax := Δmax) (ΔXmax := ΔXmax) (r₁ := r₁) (r₂ := r₂)
      (w := w) (g := g) (Δ := √(eK W θ) / ((mA n : ℝ) / n))
      (ΔX := √(eX W θ) / ((mA n : ℝ) / n)) (δ := √(eD W θ) / ((mA n : ℝ) / n)) hv₀0 hη hζ hζ₂
      hP.hw hP.hg hΔ0 hΔX0 hΔXle hP.hr₁
    have e1 : eK W θ / ((mA n : ℝ) / n) ^ 2 = (√(eK W θ) / ((mA n : ℝ) / n)) ^ 2 := by
      rw [div_pow (√(eK W θ)), Real.sq_sqrt hK0]
    have e2 : eD W θ / ((mA n : ℝ) / n) ^ 2 = (√(eD W θ) / ((mA n : ℝ) / n)) ^ 2 := by
      rw [div_pow (√(eD W θ)), Real.sq_sqrt hD0]
    have e3 : eX W θ / ((mA n : ℝ) / n) ^ 2 = (√(eX W θ) / ((mA n : ℝ) / n)) ^ 2 := by
      rw [div_pow (√(eX W θ)), Real.sq_sqrt hX0]
    rw [e1, e2, e3]
    exact hlin
  · have hmem : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        ((W, (θ.1, θ.2, y.1), y.2) : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) ∉ goodT2 G Δmax ΔXmax := fun y => hx
    have e : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        dOut2 G Δmax ΔXmax (W, (θ.1, θ.2, y.1), y.2) = 0 := fun y => by
      unfold dOut2
      rw [Set.indicator_of_notMem (hmem y)]
    simp_rw [e]
    simp

/-- The stage of `A` at fixed `W`, integrated over `(A, F)`, second route. -/
lemma errA2_inner (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {Δmax ΔXmax k₁ k₂ k₃ : ℝ} (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (hk₃ : 0 ≤ k₃)
    (hkey : ∀ (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)),
      ∫⁻ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        ENNReal.ofReal (dOut2 G Δmax ΔXmax (W, (θ.1, θ.2, y.1), y.2))
        ∂((gaussMat n (mA n) (2 / (mA n : ℝ))).prod (mlpGauss n (mF n) 1)) ≤
      (goodWAG G).indicator (fun _ => ENNReal.ofReal (linB2 n k₁ k₂ k₃ W θ)) W)
    {δb : ℝ} (hδb : cF2o (mA n) ≤ δb) (W : MlpParam (2 * n) (mW n) n) :
    ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1, ENNReal.ofReal (dOut2 G Δmax ΔXmax (W, p))
        ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) ≤
      ENNReal.ofReal (2 / (n : ℝ) * (k₁ / ((mA n : ℝ) / n) ^ 2)) * (goodWAG G).indicator
          (fun W => ∫⁻ θ, ENNReal.ofReal (eK W θ) ∂hidGauss n (mA n)) W +
        ENNReal.ofReal (2 / (n : ℝ) * (k₂ / ((mA n : ℝ) / n) ^ 2)) * (goodWAG G).indicator
          (fun W => ∫⁻ θ, ENNReal.ofReal (eX W θ) ∂hidGauss n (mA n)) W +
        ENNReal.ofReal (2 / (n : ℝ) * (k₃ / ((mA n : ℝ) / n) ^ 2)) *
          ENNReal.ofReal (((mA n : ℝ) / n * δb) ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  have hd0 : (0 : ℝ) < (mA n : ℝ) / n := by positivity
  have mOD : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ENNReal.ofReal (dOut2 G Δmax ΔXmax t)) :=
    ENNReal.measurable_ofReal.comp (measurable_dOut2 hG hn1 Δmax ΔXmax)
  have mgW : Measurable (fun p : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      ENNReal.ofReal (dOut2 G Δmax ΔXmax (W, p))) := mOD.comp measurable_prodMk_left
  have h4 := lint_assoc4 (gaussMat (mA n) n (2 / (n : ℝ)))
    (gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) (gaussMat n (mA n) (2 / (mA n : ℝ)))
    (mlpGauss n (mF n) 1) mgW
  have e1 : (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) =
      ((gaussMat (mA n) n (2 / (n : ℝ))).prod ((gaussMat (mA n) (mA n) (2 / (mA n : ℝ))).prod
        (gaussMat n (mA n) (2 / (mA n : ℝ))))).prod (mlpGauss n (mF n) 1) := rfl
  rw [e1, h4]
  have e2 : (gaussMat (mA n) n (2 / (n : ℝ))).prod (gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) =
      hidGauss n (mA n) := rfl
  rw [e2]
  refine (lintegral_mono fun θ => hkey W θ).trans ?_
  by_cases hW : W ∈ goodWAG G
  · simp only [Set.indicator_of_mem hW]
    have mK0 : Measurable (fun θ : HidParam n (mA n) => eK W θ) := by
      have h := (measurable_eK (n := n)).comp (measurable_prodMk_left (x := W))
      simp only [Function.comp_def] at h
      exact h
    have mD0 : Measurable (fun θ : HidParam n (mA n) => eD W θ) := by
      have h := (measurable_eD (n := n)).comp (measurable_prodMk_left (x := W))
      simp only [Function.comp_def] at h
      exact h
    have mX0 : Measurable (fun θ : HidParam n (mA n) => eX W θ) := by
      have h := (measurable_eX (n := n)).comp (measurable_prodMk_left (x := W))
      simp only [Function.comp_def] at h
      exact h
    have mK : Measurable (fun θ : HidParam n (mA n) => ENNReal.ofReal (eK W θ)) :=
      ENNReal.measurable_ofReal.comp mK0
    have mDD : Measurable (fun θ : HidParam n (mA n) => ENNReal.ofReal (eD W θ)) :=
      ENNReal.measurable_ofReal.comp mD0
    have mXX : Measurable (fun θ : HidParam n (mA n) => ENNReal.ofReal (eX W θ)) :=
      ENNReal.measurable_ofReal.comp mX0
    have e3 : ∀ θ : HidParam n (mA n), ENNReal.ofReal (linB2 n k₁ k₂ k₃ W θ) =
        ENNReal.ofReal (2 / (n : ℝ) * (k₁ / ((mA n : ℝ) / n) ^ 2)) * ENNReal.ofReal (eK W θ) +
          ENNReal.ofReal (2 / (n : ℝ) * (k₂ / ((mA n : ℝ) / n) ^ 2)) * ENNReal.ofReal (eX W θ) +
          ENNReal.ofReal (2 / (n : ℝ) * (k₃ / ((mA n : ℝ) / n) ^ 2)) *
            ENNReal.ofReal (eD W θ) := by
      intro θ
      have := eK_nonneg W θ
      have := eD_nonneg W θ
      have := eX_nonneg W θ
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      unfold linB2
      ring
    rw [lintegral_congr e3, lintegral_add_right _ (mDD.const_mul _),
      lintegral_add_right _ (mXX.const_mul _),
      lintegral_const_mul _ mK, lintegral_const_mul _ mDD, lintegral_const_mul _ mXX]
    exact add_le_add le_rfl (mul_le_mul' le_rfl (eD_le hn1 hδb W))
  · simp only [Set.indicator_of_notMem hW]
    simp

/-- **The mean squared error of the stage of `A` on the good event, second route**:
`E_{W, A, F}[1_good·(gOutA − gA)²] ≤ (2/n)·EA2`. -/
theorem errA2_lint (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {alo ahi Δmax ΔXmax r₁ r₂ w g : ℝ} (hwin : WinOK2 n G alo ahi)
    (hP : POK2 alo ahi Δmax ΔXmax r₁ r₂ w g) {η ζ ζ₂ : ℝ} (hη : 0 < η) (hζ : 0 < ζ)
    (hζ₂ : 0 < ζ₂) {ΔKb ΔXb δb : ℝ}
    (hΔK : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dK2 n (mA n) q ≤ ΔKb)
    (hK0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dK2 n (mA n) q)
    (hΔX : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dX2 n (mA n) q ≤ ΔXb)
    (hX0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dX2 n (mA n) q)
    (hδb : cF2o (mA n) ≤ δb) :
    ∫⁻ t, ENNReal.ofReal (dOut2 G Δmax ΔXmax t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (2 / (n : ℝ) * EA2 alo Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  have hd0 : (0 : ℝ) < (mA n : ℝ) / n := by positivity
  have hv₀0 : 0 ≤ 1 - alo + Δmax := by
    have := hP.halo1; have := hP.hΔmax
    linarith
  have hw := hP.hw
  have hg := hP.hg
  have hr₁ := hP.hr₁
  have hΔXm := hP.hΔXmax
  have hk₁0 : 0 ≤ kK2 alo Δmax w η ζ₂ := by unfold kK2; positivity
  have hk₂0 : 0 ≤ kX2 alo Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ := by unfold kX2; positivity
  have hk₃0 : 0 ≤ kD2 alo Δmax r₂ g η ζ := by unfold kD2; positivity
  have inner := errA2_inner hn hG hk₁0 hk₂0 hk₃0
    (fun W θ => errA2_key hn hwin hP hη hζ hζ₂ W θ) hδb
  have mOD : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ENNReal.ofReal (dOut2 G Δmax ΔXmax t)) :=
    ENNReal.measurable_ofReal.comp (measurable_dOut2 hG hn1 Δmax ΔXmax)
  have mIK : Measurable (fun W : MlpParam (2 * n) (mW n) n =>
      ∫⁻ θ, ENNReal.ofReal (eK W θ) ∂hidGauss n (mA n)) :=
    (ENNReal.measurable_ofReal.comp measurable_eK).lintegral_prod_right'
  have mIX : Measurable (fun W : MlpParam (2 * n) (mW n) n =>
      ∫⁻ θ, ENNReal.ofReal (eX W θ) ∂hidGauss n (mA n)) :=
    (ENNReal.measurable_ofReal.comp measurable_eX).lintegral_prod_right'
  have mIndK : Measurable (fun W : MlpParam (2 * n) (mW n) n => (goodWAG G).indicator
      (fun W => ∫⁻ θ, ENNReal.ofReal (eK W θ) ∂hidGauss n (mA n)) W) :=
    mIK.indicator (goodWAG0_meas hG hn1)
  have mIndX : Measurable (fun W : MlpParam (2 * n) (mW n) n => (goodWAG G).indicator
      (fun W => ∫⁻ θ, ENNReal.ofReal (eX W θ) ∂hidGauss n (mA n)) W) :=
    mIX.indicator (goodWAG0_meas hG hn1)
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
  rw [e0, lintegral_prod _ mOD.aemeasurable]
  refine (lintegral_mono inner).trans ?_
  rw [lintegral_add_right _ measurable_const, lintegral_add_right _ (mIndX.const_mul _),
    lintegral_const_mul _ mIndK, lintegral_const_mul _ mIndX, lintegral_const, measure_univ,
    mul_one]
  have hKm := eK_mean2 hn hG hwin hΔK hK0
  have hXm := eX_mean2 hn hG hwin hΔX hX0
  refine (add_le_add (add_le_add (mul_le_mul' le_rfl hKm) (mul_le_mul' le_rfl hXm))
    le_rfl).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold EA2
  field_simp

/-! ## The probability of the bad event -/

/-- **The bad event of the stage of `A`, second route.** -/
theorem badT2_prob (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {alo ahi : ℝ} (hwin : WinOK2 n G alo ahi) {Δmax ΔXmax : ℝ}
    (hΔmax : 0 < Δmax) (hΔXmax : 0 < ΔXmax) {ΔKb ΔXb : ℝ} (hΔKb0 : 0 ≤ ΔKb) (hΔXb0 : 0 ≤ ΔXb)
    (hΔK : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dK2 n (mA n) q ≤ ΔKb)
    (hK0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dK2 n (mA n) q)
    (hΔX : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dX2 n (mA n) q ≤ ΔXb)
    (hX0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dX2 n (mA n) q)
    {p : ℝ} (h1 : (hidGauss (2 * n) (mW n)).real Gᶜ ≤ p) :
    (mlpTriple 2 n).real (goodT2 G Δmax ΔXmax)ᶜ ≤
      p + 68000000 / (qA n : ℝ) ^ 2 + ΔKb ^ 2 / Δmax ^ 2 + ΔXb ^ 2 / ΔXmax ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  set d : ℝ := (mA n : ℝ) / n with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have mGW := goodWAG0_meas hG hn1
  set fK : MlpParam (2 * n) (mW n) n × HidParam n (mA n) → ℝ≥0∞ :=
    ({x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) | x.1 ∈ goodWAG G}).indicator
      (fun x => ENNReal.ofReal (eK x.1 x.2)) with hfK
  set fX : MlpParam (2 * n) (mW n) n × HidParam n (mA n) → ℝ≥0∞ :=
    ({x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) | x.1 ∈ goodWAG G}).indicator
      (fun x => ENNReal.ofReal (eX x.1 x.2)) with hfX
  have mfK : Measurable fK :=
    (ENNReal.measurable_ofReal.comp measurable_eK).indicator (measurable_fst mGW)
  have mfX : Measurable fX :=
    (ENNReal.measurable_ofReal.comp measurable_eX).indicator (measurable_fst mGW)
  set μ := mlpTriple 2 n with hμ
  have iK : ∫⁻ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      fK (t.1, thA t.2.1) ∂μ ≤ ENNReal.ofReal ((d * ΔKb) ^ 2) := by
    rw [hμ, lint_WX mfK]
    have e : ∀ W : MlpParam (2 * n) (mW n) n, ∫⁻ θ, fK (W, θ) ∂hidGauss n (mA n) =
        (goodWAG G).indicator
          (fun W => ∫⁻ θ, ENNReal.ofReal (eK W θ) ∂hidGauss n (mA n)) W := by
      intro W
      by_cases hW : W ∈ goodWAG G
      · simp [hfK, Set.indicator_of_mem, hW]
      · simp [hfK, Set.indicator_of_notMem, hW]
    simp_rw [e]
    exact eK_mean2 hn hG hwin hΔK hK0
  have iX : ∫⁻ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      fX (t.1, thA t.2.1) ∂μ ≤ ENNReal.ofReal ((d * ΔXb) ^ 2) := by
    rw [hμ, lint_WX mfX]
    have e : ∀ W : MlpParam (2 * n) (mW n) n, ∫⁻ θ, fX (W, θ) ∂hidGauss n (mA n) =
        (goodWAG G).indicator
          (fun W => ∫⁻ θ, ENNReal.ofReal (eX W θ) ∂hidGauss n (mA n)) W := by
      intro W
      by_cases hW : W ∈ goodWAG G
      · simp [hfX, Set.indicator_of_mem, hW]
      · simp [hfX, Set.indicator_of_notMem, hW]
    simp_rw [e]
    exact eX_mean2 hn hG hwin hΔX hX0
  have markov : ∀ {f : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 →
      ℝ≥0∞} (_ : Measurable f) {x b : ℝ} (_ : 0 < x) (_ : 0 ≤ b)
      (_ : ∫⁻ t, f t ∂μ ≤ ENNReal.ofReal ((d * b) ^ 2)),
      μ.real {t | ENNReal.ofReal ((d * x) ^ 2) < f t} ≤ b ^ 2 / x ^ 2 := by
    intro f mf x b hx hb hint
    have hε : ENNReal.ofReal ((d * x) ^ 2) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have h := meas_ge_le_lintegral_div (μ := μ) mf.aemeasurable hε ENNReal.ofReal_ne_top
    have hsub0 : {t | ENNReal.ofReal ((d * x) ^ 2) < f t} ⊆
        {t | ENNReal.ofReal ((d * x) ^ 2) ≤ f t} := by
      intro t ht
      simp only [Set.mem_ofPred_eq] at ht ⊢
      exact le_of_lt ht
    have h2 : μ {t | ENNReal.ofReal ((d * x) ^ 2) < f t} ≤
        ENNReal.ofReal ((d * b) ^ 2) / ENNReal.ofReal ((d * x) ^ 2) :=
      (measure_mono hsub0).trans (h.trans (ENNReal.div_le_div_right hint _))
    rw [← ENNReal.ofReal_div_of_pos (by positivity)] at h2
    have e : (d * b) ^ 2 / (d * x) ^ 2 = b ^ 2 / x ^ 2 := by
      field_simp
    rw [e] at h2
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h2
  have mK' : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => fK (t.1, thA t.2.1)) := mfK.comp measurable_WX
  have mX' : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => fX (t.1, thA t.2.1)) := mfX.comp measurable_WX
  have pK := markov mK' hΔmax hΔKb0 iK
  have pX := markov mX' hΔXmax hΔXb0 iX
  have hbad := badAG0_prob_gen hn hG h1
  have hsub : (goodT2 G Δmax ΔXmax)ᶜ ⊆
      {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
        t.1 ∉ goodWAG G} ∪
      ({t | ENNReal.ofReal ((d * Δmax) ^ 2) < fK (t.1, thA t.2.1)} ∪
        {t | ENNReal.ofReal ((d * ΔXmax) ^ 2) < fX (t.1, thA t.2.1)}) := by
    intro t ht
    by_cases hW : t.1 ∈ goodWAG G
    swap
    · exact Or.inl hW
    refine Or.inr ?_
    have hWx : (t.1, thA t.2.1) ∈ {x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) |
        x.1 ∈ goodWAG G} := hW
    by_cases hK : eK t.1 (thA t.2.1) ≤ (d * Δmax) ^ 2
    · refine Or.inr ?_
      have hD : ¬ eX t.1 (thA t.2.1) ≤ (d * ΔXmax) ^ 2 := fun hD => ht ⟨hW, hK, hD⟩
      push Not at hD
      change ENNReal.ofReal ((d * ΔXmax) ^ 2) < fX (t.1, thA t.2.1)
      rw [hfX, Set.indicator_of_mem hWx]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (sq_nonneg _) hD)).mpr hD
    · refine Or.inl ?_
      push Not at hK
      change ENNReal.ofReal ((d * Δmax) ^ 2) < fK (t.1, thA t.2.1)
      rw [hfK, Set.indicator_of_mem hWx]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (sq_nonneg _) hK)).mpr hK
  calc μ.real (goodT2 G Δmax ΔXmax)ᶜ
      ≤ μ.real ({t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
        t.1 ∉ goodWAG G} ∪
        ({t | ENNReal.ofReal ((d * Δmax) ^ 2) < fK (t.1, thA t.2.1)} ∪
          {t | ENNReal.ofReal ((d * ΔXmax) ^ 2) < fX (t.1, thA t.2.1)})) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
        t.1 ∉ goodWAG G} +
        (μ.real {t | ENNReal.ofReal ((d * Δmax) ^ 2) < fK (t.1, thA t.2.1)} +
          μ.real {t | ENNReal.ofReal ((d * ΔXmax) ^ 2) < fX (t.1, thA t.2.1)}) :=
        (measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le _ _))
    _ ≤ _ := by linarith

end BstLean.Part149

open BstLean.Part149 in
#print axioms W_mean
open BstLean.Part149 in
#print axioms errA2_lint
open BstLean.Part149 in
#print axioms badT2_prob
