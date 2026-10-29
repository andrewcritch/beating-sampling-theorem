import BstLean.Part150Samp

/-!
# Part 150, item 5, the frame with `k` forward passes of `F`

The text of `Part149Final4` (`sampB149_formula`) for a generic measurable centre map `bh`, with
the displacement term of `Part150Disp`.

* `bh_len`: on the good event `|bh|² ≤ (m/n)·y4`.
* **`displaceSamp150_formula`**: `Pr(|gSampH bh k − B| ≤ sd/2) ≥ 1 − pFail6`, the probability
  over `(W, A, F)` and the `k` Gaussian vectors.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss hbar)
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142 BstLean.Part143 BstLean.Part145
open BstLean.Part149

variable {n : ℕ}

/-- On the good event the centre `bh` is shorter than `√((m/n)·y4)`. -/
lemma bh_len (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))}
    {alo ahi : ℝ} (hwin : WinOK2 n G alo ahi) {Δmax ΔXmax εD εQ π₀ Dmax ρhi yhi : ℝ}
    (hΔmax : 0 < Δmax) (hA1 : Δmax < alo) (hA2 : ahi + Δmax < 1)
    (hP : POK3 ahi Δmax εD εQ π₀ Dmax ρhi yhi) (bh : CMap n) {D4 y4 : ℝ} (hD4 : 0 ≤ D4)
    (hy4 : (√yhi + D4) ^ 2 ≤ y4)
    {W : MlpParam (2 * n) (mW n) n} {θ : HidParam n (mA n)}
    (hx2 : (W, θ) ∈ goodX2 G Δmax ΔXmax) (hx3 : (W, θ) ∈ goodX3 G εD εQ Dmax)
    (hx4 : (W, θ) ∈ goodX4 bh D4) :
    normSq (bh (W, θ)) ≤ (mA n : ℝ) / n * y4 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  have hd0 : (0 : ℝ) < (mA n : ℝ) / n := by positivity
  set d : ℝ := (mA n : ℝ) / n with hd
  have hYm := bMF_len (ΔXmax := ΔXmax) hn hwin hΔmax hA1 hA2 hP hx2 hx3
  have hdisp : normSq (bh (W, θ) - bMF (cenA W) (tauWA W) θ) ≤ d * D4 ^ 2 := hx4
  have t1 := BstLean.Part140.nrm_add_le' (bMF (cenA W) (tauWA W) θ)
    (bh (W, θ) - bMF (cenA W) (tauWA W) θ)
  have eb : bMF (cenA W) (tauWA W) θ + (bh (W, θ) - bMF (cenA W) (tauWA W) θ) =
      bh (W, θ) := by abel
  rw [eb] at t1
  have n1 := nrm_sq (bh (W, θ))
  have p1 := nrm_nonneg (bh (W, θ))
  have q2 : nrm (bMF (cenA W) (tauWA W) θ) ≤ √d * √yhi := by
    refine (Real.sqrt_le_sqrt hYm).trans (le_of_eq ?_)
    rw [Real.sqrt_mul hd0.le]
  have q3 : nrm (bh (W, θ) - bMF (cenA W) (tauWA W) θ) ≤ √d * D4 := by
    refine (Real.sqrt_le_sqrt hdisp).trans (le_of_eq ?_)
    rw [Real.sqrt_mul hd0.le, Real.sqrt_sq hD4]
  have hsd := Real.sq_sqrt hd0.le
  have q1 : nrm (bh (W, θ)) ≤ √d * (√yhi + D4) := by linarith
  have : nrm (bh (W, θ)) ^ 2 ≤ (√d * (√yhi + D4)) ^ 2 := pow_le_pow_left₀ p1 q1 2
  rw [n1, mul_pow, hsd] at this
  exact this.trans (mul_le_mul_of_nonneg_left hy4 hd0.le)

/-- `1_good·(gSampH − gOutH)²`. -/
noncomputable def dSampH (k : ℕ) (G : Set (HidParam (2 * n) (mW n))) (Δmax ΔXmax εD εQ Dmax : ℝ)
    (bh : CMap n) (D4 : ℝ)
    (p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) : ℝ :=
  ({p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ) | (p.1.1, thA p.1.2.1) ∈
        (goodX2 G Δmax ΔXmax ∩ goodX3 G εD εQ Dmax) ∩ goodX4 bh D4}).indicator
    (fun p => (gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - gOutH bh p.1.1 p.1.2.1 p.1.2.2) ^ 2) p

/-- The bound of the failure probability for the centre `bh` and `k` forward passes of `F`. -/
noncomputable def pFail6 (n k : ℕ) (Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb
    εD εQ π₀ Dmax yhi ζ₃ η₃ dQb η₄ ξ D4 y4 η₅ : ℝ) : ℝ :=
  pFail5 n Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb εD εQ π₀ Dmax yhi ζ₃ η₃ dQb η₄ ξ D4 y4 +
    η₅ * (4 * ((1 + η₄) * aE3 n Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ ΔKb ΔXb δb εD π₀ yhi ζ₃ η₃ dQb +
      (1 + 1 / η₄) * (2 / (n : ℝ) * (2 / (1 - y4)) * ξ)) /
        (θ * (4 / (n : ℝ) * (222757 / 1000000)))) +
    (1 + 1 / η₅) * (4 * (4 / (n : ℝ) / k) / (θ * (4 / (n : ℝ) * (222757 / 1000000))))

/-- **A program with another centre and `k` forward passes of `F` succeeds**, formula with free
parameters. -/
theorem displaceSamp150_formula (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    {Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb εD εQ π₀ Dmax ρhi yhi ζ₃ η₃ dQb : ℝ}
    (hP : POK2 (6662 / 10000) (6969 / 10000) Δmax ΔXmax r₁ r₂ w g)
    {η₄ : ℝ} (hη₄ : 0 < η₄) {η₅ : ℝ} (hη₅ : 0 < η₅)
    (hP3 : POK3 (6969 / 10000) Δmax εD εQ π₀ Dmax ρhi yhi) (hζ₃ : 0 < ζ₃) (hη₃ : 0 < η₃)
    (hdQ : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dQ1 n (mA n) q ≤ dQb)
    (hQ0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dQ1 n (mA n) q)
    (hη : 0 < η) (hζ : 0 < ζ) (hζ₂ : 0 < ζ₂) (hη₁ : 0 < η₁) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hΔKb0 : 0 ≤ ΔKb) (hΔXb0 : 0 ≤ ΔXb)
    (hΔK : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dK2 n (mA n) q ≤ ΔKb)
    (hK0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dK2 n (mA n) q)
    (hΔX : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dX2 n (mA n) q ≤ ΔXb)
    (hX0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dX2 n (mA n) q)
    (hδb : cF2o (mA n) ≤ δb)
    {bh : CMap n} (hbh : Measurable bh) {D4 y4 : ℝ} (hD4 : 0 < D4)
    (hy4 : (√yhi + D4) ^ 2 ≤ y4) (hy41 : y4 < 1) {ξ : ℝ} (hξ0 : 0 ≤ ξ)
    (hξ : DispOK n (Gwin n) εD εQ bh ξ) :
    1 - pFail6 n k Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb εD εQ π₀ Dmax yhi ζ₃ η₃ dQb
        η₄ ξ D4 y4 η₅ ≤
      ((mlpTriple 2 n).prod (gamK k n)).real
        {p | |gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
          sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  obtain ⟨errH, c, e, merrH, herr0H, hcovH, hEH, hbadT, hV, hcc, he0, heR, haE0⟩ :=
    frame150 hn hP hη₄ hP3 hζ₃ hη₃ hdQ hQ0 hη hζ hζ₂ hη₁ hθ0 hθ1 hΔKb0 hΔXb0 hΔK hK0 hΔX hX0 hδb hbh hD4 hy4 hy41 hξ0 hξ
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hG := (goodEvFR hn).to0
  have hwin := winOK2_149 hn
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have hy41' : 0 < 1 - y4 := by linarith
  set c₀ : ℝ := 4 / (n : ℝ) * (222757 / 1000000) with hc₀
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  have hc0 : 0 < c := lt_of_lt_of_le hc₀0 hcc
  set aE : ℝ := aE3 n Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ ΔKb ΔXb δb εD π₀ yhi ζ₃ η₃ dQb with haE
  set aH : ℝ := 2 / (n : ℝ) * (2 / (1 - y4)) * ξ with haH
  have haH0 : 0 ≤ aH := by rw [haH]; positivity
  set aEH : ℝ := (1 + η₄) * aE + (1 + 1 / η₄) * aH with haEH
  have haEH0 : 0 ≤ aEH := by rw [haEH]; positivity
  have msd3 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => sdn t.1 t.2.1 t.2.2) := measurable_sdn (mA := mA n) (mF := mF n) hN
  -- the product space
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set μ' := (mlpTriple 2 n).prod (gamK k n) with hμ'
  have hbad' : μ'.real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1 ∈ goodT234 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4}ᶜ ≤
      1 / 50000 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 + ΔKb ^ 2 / Δmax ^ 2 +
        ΔXb ^ 2 / ΔXmax ^ 2 +
      (1 / 50000 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 + dQb ^ 2 / εQ ^ 2 +
        5 / (mA n : ℝ) / εD ^ 2 + xiB n εD π₀ ζ₃ dQb / Dmax ^ 2) + ξ / D4 ^ 2 :=
    (prod_fst_real (mlpTriple 2 n) (gamK k n)
      (goodT234 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4)ᶜ).trans_le hbadT
  have msd : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => sdn p.1.1 p.1.2.1 p.1.2.2) :=
    msd3.comp measurable_fst
  have hV' : ∫⁻ p, ENNReal.ofReal ((sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2 - c) ^ 2) ∂μ' ≤
      ENNReal.ofReal (2 * (4 / (n : ℝ) * e) ^ 2) := by
    set Fs : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
      fun t => ENNReal.ofReal ((sdn t.1 t.2.1 t.2.2 ^ 2 - c) ^ 2) with hFs
    have mFs : Measurable Fs :=
      ENNReal.measurable_ofReal.comp (((msd3.pow_const 2).sub measurable_const).pow_const 2)
    have e3 : ∫⁻ p, ENNReal.ofReal ((sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2 - c) ^ 2) ∂μ' =
        ∫⁻ p, Fs p.1 ∂μ' := rfl
    rw [e3, hμ', lintegral_prod (fun p => Fs p.1) (mFs.comp measurable_fst).aemeasurable]
    simp only [lintegral_const, measure_univ, mul_one]
    exact hV
  have mX : MeasurableSet ((goodX2 (Gwin n) Δmax ΔXmax ∩ goodX3 (Gwin n) εD εQ Dmax) ∩ goodX4 bh D4) :=
    ((goodX2_meas hG hn1 Δmax ΔXmax).inter (goodX3_meas hG hn1 εD εQ Dmax)).inter
      (goodX4_meas hbh D4)
  have hlen : ∀ x ∈ (goodX2 (Gwin n) Δmax ΔXmax ∩ goodX3 (Gwin n) εD εQ Dmax) ∩ goodX4 bh D4,
      normSq (bh x) ≤ (mA n : ℝ) / n := by
    intro x hx
    have hd0 : (0 : ℝ) < (mA n : ℝ) / n := by
      have : (0 : ℝ) < mA n := by exact_mod_cast hmA
      positivity
    have h1 := bh_len hn hwin hP.hΔmax hP.hA1 hP.hA2 hP3 bh hD4.le hy4 (W := x.1) (θ := x.2)
      hx.1.1 hx.1.2 hx.2
    exact h1.trans ((mul_le_mul_of_nonneg_left hy41.le hd0.le).trans (le_of_eq (mul_one _)))
  have hS := sampH_lint hn1 hk hbh mX hlen
  have mgS := measurable_gSampH hbh k
  have mgB : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => gOutH bh p.1.1 p.1.2.1 p.1.2.2) :=
    (measurable_gOutH hbh).comp measurable_fst
  have mSet : MeasurableSet {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
      (p.1.1, thA p.1.2.1) ∈ (goodX2 (Gwin n) Δmax ΔXmax ∩ goodX3 (Gwin n) εD εQ Dmax) ∩ goodX4 bh D4} :=
    (measurable_WX.comp measurable_fst) mX
  have mdS : Measurable (dSampH k (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4) :=
    ((mgS.sub mgB).pow_const 2).indicator mSet
  have hdS0 : ∀ p, 0 ≤ dSampH k (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 p := fun p =>
    Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  set err' : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ) → ℝ :=
    fun p => (1 + η₅) * errH p.1 + (1 + 1 / η₅) * dSampH k (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 p
    with herr'
  have merr' : Measurable err' :=
    ((merrH.comp measurable_fst).const_mul _).add (mdS.const_mul _)
  have herr0' : ∀ p, 0 ≤ err' p := fun p => by
    have := herr0H p.1
    have := hdS0 p
    simp only [herr']
    positivity
  have hE' : ∫⁻ p, ENNReal.ofReal (err' p) ∂μ' ≤
      ENNReal.ofReal ((1 + η₅) * aEH + (1 + 1 / η₅) * (4 / (n : ℝ) / k)) := by
    have e : ∀ p, ENNReal.ofReal (err' p) =
        ENNReal.ofReal (1 + η₅) * ENNReal.ofReal (errH p.1) +
          ENNReal.ofReal (1 + 1 / η₅) *
            ENNReal.ofReal (dSampH k (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 p) := by
      intro p
      have := herr0H p.1
      have := hdS0 p
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    have mm1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1 => ENNReal.ofReal (errH t)) := ENNReal.measurable_ofReal.comp merrH
    have mm1' : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => ENNReal.ofReal (errH p.1)) :=
      mm1.comp measurable_fst
    have mm2 : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) =>
        ENNReal.ofReal (dSampH k (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 p)) :=
      ENNReal.measurable_ofReal.comp mdS
    rw [lintegral_congr e, lintegral_add_left (mm1'.const_mul _), lintegral_const_mul _ mm1',
      lintegral_const_mul _ mm2]
    have i1 : ∫⁻ p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ), ENNReal.ofReal (errH p.1) ∂μ' ≤
        ENNReal.ofReal aEH := by
      rw [hμ', lintegral_prod (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => ENNReal.ofReal (errH p.1)) mm1'.aemeasurable]
      simp only [lintegral_const, measure_univ, mul_one]
      exact hEH
    have i2 : ∫⁻ p, ENNReal.ofReal (dSampH k (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 p) ∂μ' ≤
        ENNReal.ofReal (4 / (n : ℝ) / k) := hS
    refine (add_le_add (mul_le_mul' le_rfl i1) (mul_le_mul' le_rfl i2)).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  -- the assembly
  have h := ok_joint μ'
    (G := {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1 ∈ goodT234 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4}) (Z := ∅)
    (d := fun p => gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2)
    (sd := fun p => sdn p.1.1 p.1.2.1 p.1.2.2) (err := err')
    (fun p => sdn_nonneg' _ _ _) msd merr' herr0'
    (by
      intro p hg _
      have hg' : p.1 ∈ goodT234 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 := hg
      have hc1 := hcovH p.1 hg'
      have hmemS : p ∈ {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
          (p.1.1, thA p.1.2.1) ∈ (goodX2 (Gwin n) Δmax ΔXmax ∩ goodX3 (Gwin n) εD εQ Dmax) ∩ goodX4 bh D4} :=
        ⟨⟨hg'.1.1, hg'.1.2⟩, hg'.2⟩
      simp only [herr']
      unfold dSampH
      rw [Set.indicator_of_mem hmemS]
      have s1 := sq_add_le' hη₅ (gOutH bh p.1.1 p.1.2.1 p.1.2.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2)
        (gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - gOutH bh p.1.1 p.1.2.1 p.1.2.2)
      have e3 : gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2 =
          (gOutH bh p.1.1 p.1.2.1 p.1.2.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2) +
            (gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - gOutH bh p.1.1 p.1.2.1 p.1.2.2) := by ring
      have hp : (0 : ℝ) ≤ 1 + η₅ := by positivity
      have s3 := mul_le_mul_of_nonneg_left hc1 hp
      rw [e3]
      linarith)
    (by simp) hc0 hθ0 hθ1 (by positivity : (0 : ℝ) ≤ (1 + η₅) * aEH + (1 + 1 / η₅) *
      (4 / (n : ℝ) / k)) (by positivity : (0 : ℝ) ≤ 2 * (4 / (n : ℝ) * e) ^ 2) hbad' hE' hV'
  refine le_trans ?_ h
  -- from `c` to `c₀` and from `e` to its bound
  have t1 : 4 * ((1 + η₅) * aEH + (1 + 1 / η₅) * (4 / (n : ℝ) / k)) / (θ * c) ≤
      4 * ((1 + η₅) * aEH + (1 + 1 / η₅) * (4 / (n : ℝ) / k)) / (θ * c₀) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hcc hθ0.le)
  have he2 : (4 / (n : ℝ) * e) ^ 2 ≤ (4 / (n : ℝ) * (78728 / 100000 / √(n : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left heR (by positivity)) 2
  have t2 : 2 * (4 / (n : ℝ) * e) ^ 2 / (4 * θ * (1 - θ) * c ^ 2) ≤
      2 * (4 / (n : ℝ) * (78728 / 100000 / √(n : ℝ))) ^ 2 / (4 * θ * (1 - θ) * c₀ ^ 2) := by
    have hden : 4 * θ * (1 - θ) * c₀ ^ 2 ≤ 4 * θ * (1 - θ) * c ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc₀0.le hcc 2) (by positivity)
    calc 2 * (4 / (n : ℝ) * e) ^ 2 / (4 * θ * (1 - θ) * c ^ 2)
        ≤ 2 * (4 / (n : ℝ) * e) ^ 2 / (4 * θ * (1 - θ) * c₀ ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)
  have e5 : 4 * aEH / (θ * c₀) =
      4 * aE / (θ * c₀) + η₄ * (4 * aE / (θ * c₀)) + (1 + 1 / η₄) * (4 * aH / (θ * c₀)) := by
    rw [haEH]; ring
  have e6 : 4 * ((1 + η₅) * aEH + (1 + 1 / η₅) * (4 / (n : ℝ) / k)) / (θ * c₀) =
      4 * aEH / (θ * c₀) + η₅ * (4 * aEH / (θ * c₀)) +
        (1 + 1 / η₅) * (4 * (4 / (n : ℝ) / k) / (θ * c₀)) := by
    ring
  unfold pFail6 pFail5 pFail3
  rw [← haE, ← hc₀, ← haH, ← haEH]
  unfold aE3 at haE
  rw [← haE]
  linarith

end BstLean.Part150

open BstLean.Part150 in
#print axioms displaceSamp150_formula
