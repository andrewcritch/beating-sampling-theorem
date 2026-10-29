import BstLean.Part149Final4

/-!
# Part 150, item 5, the frame: a program with ANOTHER centre of the last hidden layer of `A`

Role: `delegations/statements/p150-spec.md`, item 5. Lean source: `Part149Final3`
(`onePassA149_formula`), `Part149Asm3` (`errB_key`, `errB_lint`, `badT3_prob`).

`bh (W, (A₁, A₂))` is ANY measurable centre (a vector of `ℝ^m`, `m = mA n`). The program output
with this centre is `gOutH bh W A F = E_γ′ F(A₃·bh + tauOutOf n bh·γ′)`. Part 149 has the
mean-field centre `bMF` (oracle values). `dispH bh x = |bh x − bMF|²` is the squared
displacement of the centre.

* `errH_key`, `errH_lint`: Lemma C of Part 149 (`outCompare_tau`) pays for the displacement:
  `E[1_good·(gOutH − gOutB)²] ≤ (2/n)·(2/(1 − y4))·ξ` if `E[1_good·dispH] ≤ (m/n)·ξ`.
* `badT4_prob`: the event `dispH ≤ (m/n)·D4²` fails with probability at most `ξ/D4²` more.
* **`displace150_formula`**: `Pr(|gOutH − B| ≤ sd/2) ≥ 1 − pFail5`, with
  `pFail5 = pFail3 + η₄·(4·aE3/(θc₀)) + ξ/D4² + (1 + 1/η₄)·4·(2/n)(2/(1 − y4))ξ/(θc₀)`.
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

/-- The type of a centre map: from `(W, (A₁, A₂))` to a vector of `ℝ^m`. -/
abbrev CMap (n : ℕ) : Type :=
  MlpParam (2 * n) (mW n) n × HidParam n (mA n) → Fin (mA n) → ℝ

/-- The output of the program with the centre `bh`: `E_γ′ F(A₃·bh + tauOutOf n bh·γ′)`. -/
noncomputable def gOutH (bh : CMap n) {mF : ℕ} (W : MlpParam (2 * n) (mW n) n)
    (A : MlpParam n (mA n) n) (F : MlpParam n mF 1) : ℝ :=
  gO (bh (W, thA A)) (tauOutOf n (bh (W, thA A))) (A.2.2, F)

/-- The squared displacement of the centre `bh` from the mean-field centre of Part 149. -/
noncomputable def dispH (bh : CMap n) (x : MlpParam (2 * n) (mW n) n × HidParam n (mA n)) : ℝ :=
  normSq (bh x - bMF (cenA x.1) (tauWA x.1) x.2)

/-- The event `dispH ≤ (m/n)·D4²`. -/
def goodX4 (bh : CMap n) (D4 : ℝ) : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n)) :=
  {x | dispH bh x ≤ (mA n : ℝ) / n * D4 ^ 2}

/-- The same as an event of `(W, A, F)`. -/
def goodT4 (bh : CMap n) (D4 : ℝ) :
    Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :=
  {t | (t.1, thA t.2.1) ∈ goodX4 bh D4}

/-- The good event of the program with the centre `bh`. -/
def goodT234 (G : Set (HidParam (2 * n) (mW n))) (Δmax ΔXmax εD εQ Dmax : ℝ) (bh : CMap n)
    (D4 : ℝ) : Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :=
  goodT23 G Δmax ΔXmax εD εQ Dmax ∩ goodT4 bh D4

/-- `1_good·(gOutH − gOutB)²`. -/
noncomputable def dOut4 (G : Set (HidParam (2 * n) (mW n))) (Δmax ΔXmax εD εQ Dmax : ℝ)
    (bh : CMap n) (D4 : ℝ)
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) : ℝ :=
  (goodT234 G Δmax ΔXmax εD εQ Dmax bh D4).indicator
    (fun t => (gOutH bh t.1 t.2.1 t.2.2 - gOutB t.1 t.2.1 t.2.2) ^ 2) t

lemma dOut4_nonneg (G : Set (HidParam (2 * n) (mW n))) (Δmax ΔXmax εD εQ Dmax : ℝ)
    (bh : CMap n) (D4 : ℝ)
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :
    0 ≤ dOut4 G Δmax ΔXmax εD εQ Dmax bh D4 t := Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

/-! ## Measurability -/

lemma measurable_dispH {bh : CMap n} (hbh : Measurable bh) : Measurable (dispH bh) := by
  have h2 := (measurable_bMF (n := n) (m := mA n)).comp measurable_cτθ
  simp only [Function.comp_def] at h2
  exact measurable_normSq.comp (hbh.sub h2)

lemma goodX4_meas {bh : CMap n} (hbh : Measurable bh) (D4 : ℝ) : MeasurableSet (goodX4 bh D4) :=
  measurableSet_le (measurable_dispH hbh) measurable_const

lemma goodT4_meas {bh : CMap n} (hbh : Measurable bh) (D4 : ℝ) :
    MeasurableSet (goodT4 (n := n) bh D4) :=
  measurable_WX (goodX4_meas hbh D4)

lemma measurable_gOutH {bh : CMap n} (hbh : Measurable bh) :
    Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      gOutH bh t.1 t.2.1 t.2.2) := by
  have hp : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => (t.2.1.2.2, t.2.2)) :=
    (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  have hb : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => bh (t.1, thA t.2.1)) := hbh.comp measurable_WX
  have hτ : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => tauOutOf n (bh (t.1, thA t.2.1))) :=
    measurable_tauOutOf.comp hb
  have h3 := (measurable_gO_joint (n := n) (m := mA n) (mF := mF n)).comp
    ((hb.prodMk hτ).prodMk hp)
  simp only [Function.comp_def] at h3
  exact h3

lemma measurable_dOut4 {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤ n)
    (Δmax ΔXmax εD εQ Dmax : ℝ) {bh : CMap n} (hbh : Measurable bh) (D4 : ℝ) :
    Measurable (dOut4 G Δmax ΔXmax εD εQ Dmax bh D4) :=
  (((measurable_gOutH hbh).sub measurable_gOutB).pow_const 2).indicator
    ((goodT23_meas hG hn Δmax ΔXmax εD εQ Dmax).inter (goodT4_meas hbh D4))

/-! ## Lemma C pays for the displacement -/

/-- The stage at fixed `(W, A₁, A₂)`, integrated over `(A₃, F)`. -/
lemma errH_key (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))}
    {alo ahi : ℝ} (hwin : WinOK2 n G alo ahi) {Δmax ΔXmax εD εQ π₀ Dmax ρhi yhi : ℝ}
    (hΔmax : 0 < Δmax) (hA1 : Δmax < alo) (hA2 : ahi + Δmax < 1)
    (hP : POK3 ahi Δmax εD εQ π₀ Dmax ρhi yhi) (bh : CMap n) {D4 y4 : ℝ} (hD4 : 0 ≤ D4)
    (hy4 : (√yhi + D4) ^ 2 ≤ y4) (hy41 : y4 < 1)
    (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)) :
    ∫⁻ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        ENNReal.ofReal (dOut4 G Δmax ΔXmax εD εQ Dmax bh D4 (W, (θ.1, θ.2, y.1), y.2))
        ∂((gaussMat n (mA n) (2 / (mA n : ℝ))).prod (mlpGauss n (mF n) 1)) ≤
      ENNReal.ofReal (2 / (n : ℝ) * (2 / (1 - y4)) / ((mA n : ℝ) / n)) *
        (goodX1 G εD εQ).indicator (fun x => ENNReal.ofReal (dispH bh x)) (W, θ) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := BstLean.Part132.mF_ge hn; omega
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  have hd0 : (0 : ℝ) < (mA n : ℝ) / n := by positivity
  have hy1 : 0 < 1 - y4 := by linarith
  by_cases hx : ((W, θ) ∈ goodX2 G Δmax ΔXmax ∧ (W, θ) ∈ goodX3 G εD εQ Dmax) ∧
      (W, θ) ∈ goodX4 bh D4
  · obtain ⟨⟨hx2, hx3⟩, hx4⟩ := hx
    have hx1 : (W, θ) ∈ goodX1 G εD εQ := hx3.1
    rw [Set.indicator_of_mem hx1]
    have hmem : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        ((W, (θ.1, θ.2, y.1), y.2) : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) ∈ goodT234 G Δmax ΔXmax εD εQ Dmax bh D4 :=
      fun y => ⟨⟨hx2, hx3⟩, hx4⟩
    have e : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        dOut4 G Δmax ΔXmax εD εQ Dmax bh D4 (W, (θ.1, θ.2, y.1), y.2) =
          (gO (bh (W, θ)) (tauOutOf n (bh (W, θ))) y -
            gO (bMF (cenA W) (tauWA W) θ) (tauOutOf n (bMF (cenA W) (tauWA W) θ)) y) ^ 2 := by
      intro y
      unfold dOut4
      rw [Set.indicator_of_mem (hmem y)]
      rfl
    simp_rw [e]
    set d : ℝ := (mA n : ℝ) / n with hd
    have hyhi0 : 0 ≤ yhi := le_trans (sq_nonneg _) hP.hy
    have hYm := bMF_len (ΔXmax := ΔXmax) hn hwin hΔmax hA1 hA2 hP hx2 hx3
    have hdisp : normSq (bh (W, θ) - bMF (cenA W) (tauWA W) θ) ≤ d * D4 ^ 2 := hx4
    have hsy : 0 ≤ √yhi := Real.sqrt_nonneg _
    have hYm4 : normSq (bMF (cenA W) (tauWA W) θ) ≤ d * y4 := by
      refine hYm.trans (mul_le_mul_of_nonneg_left ?_ hd0.le)
      have h1 : yhi = √yhi ^ 2 := (Real.sq_sqrt hyhi0).symm
      nlinarith
    have hYh : normSq (bh (W, θ)) ≤ d * y4 := by
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
    have hYd : d * y4 < (mA n : ℝ) / n := by rw [← hd]; nlinarith
    have hcmp := outCompare_tau (mF := mF n) hn1 hmA hmF hYh hYm4 hYd
    refine hcmp.trans (le_of_eq ?_)
    have hC0 : 0 ≤ dispH bh (W, θ) := normSq_nonneg _
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have e1 : normSq (bh (W, θ) - bMF (cenA W) (tauWA W) θ) = dispH bh (W, θ) := rfl
    rw [e1, ← hd]
    have hyne : (1 - y4) ≠ 0 := hy1.ne'
    have e2 : d / (d - d * y4) = 1 / (1 - y4) := by
      rw [show d - d * y4 = d * (1 - y4) by ring]
      field_simp
    rw [e2, hd]
    field_simp
  · have hmem : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        ((W, (θ.1, θ.2, y.1), y.2) : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) ∉ goodT234 G Δmax ΔXmax εD εQ Dmax bh D4 :=
      fun y h => hx ⟨⟨h.1.1, h.1.2⟩, h.2⟩
    have e : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        dOut4 G Δmax ΔXmax εD εQ Dmax bh D4 (W, (θ.1, θ.2, y.1), y.2) = 0 := fun y => by
      unfold dOut4
      rw [Set.indicator_of_notMem (hmem y)]
    simp_rw [e]
    simp

/-- The hypothesis on the centre: `E[1_good·dispH] ≤ (m/n)·ξ`. -/
def DispOK (n : ℕ) (G : Set (HidParam (2 * n) (mW n))) (εD εQ : ℝ) (bh : CMap n) (ξ : ℝ) : Prop :=
  ∫⁻ W, ∫⁻ θ, (goodX1 G εD εQ).indicator (fun x => ENNReal.ofReal (dispH bh x)) (W, θ)
      ∂hidGauss n (mA n) ∂mlpGauss (2 * n) (mW n) n ≤
    ENNReal.ofReal ((mA n : ℝ) / n * ξ)

/-- **Lemma C pays for the displacement**:
`E[1_good·(gOutH − gOutB)²] ≤ (2/n)·(2/(1 − y4))·ξ`. -/
theorem errH_lint (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {alo ahi : ℝ} (hwin : WinOK2 n G alo ahi) {Δmax ΔXmax εD εQ π₀ Dmax ρhi yhi : ℝ}
    (hΔmax : 0 < Δmax) (hA1 : Δmax < alo) (hA2 : ahi + Δmax < 1)
    (hP : POK3 ahi Δmax εD εQ π₀ Dmax ρhi yhi) {bh : CMap n} (hbh : Measurable bh)
    {D4 y4 : ℝ} (hD4 : 0 ≤ D4) (hy4 : (√yhi + D4) ^ 2 ≤ y4) (hy41 : y4 < 1) {ξ : ℝ}
    (_hξ0 : 0 ≤ ξ) (hξ : DispOK n G εD εQ bh ξ) :
    ∫⁻ t, ENNReal.ofReal (dOut4 G Δmax ΔXmax εD εQ Dmax bh D4 t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (2 / (n : ℝ) * (2 / (1 - y4)) * ξ) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  have hd0 : (0 : ℝ) < (mA n : ℝ) / n := by positivity
  have hy1 : 0 < 1 - y4 := by linarith
  have mOD : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ENNReal.ofReal (dOut4 G Δmax ΔXmax εD εQ Dmax bh D4 t)) :=
    ENNReal.measurable_ofReal.comp (measurable_dOut4 hG hn1 Δmax ΔXmax εD εQ Dmax hbh D4)
  have mind : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) =>
      (goodX1 G εD εQ).indicator (fun x => ENNReal.ofReal (dispH bh x)) x) :=
    (ENNReal.measurable_ofReal.comp (measurable_dispH hbh)).indicator (goodX1_meas hG hn1 εD εQ)
  have inner : ∀ W : MlpParam (2 * n) (mW n) n,
      ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
          ENNReal.ofReal (dOut4 G Δmax ΔXmax εD εQ Dmax bh D4 (W, p))
          ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) ≤
        ENNReal.ofReal (2 / (n : ℝ) * (2 / (1 - y4)) / ((mA n : ℝ) / n)) *
          ∫⁻ θ, (goodX1 G εD εQ).indicator (fun x => ENNReal.ofReal (dispH bh x)) (W, θ)
            ∂hidGauss n (mA n) := by
    intro W
    have mgW : Measurable (fun p : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
        ENNReal.ofReal (dOut4 G Δmax ΔXmax εD εQ Dmax bh D4 (W, p))) :=
      mOD.comp measurable_prodMk_left
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
    refine (lintegral_mono fun θ =>
      errH_key hn hwin hΔmax hA1 hA2 hP bh hD4 hy4 hy41 W θ).trans (le_of_eq ?_)
    exact lintegral_const_mul _ (mind.comp measurable_prodMk_left)
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
  rw [e0, lintegral_prod _ mOD.aemeasurable]
  refine (lintegral_mono inner).trans ?_
  rw [lintegral_const_mul _ mind.lintegral_prod_right']
  refine (mul_le_mul' le_rfl hξ).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  field_simp

/-- **The bad event of the displacement.** -/
theorem badT4_prob (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    (Δmax ΔXmax εD εQ Dmax : ℝ) {bh : CMap n} (hbh : Measurable bh) {D4 : ℝ} (hD4 : 0 < D4)
    {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ : DispOK n G εD εQ bh ξ) :
    (mlpTriple 2 n).real (goodT234 G Δmax ΔXmax εD εQ Dmax bh D4)ᶜ ≤
      (mlpTriple 2 n).real (goodT23 G Δmax ΔXmax εD εQ Dmax)ᶜ + ξ / D4 ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  set d : ℝ := (mA n : ℝ) / n with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  set fH : MlpParam (2 * n) (mW n) n × HidParam n (mA n) → ℝ≥0∞ :=
    (goodX1 G εD εQ).indicator (fun x => ENNReal.ofReal (dispH bh x)) with hfH
  have mfH : Measurable fH :=
    (ENNReal.measurable_ofReal.comp (measurable_dispH hbh)).indicator (goodX1_meas hG hn1 εD εQ)
  set μ := mlpTriple 2 n with hμ
  have iH : ∫⁻ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      fH (t.1, thA t.2.1) ∂μ ≤ ENNReal.ofReal (d * ξ) := by
    rw [hμ, lint_WX mfH]
    exact hξ
  have mH' : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => fH (t.1, thA t.2.1)) := mfH.comp measurable_WX
  have pH := markov_real μ mH' (ε := d * D4 ^ 2) (by positivity) (by positivity) iH
  have eH : d * ξ / (d * D4 ^ 2) = ξ / D4 ^ 2 := by field_simp
  rw [eH] at pH
  have hsub : (goodT234 G Δmax ΔXmax εD εQ Dmax bh D4)ᶜ ⊆
      (goodT23 G Δmax ΔXmax εD εQ Dmax)ᶜ ∪
        {t | ENNReal.ofReal (d * D4 ^ 2) < fH (t.1, thA t.2.1)} := by
    intro t ht
    by_cases h23 : t ∈ goodT23 G Δmax ΔXmax εD εQ Dmax
    swap
    · exact Or.inl h23
    refine Or.inr ?_
    have hX1 : (t.1, thA t.2.1) ∈ goodX1 G εD εQ := h23.2.1
    have hC : ¬ dispH bh (t.1, thA t.2.1) ≤ d * D4 ^ 2 := fun hC => ht ⟨h23, hC⟩
    push Not at hC
    change ENNReal.ofReal (d * D4 ^ 2) < fH (t.1, thA t.2.1)
    rw [hfH, Set.indicator_of_mem hX1]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (by positivity) hC)).mpr hC
  have hm := measureReal_mono (μ := μ) hsub (measure_ne_top _ _)
  have u1 := measureReal_union_le (μ := μ) (goodT23 G Δmax ΔXmax εD εQ Dmax)ᶜ
    {t | ENNReal.ofReal (d * D4 ^ 2) < fH (t.1, thA t.2.1)}
  linarith

/-! ## The success probability -/

/-- The error bound `aE` of `Part149Final3`. -/
noncomputable def aE3 (n : ℕ) (Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ ΔKb ΔXb δb εD π₀ yhi ζ₃ η₃ dQb : ℝ) :
    ℝ :=
  (1 + η₁) * (4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) + (1 + 1 / η₁) *
    ((1 + η₃) * (2 / (n : ℝ) * EA2 (6662 / 10000) Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb) +
      (1 + 1 / η₃) * (2 / (n : ℝ) * (2 / (1 - yhi)) * xiB n εD π₀ ζ₃ dQb))

/-- The bound of the failure probability for the centre `bh`. -/
noncomputable def pFail5 (n : ℕ) (Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb
    εD εQ π₀ Dmax yhi ζ₃ η₃ dQb η₄ ξ D4 y4 : ℝ) : ℝ :=
  pFail3 n Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb εD εQ π₀ Dmax yhi ζ₃ η₃ dQb +
    η₄ * (4 * aE3 n Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ ΔKb ΔXb δb εD π₀ yhi ζ₃ η₃ dQb /
      (θ * (4 / (n : ℝ) * (222757 / 1000000)))) +
    ξ / D4 ^ 2 +
    (1 + 1 / η₄) * (4 * (2 / (n : ℝ) * (2 / (1 - y4)) * ξ) /
      (θ * (4 / (n : ℝ) * (222757 / 1000000))))

/-- **The frame.** The error function `errH` of the program with the centre `bh` (exact mean
over the last Gaussian vector), the level `c` of the spread and its error `e`: everything that
the joint assembly `ok_joint` of Part 145 needs. The proof is the text of
`onePassA149_formula` (Part 149) with the displacement term. -/
lemma frame150 (hn : 4096 ≤ n)
    {Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb εD εQ π₀ Dmax ρhi yhi ζ₃ η₃ dQb : ℝ}
    (hP : POK2 (6662 / 10000) (6969 / 10000) Δmax ΔXmax r₁ r₂ w g)
    {η₄ : ℝ} (hη₄ : 0 < η₄)
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
    ∃ (errH : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ)
      (c e : ℝ),
      Measurable errH ∧ (∀ t, 0 ≤ errH t) ∧
      (∀ t ∈ goodT234 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4,
        (gOutH bh t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2) ^ 2 ≤ errH t) ∧
      ∫⁻ t, ENNReal.ofReal (errH t) ∂mlpTriple 2 n ≤
        ENNReal.ofReal ((1 + η₄) * aE3 n Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ ΔKb ΔXb δb εD π₀ yhi ζ₃ η₃ dQb +
          (1 + 1 / η₄) * (2 / (n : ℝ) * (2 / (1 - y4)) * ξ)) ∧
      (mlpTriple 2 n).real (goodT234 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4)ᶜ ≤
        1 / 50000 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 + ΔKb ^ 2 / Δmax ^ 2 +
          ΔXb ^ 2 / ΔXmax ^ 2 +
        (1 / 50000 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 + dQb ^ 2 / εQ ^ 2 +
          5 / (mA n : ℝ) / εD ^ 2 + xiB n εD π₀ ζ₃ dQb / Dmax ^ 2) + ξ / D4 ^ 2 ∧
      ∫⁻ t, ENNReal.ofReal ((sdn t.1 t.2.1 t.2.2 ^ 2 - c) ^ 2) ∂mlpTriple 2 n ≤
        ENNReal.ofReal (2 * (4 / (n : ℝ) * e) ^ 2) ∧
      4 / (n : ℝ) * (222757 / 1000000) ≤ c ∧ 0 ≤ e ∧ e ≤ 78728 / 100000 / √(n : ℝ) ∧
      0 ≤ aE3 n Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ ΔKb ΔXb δb εD π₀ yhi ζ₃ η₃ dQb := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmF : 1 ≤ mF n := by have := BstLean.Part132.mF_ge hn; omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hG := (goodEvFR hn).to0
  have hwin := winOK2_149 hn
  have hcF := BstLean.Part136.cF2o_pos hmA
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  set c : ℝ := 4 / (n : ℝ) * (1 - kappa^[6] 0) with hc
  set c₀ : ℝ := 4 / (n : ℝ) * (222757 / 1000000) with hc₀
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  have hcc : c₀ ≤ c := by
    rw [hc, hc₀]; exact mul_le_mul_of_nonneg_left hy (by positivity)
  have hc0 : 0 < c := lt_of_lt_of_le hc₀0 hcc
  set μ := mlpTriple 2 n with hμ
  -- the hidden event of `W`
  have hG1 : (hidGauss (2 * n) (mW n)).real (Gwin n)ᶜ ≤ 1 / 50000 / (n : ℝ) := by
    have h := Gwin_compl_n hn
    unfold cW at h
    have e : (15640 : ℝ) / 1073741824 / (n : ℝ) ≤ 1 / 50000 / (n : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num) hx0.le
    linarith
  have hbad2 := badT2_prob hn hG hwin hP.hΔmax hP.hΔXmax hΔKb0 hΔXb0 hΔK hK0 hΔX hX0 hG1
  have hbad3 := badT3_prob hn hG hwin hP3 hζ₃ hdQ hQ0 hG1
  have hbad : μ.real (goodT23 (Gwin n) Δmax ΔXmax εD εQ Dmax)ᶜ ≤
      1 / 50000 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 + ΔKb ^ 2 / Δmax ^ 2 +
        ΔXb ^ 2 / ΔXmax ^ 2 +
      (1 / 50000 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 + dQb ^ 2 / εQ ^ 2 +
        5 / (mA n : ℝ) / εD ^ 2 + xiB n εD π₀ ζ₃ dQb / Dmax ^ 2) := by
    have hsub : (goodT23 (Gwin n) Δmax ΔXmax εD εQ Dmax)ᶜ ⊆
        (goodT2 (Gwin n) Δmax ΔXmax)ᶜ ∪ (goodT3 (Gwin n) εD εQ Dmax)ᶜ := by
      intro t ht
      by_cases h2 : t ∈ goodT2 (Gwin n) Δmax ΔXmax
      · exact Or.inr fun h3 => ht ⟨h2, h3⟩
      · exact Or.inl h2
    have hm := measureReal_mono (μ := μ) hsub (measure_ne_top _ _)
    have hu := measureReal_union_le (μ := μ) (goodT2 (Gwin n) Δmax ΔXmax)ᶜ
      (goodT3 (Gwin n) εD εQ Dmax)ᶜ
    linarith
  -- the error
  obtain ⟨hΛi, hΛ⟩ := LamVR hn
  have hW := errVecAF_lint (goodEvFR hn) hn (by unfold Lam145R; norm_num) hΛi hΛ
    (ζ := 1 / 20) (by norm_num) (by norm_num) (η := 1 / 7) (by norm_num) (η' := 1 / 29)
    (by norm_num)
  have hXA := XA145_R hn
  have hXF0 := XF_nonneg hn (ΛV := Lam145R) (by unfold Lam145R; norm_num) (1 / 20)
    (η := 1 / 7) (by norm_num) (η' := 1 / 29) (by norm_num)
  have hA := errA2_lint hn hG hwin hP hη hζ hζ₂ hΔK hK0 hΔX hX0 hδb
  have hB := errB_lint (ΔXmax := ΔXmax) hn hG hwin hP.hΔmax hP.hA1 hP.hA2 hP3 hζ₃ hdQ hQ0
  have hy1 : 0 < 1 - yhi := by linarith [hP3.hy1]
  have hxi0 : 0 ≤ xiB n εD π₀ ζ₃ dQb := by
    have h1 := hP3.hπ0
    have h2 : 0 < 1 - π₀ := by linarith [hP3.hπ1]
    have h3 := Kq_nonneg
    unfold xiB cQ3 cD3
    positivity
  have hEA0 : 0 ≤ EA2 (6662 / 10000) Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb := by
    have hw := hP.hw
    have hg := hP.hg
    have := hP.hΔmax
    have := hP.hΔXmax
    have := hP.hr₁
    have hv : (0 : ℝ) ≤ 1 - 6662 / 10000 + Δmax := by linarith
    unfold EA2 Part149.kK2 Part149.kX2 Part149.kD2
    positivity
  set aE : ℝ := (1 + η₁) * (4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) + (1 + 1 / η₁) *
    ((1 + η₃) * (2 / (n : ℝ) * EA2 (6662 / 10000) Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb) +
      (1 + 1 / η₃) * (2 / (n : ℝ) * (2 / (1 - yhi)) * xiB n εD π₀ ζ₃ dQb)) with haE
  have haE0 : 0 ≤ aE := by rw [haE]; positivity
  set err : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ :=
    fun t => (1 + η₁) * errGAG (Gwin n) t + (1 + 1 / η₁) *
      ((1 + η₃) * dOut2 (Gwin n) Δmax ΔXmax t +
        (1 + 1 / η₃) * dOut3 (Gwin n) Δmax ΔXmax εD εQ Dmax t) with herr
  have hGn : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      0 ≤ errGAG (Gwin n) t := fun t => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  have m1 := measurable_errGAG0 hG hn1
  have m2 := measurable_dOut2 hG hn1 Δmax ΔXmax
  have m3 := measurable_dOut3 hG hn1 Δmax ΔXmax εD εQ Dmax
  have merr : Measurable err :=
    (m1.const_mul _).add (((m2.const_mul _).add (m3.const_mul _)).const_mul _)
  have herr0 : ∀ t, 0 ≤ err t := fun t => by
    have := hGn t
    have := dOut2_nonneg (Gwin n) Δmax ΔXmax t
    have := dOut3_nonneg (Gwin n) Δmax ΔXmax εD εQ Dmax t
    simp only [herr]
    positivity
  have hE : ∫⁻ t, ENNReal.ofReal (err t) ∂μ ≤ ENNReal.ofReal aE := by
    have e : ∀ t, ENNReal.ofReal (err t) =
        ENNReal.ofReal (1 + η₁) * ENNReal.ofReal (errGAG (Gwin n) t) +
          (ENNReal.ofReal ((1 + 1 / η₁) * (1 + η₃)) *
              ENNReal.ofReal (dOut2 (Gwin n) Δmax ΔXmax t) +
            ENNReal.ofReal ((1 + 1 / η₁) * (1 + 1 / η₃)) *
              ENNReal.ofReal (dOut3 (Gwin n) Δmax ΔXmax εD εQ Dmax t)) := by
      intro t
      have := hGn t
      have := dOut2_nonneg (Gwin n) Δmax ΔXmax t
      have := dOut3_nonneg (Gwin n) Δmax ΔXmax εD εQ Dmax t
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      simp only [herr]
      ring
    have mm1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1 => ENNReal.ofReal (errGAG (Gwin n) t)) :=
      ENNReal.measurable_ofReal.comp m1
    have mm2 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1 => ENNReal.ofReal (dOut2 (Gwin n) Δmax ΔXmax t)) :=
      ENNReal.measurable_ofReal.comp m2
    have mm3 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1 => ENNReal.ofReal (dOut3 (Gwin n) Δmax ΔXmax εD εQ Dmax t)) :=
      ENNReal.measurable_ofReal.comp m3
    rw [lintegral_congr e, lintegral_add_left (mm1.const_mul _),
      lintegral_add_left (mm2.const_mul _), lintegral_const_mul _ mm1,
      lintegral_const_mul _ mm2, lintegral_const_mul _ mm3]
    have hW' : ∫⁻ t, ENNReal.ofReal (errGAG (Gwin n) t) ∂μ ≤
        ENNReal.ofReal (4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) :=
      hW.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hXA (by positivity)))
    refine (add_le_add (mul_le_mul' le_rfl hW')
      (add_le_add (mul_le_mul' le_rfl hA) (mul_le_mul' le_rfl hB))).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [haE]
    ring
  -- the spread
  have he0 := eDBq_nonneg (biasK (mF n)) (tau143sC n) (pWC n) n
  have heR := eD145_R hn
  set e : ℝ := eDBq (biasK (mF n)) (tau143sC n) (pWC n) n with hed
  have msd3 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => sdn t.1 t.2.1 t.2.2) := measurable_sdn (mA := mA n) (mF := mF n) hN
  have hV : ∫⁻ t, ENNReal.ofReal ((sdn t.1 t.2.1 t.2.2 ^ 2 - c) ^ 2) ∂μ ≤
      ENNReal.ofReal (2 * (4 / (n : ℝ) * e) ^ 2) := by
    have mFs : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1 => ENNReal.ofReal ((sdn t.1 t.2.1 t.2.2 ^ 2 - c) ^ 2)) :=
      ENNReal.measurable_ofReal.comp (((msd3.pow_const 2).sub measurable_const).pow_const 2)
    have mπ : Measurable (fun r : Rest (2 * n) (mW n) n (mA n) (mF n) =>
        (r.1, r.2.1, r.2.2.2)) := by fun_prop
    have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
        ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
    rw [hμ, e0, ← lawR_drop, lintegral_map mFs mπ]
    exact spread_L2_dist2 hn1 hN hmF (by positivity : (0 : ℝ) ≤ 4 / (n : ℝ) * e) (kernR hn)
  have hcov : ∀ t ∈ goodT23 (Gwin n) Δmax ΔXmax εD εQ Dmax,
    (gOutB t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2) ^ 2 ≤ err t := by
    intro t hg
    have hW : t.1 ∈ goodWAG (Gwin n) := hg.1.1
    simp only [herr]
    unfold errGAG dOut2 dOut3
    rw [Set.indicator_of_mem hW, Set.indicator_of_mem hg.1, Set.indicator_of_mem hg]
    have s1 := sq_add_le' hη₃ (gOutA t.1 t.2.1 t.2.2 - gA t.1 t.2.1 t.2.2)
      (gOutB t.1 t.2.1 t.2.2 - gOutA t.1 t.2.1 t.2.2)
    have s2 := sq_add_le' hη₁ (gA t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2)
      ((gOutA t.1 t.2.1 t.2.2 - gA t.1 t.2.1 t.2.2) +
        (gOutB t.1 t.2.1 t.2.2 - gOutA t.1 t.2.1 t.2.2))
    have e3 : gOutB t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2 =
        (gA t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2) +
          ((gOutA t.1 t.2.1 t.2.2 - gA t.1 t.2.1 t.2.2) +
            (gOutB t.1 t.2.1 t.2.2 - gOutA t.1 t.2.1 t.2.2)) := by ring
    have hp : (0 : ℝ) ≤ 1 + 1 / η₁ := by positivity
    have s3 := mul_le_mul_of_nonneg_left s1 hp
    rw [e3]
    linarith
  -- the displacement
  have hy41' : 0 < 1 - y4 := by linarith
  have hH := errH_lint (ΔXmax := ΔXmax) hn hG hwin hP.hΔmax hP.hA1 hP.hA2 hP3 hbh hD4.le hy4
    hy41 hξ0 hξ
  have hbad4 := badT4_prob hn hG Δmax ΔXmax εD εQ Dmax hbh hD4 hξ0 hξ
  set aH : ℝ := 2 / (n : ℝ) * (2 / (1 - y4)) * ξ with haH
  have haH0 : 0 ≤ aH := by rw [haH]; positivity
  set errH : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ :=
    fun t => (1 + η₄) * err t + (1 + 1 / η₄) * dOut4 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 t
    with herrH
  have m4 := measurable_dOut4 hG hn1 Δmax ΔXmax εD εQ Dmax hbh D4
  have merrH : Measurable errH := (merr.const_mul _).add (m4.const_mul _)
  have herr0H : ∀ t, 0 ≤ errH t := fun t => by
    have := herr0 t
    have := dOut4_nonneg (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 t
    simp only [herrH]
    positivity
  set aEH : ℝ := (1 + η₄) * aE + (1 + 1 / η₄) * aH with haEH
  have haEH0 : 0 ≤ aEH := by rw [haEH]; positivity
  have hEH : ∫⁻ t, ENNReal.ofReal (errH t) ∂μ ≤ ENNReal.ofReal aEH := by
    have e : ∀ t, ENNReal.ofReal (errH t) =
        ENNReal.ofReal (1 + η₄) * ENNReal.ofReal (err t) +
          ENNReal.ofReal (1 + 1 / η₄) *
            ENNReal.ofReal (dOut4 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 t) := by
      intro t
      have := herr0 t
      have := dOut4_nonneg (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 t
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    have mm1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1 => ENNReal.ofReal (err t)) := ENNReal.measurable_ofReal.comp merr
    have mm4 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1 =>
        ENNReal.ofReal (dOut4 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4 t)) :=
      ENNReal.measurable_ofReal.comp m4
    rw [lintegral_congr e, lintegral_add_left (mm1.const_mul _), lintegral_const_mul _ mm1,
      lintegral_const_mul _ mm4]
    refine (add_le_add (mul_le_mul' le_rfl hE) (mul_le_mul' le_rfl hH)).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hbadT : μ.real (goodT234 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4)ᶜ ≤
      1 / 50000 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 + ΔKb ^ 2 / Δmax ^ 2 +
        ΔXb ^ 2 / ΔXmax ^ 2 +
      (1 / 50000 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 + dQb ^ 2 / εQ ^ 2 +
        5 / (mA n : ℝ) / εD ^ 2 + xiB n εD π₀ ζ₃ dQb / Dmax ^ 2) + ξ / D4 ^ 2 := by
    linarith
  have hcovH : ∀ t ∈ goodT234 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4,
      (gOutH bh t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2) ^ 2 ≤ errH t := by
    intro t hg
    have h23 : t ∈ goodT23 (Gwin n) Δmax ΔXmax εD εQ Dmax := hg.1
    have hc := hcov t h23
    simp only [herrH]
    unfold dOut4
    rw [Set.indicator_of_mem hg]
    have s1 := sq_add_le' hη₄ (gOutB t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2)
      (gOutH bh t.1 t.2.1 t.2.2 - gOutB t.1 t.2.1 t.2.2)
    have e3 : gOutH bh t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2 =
        (gOutB t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2) +
          (gOutH bh t.1 t.2.1 t.2.2 - gOutB t.1 t.2.1 t.2.2) := by ring
    have hp : (0 : ℝ) ≤ 1 + η₄ := by positivity
    have s3 := mul_le_mul_of_nonneg_left hc hp
    rw [e3]
    linarith
  rw [haEH, haE, haH] at hEH
  rw [hc₀] at hcc
  rw [haE] at haE0
  exact ⟨errH, c, e, merrH, herr0H, hcovH, hEH, hbadT, hV, hcc, he0, heR, haE0⟩

/-- **A program with another centre succeeds**, formula with free parameters. For every
`n ≥ 4096` and every measurable centre `bh` with `E[1_good·|bh − bMF|²] ≤ (m/n)·ξ`:
`Pr_{W, A, F}(|gOutH bh − B| ≤ sd/2) ≥ 1 − pFail5`. -/
theorem displace150_formula (hn : 4096 ≤ n)
    {Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb εD εQ π₀ Dmax ρhi yhi ζ₃ η₃ dQb : ℝ}
    (hP : POK2 (6662 / 10000) (6969 / 10000) Δmax ΔXmax r₁ r₂ w g)
    {η₄ : ℝ} (hη₄ : 0 < η₄)
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
    1 - pFail5 n Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb εD εQ π₀ Dmax yhi ζ₃ η₃ dQb
        η₄ ξ D4 y4 ≤
      (mlpTriple 2 n).real
        {t | |gOutH bh t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2| ≤
          sdn t.1 t.2.1 t.2.2 / 2} := by
  obtain ⟨errH, c, e, merrH, herr0H, hcovH, hEH, hbadT, hV, hcc, he0, heR, haE0⟩ :=
    frame150 hn hP hη₄ hP3 hζ₃ hη₃ hdQ hQ0 hη hζ hζ₂ hη₁ hθ0 hθ1 hΔKb0 hΔXb0 hΔK hK0 hΔX hX0 hδb hbh hD4 hy4 hy41 hξ0 hξ
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hN : 1 ≤ 2 * n := by omega
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have hy41' : 0 < 1 - y4 := by linarith
  set c₀ : ℝ := 4 / (n : ℝ) * (222757 / 1000000) with hc₀
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  have hc0 : 0 < c := lt_of_lt_of_le hc₀0 hcc
  set aE : ℝ := aE3 n Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ ΔKb ΔXb δb εD π₀ yhi ζ₃ η₃ dQb with haE
  set aH : ℝ := 2 / (n : ℝ) * (2 / (1 - y4)) * ξ with haH
  have haH0 : 0 ≤ aH := by rw [haH]; positivity
  have msd3 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => sdn t.1 t.2.1 t.2.2) := measurable_sdn (mA := mA n) (mF := mF n) hN
  have h := ok_joint (mlpTriple 2 n) (G := goodT234 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4)
    (Z := ∅)
    (d := fun t => gOutH bh t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2)
    (sd := fun t => sdn t.1 t.2.1 t.2.2) (err := errH)
    (fun t => sdn_nonneg' _ _ _) msd3 merrH herr0H (fun t hg _ => hcovH t hg)
    (by simp) hc0 hθ0 hθ1 (by positivity : (0 : ℝ) ≤ (1 + η₄) * aE + (1 + 1 / η₄) * aH)
    (by positivity : (0 : ℝ) ≤ 2 * (4 / (n : ℝ) * e) ^ 2) hbadT hEH hV
  refine le_trans ?_ h
  -- from `c` to `c₀` and from `e` to its bound
  have t1 : 4 * ((1 + η₄) * aE + (1 + 1 / η₄) * aH) / (θ * c) ≤
      4 * ((1 + η₄) * aE + (1 + 1 / η₄) * aH) / (θ * c₀) :=
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
  have e5 : 4 * ((1 + η₄) * aE + (1 + 1 / η₄) * aH) / (θ * c₀) =
      4 * aE / (θ * c₀) + η₄ * (4 * aE / (θ * c₀)) + (1 + 1 / η₄) * (4 * aH / (θ * c₀)) := by
    ring
  unfold pFail5 pFail3
  rw [← haE, ← hc₀, ← haH]
  unfold aE3 at haE
  rw [← haE]
  linarith

end BstLean.Part150

open BstLean.Part150 in
#print axioms frame150
open BstLean.Part150 in
#print axioms displace150_formula
