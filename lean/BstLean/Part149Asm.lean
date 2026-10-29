import BstLean.Part149Pt
import BstLean.Part149Mean
import BstLean.Part149Tonelli
import BstLean.Part145G5

/-!
# Part 149: the error of the stage of the Agent network, integrated over `(W, A, F)`

Do not use `sorry`, `native_decide` or `axiom`.

Role: `delegations/statements/p149-spec.md`, item 4 (the `A`-stage error and its good event).
The pass over `W` is that of Part 141 (centre `cenA W = M₃ b̃`, scalar `tauWA W = τ̃₀`); the
stand-in inputs are `x(γ) = sphPt (cenA W + τ̃₀·γ)`. The stage of `A` uses the EXACT centre
`b̄ = E_γ a₂(x(γ))` (an idealized program) and the constant scalar `tauOut`.

* `gOutA W A F = E_γ' F(A₃ b̄ + tauOut·γ')`: the output (forward passes of `F` only; no forward
  pass of `A` at an input).
* `eK W θ`, `eD W θ`: the two kernel errors of the hidden map of `A`; `goodX G Δmax δmax`: the
  good event of `(W, A₁, A₂)`; `goodT`: the same as an event of `(W, A, F)`.
* `eK_mean`, `eD_le`: the means of the kernel errors.
* `errA_lint`: `E[1_good·(gOutA − gA)²] ≤ (2/n)·EA(…)`, `gA` the exact mean over the stand-in
  inputs of the `W` stage (Part 141).
* `badT_prob`: the probability of the bad event.
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

/-- The two hidden matrices of `A`. -/
def thA {m : ℕ} (A : MlpParam n m n) : HidParam n m := (A.1, A.2.1)

lemma measurable_thA {m : ℕ} : Measurable (thA (n := n) (m := m)) :=
  measurable_fst.prodMk (measurable_fst.comp measurable_snd)

/-- `β² = t|b̃|²`: the variance of a coordinate of the centre `M₃ b̃` of the `W` stage. -/
noncomputable def betaSq (θ : HidParam (2 * n) (mW n)) : ℝ :=
  2 / (mW n : ℝ) * normSq (bA n θ)

/-- `q = β²/(β² + τ̃₀²)`: the cosine of two stand-in pre-inputs. -/
noncomputable def qTh (θ : HidParam (2 * n) (mW n)) : ℝ :=
  betaSq θ / (betaSq θ + tauA n θ ^ 2)

/-- The reference value of the Gram kernel of `a₂`: `(m_A/n)·κ(κ(q))`. -/
noncomputable def aW (W : MlpParam (2 * n) (mW n) n) : ℝ :=
  (mA n : ℝ) / n * kappa (kappa (qTh (W.1, W.2.1)))

/-- The kernel error of the hidden map of `A` at the stand-in inputs of `W`. -/
noncomputable def eK (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)) : ℝ :=
  errKc (aW W) (cenA W) (tauWA W) θ

/-- The diagonal error of the hidden map of `A` at the stand-in inputs of `W`. -/
noncomputable def eD (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)) : ℝ :=
  errDc (cenA W) (tauWA W) θ

/-- **The output of the idealized program**: `E_γ' F(A₃ b̄ + tauOut·γ')`. -/
noncomputable def gOutA {mF : ℕ} (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (F : MlpParam n mF 1) : ℝ :=
  gO (bbar (cenA W) (tauWA W) (thA A)) (tauOut (cenA W) (tauWA W) (thA A)) (A.2.2, F)

/-- The good event of `(W, A₁, A₂)`. -/
def goodX (G : Set (HidParam (2 * n) (mW n))) (Δmax δmax : ℝ) :
    Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n)) :=
  {x | x.1 ∈ goodWAG G ∧ eK x.1 x.2 ≤ ((mA n : ℝ) / n * Δmax) ^ 2 ∧
    eD x.1 x.2 ≤ ((mA n : ℝ) / n * δmax) ^ 2}

/-- The good event as an event of `(W, A, F)`. -/
def goodT (G : Set (HidParam (2 * n) (mW n))) (Δmax δmax : ℝ) :
    Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :=
  {t | (t.1, thA t.2.1) ∈ goodX G Δmax δmax}

/-- `1_good·(gOutA − gA)²`. -/
noncomputable def dOut (G : Set (HidParam (2 * n) (mW n))) (Δmax δmax : ℝ)
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) : ℝ :=
  (goodT G Δmax δmax).indicator
    (fun t => (gOutA t.1 t.2.1 t.2.2 - gA t.1 t.2.1 t.2.2) ^ 2) t

/-- The window hypothesis of the `W` stage: on the good hidden event of `W`, the cosine `q` and
`κ(κ(q))` are in fixed windows. -/
def WinOK (n : ℕ) (G : Set (HidParam (2 * n) (mW n))) (qlo alo ahi : ℝ) : Prop :=
  ∀ θ ∈ goodAG G, 0 < betaSq θ ∧ 0 < tauA n θ ∧ qlo ≤ qTh θ ∧
    alo ≤ kappa (kappa (qTh θ)) ∧ kappa (kappa (qTh θ)) ≤ ahi

/-- The hypotheses on the parameters of the stage of `A`. -/
structure POK (qlo alo ahi Δmax δmax ε₁ ε₂ su r₁ r₂ : ℝ) : Prop where
  hqlo : 0 ≤ qlo
  hqlo1 : qlo ≤ 1
  halo1 : alo ≤ 1
  hΔmax : 0 < Δmax
  hδmax : 0 < δmax
  hA1 : Δmax < alo
  hA2 : ahi + Δmax < 1
  hε₁ : 0 < ε₁
  hε₂ : 0 < ε₂
  hsu : 0 < su
  hsle : su ≤ 1 - ε₁ - (ahi + ε₂) ^ 2 / (alo - Δmax)
  hr₁ : 0 < r₁
  hr₁' : 1 ≤ r₁ ^ 2 * (alo - Δmax)
  hr₂ : 0 < r₂
  hr₂' : 1 ≤ r₂ ^ 2 * (1 - ahi - Δmax)

/-- The constant of the mean squared error of the stage of `A`, in units `2/n`. -/
noncomputable def EA (alo Δmax δmax ε₁ ε₂ su r₁ r₂ η ζ Δb δb : ℝ) : ℝ :=
  (1 + η) * (2 * (1 - alo + δmax + Δmax)) * (Δb / su + Δb ^ 2 / ε₂ ^ 2 + δb ^ 2 / ε₁ ^ 2) +
    (1 + 1 / η) * 2 * (r₁ ^ 2 * Δb ^ 2 + (1 + ζ) * (r₁ + 2 * r₂) ^ 2 * Δb ^ 2 +
      (1 + 1 / ζ) * r₂ ^ 2 * δb ^ 2)

/-! ## Measurability -/

lemma measurable_betaSq : Measurable (betaSq (n := n)) :=
  (measurable_normSq.comp (measurable_bA n)).const_mul _

lemma measurable_qTh : Measurable (qTh (n := n)) :=
  measurable_betaSq.div (measurable_betaSq.add ((measurable_tauA n).pow_const 2))

lemma measurable_thW :
    Measurable (fun W : MlpParam (2 * n) (mW n) n => ((W.1, W.2.1) : HidParam (2 * n) (mW n))) :=
  measurable_fst.prodMk (measurable_fst.comp measurable_snd)

lemma measurable_aW : Measurable (aW (n := n)) :=
  ((continuous_kappa.comp continuous_kappa).measurable.comp
    (measurable_qTh.comp measurable_thW)).const_mul _

lemma measurable_eK :
    Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) => eK x.1 x.2) := by
  have t1 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) => aW x.1) :=
    measurable_aW.comp measurable_fst
  have t2 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) => cenA x.1) :=
    measurable_cenA.comp measurable_fst
  have t3 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) => tauWA x.1) :=
    measurable_tauWA.comp measurable_fst
  have t4 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) =>
      ((aW x.1, cenA x.1, tauWA x.1), x.2)) := (t1.prodMk (t2.prodMk t3)).prodMk measurable_snd
  have t5 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) =>
      errKc (aW x.1) (cenA x.1) (tauWA x.1) x.2) := by
    have h := (measurable_errKc (n := n) (m := mA n)).comp t4
    simp only [Function.comp_def] at h
    exact h
  exact t5

lemma measurable_eD :
    Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) => eD x.1 x.2) := by
  have t2 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) => cenA x.1) :=
    measurable_cenA.comp measurable_fst
  have t3 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) => tauWA x.1) :=
    measurable_tauWA.comp measurable_fst
  have t4 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) =>
      ((cenA x.1, tauWA x.1), x.2)) := (t2.prodMk t3).prodMk measurable_snd
  have t5 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) =>
      errDc (cenA x.1) (tauWA x.1) x.2) := by
    have h := (measurable_errDc (n := n) (m := mA n)).comp t4
    simp only [Function.comp_def] at h
    exact h
  exact t5

lemma goodX_meas {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤ n)
    (Δmax δmax : ℝ) : MeasurableSet (goodX G Δmax δmax) := by
  have h1 : MeasurableSet {x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) |
      x.1 ∈ goodWAG G} := measurable_fst (goodWAG0_meas hG hn)
  have h2 : MeasurableSet {x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) |
      eK x.1 x.2 ≤ ((mA n : ℝ) / n * Δmax) ^ 2} := measurableSet_le measurable_eK measurable_const
  have h3 : MeasurableSet {x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) |
      eD x.1 x.2 ≤ ((mA n : ℝ) / n * δmax) ^ 2} := measurableSet_le measurable_eD measurable_const
  exact h1.inter (h2.inter h3)

lemma measurable_WX :
    Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      (t.1, thA t.2.1)) :=
  measurable_fst.prodMk (measurable_thA.comp (measurable_fst.comp measurable_snd))

lemma goodT_meas {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤ n)
    (Δmax δmax : ℝ) : MeasurableSet (goodT G Δmax δmax) :=
  measurable_WX (goodX_meas hG hn Δmax δmax)

lemma measurable_gO_joint {m mF : ℕ} :
    Measurable (fun x : ((Fin m → ℝ) × ℝ) × (Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1) =>
      gO x.1.1 x.1.2 x.2) := by
  have mF1 : Measurable (fun q : (((Fin m → ℝ) × ℝ) ×
      (Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1)) × (Fin n → ℝ) => q.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have mM : Measurable (fun q : (((Fin m → ℝ) × ℝ) ×
      (Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1)) × (Fin n → ℝ) => q.1.2.1.mulVec q.1.1.1) :=
    measurable_mulVec_joint.comp
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
        (measurable_fst.comp (measurable_fst.comp measurable_fst)))
  have mτ : Measurable (fun q : (((Fin m → ℝ) × ℝ) ×
      (Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1)) × (Fin n → ℝ) => q.1.1.2 • q.2) :=
    (measurable_snd.comp (measurable_fst.comp measurable_fst)).smul measurable_snd
  have h1 : Measurable (fun q : (((Fin m → ℝ) × ℝ) ×
      (Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1)) × (Fin n → ℝ) =>
      evF q.1.2.2 (q.1.2.1.mulVec q.1.1.1 + q.1.1.2 • q.2)) :=
    measurable_evF_comp mF1 (mM.add mτ)
  exact (h1.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable

lemma measurable_gOutA :
    Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      gOutA t.1 t.2.1 t.2.2) := by
  have hX : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ((cenA t.1, tauWA t.1), thA t.2.1)) :=
    ((measurable_cenA.comp measurable_fst).prodMk (measurable_tauWA.comp measurable_fst)).prodMk
      (measurable_thA.comp (measurable_fst.comp measurable_snd))
  have hp : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => (t.2.1.2.2, t.2.2)) :=
    (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  have hb : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => bbar (cenA t.1) (tauWA t.1) (thA t.2.1)) := by
    have h2 := (measurable_bbar (n := n) (m := mA n)).comp hX
    simp only [Function.comp_def] at h2
    exact h2
  have hτ : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => tauOut (cenA t.1) (tauWA t.1) (thA t.2.1)) := by
    have h2 := (measurable_tauOut (n := n) (m := mA n)).comp hX
    simp only [Function.comp_def] at h2
    exact h2
  have h3 := (measurable_gO_joint (n := n) (m := mA n) (mF := mF n)).comp ((hb.prodMk hτ).prodMk hp)
  simp only [Function.comp_def] at h3
  exact h3

lemma measurable_dOut {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤ n)
    (Δmax δmax : ℝ) : Measurable (dOut G Δmax δmax) :=
  ((measurable_gOutA.sub measurable_gA).pow_const 2).indicator (goodT_meas hG hn Δmax δmax)

lemma dOut_nonneg (G : Set (HidParam (2 * n) (mW n))) (Δmax δmax : ℝ)
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :
    0 ≤ dOut G Δmax δmax t := Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

/-! ## The exact mean over the stand-in inputs is `gT` -/

lemma gA_eq_gT (hn : 1 ≤ n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (F : MlpParam n (mF n) 1) :
    gA W A F = gT (stdGauss (Fin n)) (hA (cenA W) (tauWA W) (thA A)) (A.2.2, F) := by
  rw [gA_eq hn]
  rfl

lemma eK_nonneg (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)) : 0 ≤ eK W θ :=
  integral_nonneg fun _ => sq_nonneg _

lemma eD_nonneg (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)) : 0 ≤ eD W θ :=
  integral_nonneg fun _ => sq_nonneg _

/-! ## Integrals of functions of `(W, A₁, A₂)` -/

/-- A function of `(W, A₁, A₂)` integrated over `(W, A, F)`. -/
lemma lint_WX {g : MlpParam (2 * n) (mW n) n × HidParam n (mA n) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
        g (t.1, thA t.2.1) ∂mlpTriple 2 n =
      ∫⁻ W, ∫⁻ θ, g (W, θ) ∂hidGauss n (mA n) ∂mlpGauss (2 * n) (mW n) n := by
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
  have mg : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => g (t.1, thA t.2.1)) := hg.comp measurable_WX
  rw [e0, lintegral_prod _ mg.aemeasurable]
  refine lintegral_congr fun W => ?_
  have mgW : Measurable (fun p : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      g (W, thA p.1)) := mg.comp measurable_prodMk_left
  have h4 := lint_assoc4 (gaussMat (mA n) n (2 / (n : ℝ)))
    (gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) (gaussMat n (mA n) (2 / (mA n : ℝ)))
    (mlpGauss n (mF n) 1) mgW
  have e1 : (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) =
      ((gaussMat (mA n) n (2 / (n : ℝ))).prod ((gaussMat (mA n) (mA n) (2 / (mA n : ℝ))).prod
        (gaussMat n (mA n) (2 / (mA n : ℝ))))).prod (mlpGauss n (mF n) 1) := rfl
  rw [e1, h4]
  refine lintegral_congr fun x => ?_
  simp only [thA, lintegral_const, measure_univ, mul_one]

/-! ## The means of the kernel errors -/

/-- The mean of the diagonal error, at every `W`. -/
lemma eD_le (hn : 1 ≤ n) {δb : ℝ} (hδb : cF2o (mA n) ≤ δb) (W : MlpParam (2 * n) (mW n) n) :
    ∫⁻ θ, ENNReal.ofReal (eD W θ) ∂hidGauss n (mA n) ≤
      ENNReal.ofReal (((mA n : ℝ) / n * δb) ^ 2) := by
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  refine (errD_mean hn hmA (cenA W) (tauWA W)).trans (ENNReal.ofReal_le_ofReal ?_)
  have h0 := (BstLean.Part136.cF2o_pos hmA).le
  have hd : (0 : ℝ) ≤ (mA n : ℝ) / n := by positivity
  exact pow_le_pow_left₀ (mul_nonneg hd h0) (mul_le_mul_of_nonneg_left hδb hd) 2

/-- **The mean of the kernel error on the good event of `W`.** -/
lemma eK_mean (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {qlo alo ahi : ℝ} (hwin : WinOK n G qlo alo ahi) (hqlo : 0 ≤ qlo) {Δb : ℝ}
    (hΔb : cF2o (mA n) + ((1 - qlo ^ 2) / √(n : ℝ) + jCosC n) ≤ Δb) :
    ∫⁻ W, (goodWAG G).indicator
        (fun W => ∫⁻ θ, ENNReal.ofReal (eK W θ) ∂hidGauss n (mA n)) W
        ∂mlpGauss (2 * n) (mW n) n ≤ ENNReal.ofReal (((mA n : ℝ) / n * Δb) ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hd : (0 : ℝ) ≤ (mA n : ℝ) / n := by positivity
  have mIK : Measurable (fun W : MlpParam (2 * n) (mW n) n =>
      ∫⁻ θ, ENNReal.ofReal (eK W θ) ∂hidGauss n (mA n)) :=
    (ENNReal.measurable_ofReal.comp measurable_eK).lintegral_prod_right'
  have mg : Measurable (fun W : MlpParam (2 * n) (mW n) n => (goodWAG G).indicator
      (fun W => ∫⁻ θ, ENNReal.ofReal (eK W θ) ∂hidGauss n (mA n)) W) :=
    mIK.indicator (goodWAG0_meas hG hn1)
  have e0 : mlpGauss (2 * n) (mW n) n = (gaussMat (mW n) (2 * n) (2 / ((2 * n : ℕ) : ℝ))).prod
      ((gaussMat (mW n) (mW n) (2 / (mW n : ℝ))).prod (gaussMat n (mW n) (2 / (mW n : ℝ)))) := rfl
  rw [e0, lint_assoc3 _ _ _ mg]
  have key : ∀ x : HidParam (2 * n) (mW n),
      ∫⁻ M₃, (goodWAG G).indicator
        (fun W => ∫⁻ θ, ENNReal.ofReal (eK W θ) ∂hidGauss n (mA n)) (x.1, x.2, M₃)
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)) ≤ ENNReal.ofReal (((mA n : ℝ) / n * Δb) ^ 2) := by
    intro x
    by_cases hx : x ∈ goodAG G
    · obtain ⟨hβ, hτ, hq1, _, _⟩ := hwin x hx
      have hmem : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((x.1, x.2, M₃) : MlpParam (2 * n) (mW n) n) ∈ goodWAG G := fun M₃ => hx
      simp only [Set.indicator_of_mem (hmem _)]
      set a : ℝ := (mA n : ℝ) / n * kappa (kappa (qTh x)) with ha
      set Ψ : (Fin n → ℝ) → ℝ≥0∞ := fun c =>
        ∫⁻ θ, ENNReal.ofReal (errKc a c (tauA n x) θ) ∂hidGauss n (mA n) with hΨ
      have mΨ : Measurable Ψ := by
        have h0 : Measurable (fun q : (Fin n → ℝ) × HidParam n (mA n) =>
            ((a, q.1, tauA n x), q.2)) :=
          (measurable_const.prodMk (measurable_fst.prodMk measurable_const)).prodMk measurable_snd
        have h1 : Measurable (fun q : (Fin n → ℝ) × HidParam n (mA n) =>
            errKc a q.1 (tauA n x) q.2) := by
          have h2 := (measurable_errKc (n := n) (m := mA n)).comp h0
          simp only [Function.comp_def] at h2
          exact h2
        exact (ENNReal.measurable_ofReal.comp h1).lintegral_prod_right'
      have e1 : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ∫⁻ θ, ENNReal.ofReal (eK ((x.1, x.2, M₃) : MlpParam (2 * n) (mW n) n) θ)
            ∂hidGauss n (mA n) = Ψ (M₃.mulVec (bA n x)) := fun M₃ => rfl
      simp_rw [e1]
      set β : ℝ := Real.sqrt (2 / (mW n : ℝ)) * Real.sqrt (normSq (bA n x)) with hβd
      have hβ2 : β ^ 2 = betaSq x := by
        rw [hβd, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (normSq_nonneg _)]
        rfl
      have hβ0 : 0 < β := by
        have h0 : 0 ≤ β := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        rcases h0.lt_or_eq with h | h
        · exact h
        · rw [← h] at hβ2
          rw [← hβ2] at hβ
          norm_num at hβ
      have e2 : ∫⁻ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ, Ψ (M₃.mulVec (bA n x))
          ∂gaussMat n (mW n) (2 / (mW n : ℝ)) = ∫⁻ ξ, Ψ (β • ξ) ∂stdGauss (Fin n) := by
        rw [← lintegral_map mΨ (measurable_mulVec_right (bA n x)), gaussMat_mulVec,
          lintegral_map mΨ (measurable_const_smul _)]
      rw [e2]
      have hmean := errK_mean (m := mA n) hn1 hmA hβ0 hτ
      rw [hβ2] at hmean
      refine hmean.trans (ENNReal.ofReal_le_ofReal ?_)
      have hq0 : 0 ≤ qTh x := hqlo.trans hq1
      have hqq : (1 - qTh x ^ 2) / √(n : ℝ) ≤ (1 - qlo ^ 2) / √(n : ℝ) := by
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        nlinarith
      have hq1' : qTh x ≤ 1 := by
        unfold qTh
        rw [div_le_one (by positivity)]
        nlinarith [sq_nonneg (tauA n x)]
      have h0 : 0 ≤ cF2o (mA n) + ((1 - qTh x ^ 2) / √(n : ℝ) + jCosC n) := by
        have := (BstLean.Part136.cF2o_pos hmA).le
        have := jCosC_nonneg n
        have : 0 ≤ (1 - qTh x ^ 2) / √(n : ℝ) :=
          div_nonneg (by nlinarith) (Real.sqrt_nonneg _)
        linarith
      exact pow_le_pow_left₀ (mul_nonneg hd h0)
        (mul_le_mul_of_nonneg_left (by linarith) hd) 2
    · have hmem : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((x.1, x.2, M₃) : MlpParam (2 * n) (mW n) n) ∉ goodWAG G := fun M₃ => hx
      simp only [Set.indicator_of_notMem (hmem _)]
      simp
  calc ∫⁻ x, ∫⁻ M₃, (goodWAG G).indicator
        (fun W => ∫⁻ θ, ENNReal.ofReal (eK W θ) ∂hidGauss n (mA n)) (x.1, x.2, M₃)
        ∂gaussMat n (mW n) (2 / (mW n : ℝ))
        ∂((gaussMat (mW n) (2 * n) (2 / ((2 * n : ℕ) : ℝ))).prod
          (gaussMat (mW n) (mW n) (2 / (mW n : ℝ))))
      ≤ ∫⁻ _x, ENNReal.ofReal (((mA n : ℝ) / n * Δb) ^ 2)
        ∂((gaussMat (mW n) (2 * n) (2 / ((2 * n : ℕ) : ℝ))).prod
          (gaussMat (mW n) (mW n) (2 / (mW n : ℝ)))) := lintegral_mono key
    _ = _ := by simp

/-! ## The error of the stage of `A` -/

/-- The constant part of the linearized error bound. -/
noncomputable def K0 (alo Δmax δmax su η Δb : ℝ) : ℝ :=
  (1 + η) * (2 * (1 - alo + δmax + Δmax)) / su * (Δb / 2)

/-- The coefficient of `Δ²` in the linearized error bound. -/
noncomputable def K1 (alo Δmax δmax ε₂ su r₁ r₂ η ζ Δb : ℝ) : ℝ :=
  (1 + η) * (2 * (1 - alo + δmax + Δmax)) / su / (2 * Δb) +
    (1 + η) * (2 * (1 - alo + δmax + Δmax)) / ε₂ ^ 2 +
    (1 + 1 / η) * 2 * (r₁ ^ 2 + (1 + ζ) * (r₁ + 2 * r₂) ^ 2)

/-- The coefficient of `δ²` in the linearized error bound. -/
noncomputable def K3 (alo Δmax δmax ε₁ r₂ η ζ : ℝ) : ℝ :=
  (1 + η) * (2 * (1 - alo + δmax + Δmax)) / ε₁ ^ 2 + (1 + 1 / η) * 2 * ((1 + 1 / ζ) * r₂ ^ 2)

lemma EA_eq (alo Δmax δmax ε₁ ε₂ su r₁ r₂ η ζ : ℝ) {Δb : ℝ} (hΔb : Δb ≠ 0) (δb : ℝ) :
    EA alo Δmax δmax ε₁ ε₂ su r₁ r₂ η ζ Δb δb =
      K0 alo Δmax δmax su η Δb + K1 alo Δmax δmax ε₂ su r₁ r₂ η ζ Δb * Δb ^ 2 +
        K3 alo Δmax δmax ε₁ r₂ η ζ * δb ^ 2 := by
  unfold EA K0 K1 K3
  field_simp
  ring

/-- The linearization of the bound of `stagePt`. -/
lemma stage_lin {alo Δmax δmax ε₁ ε₂ su r₁ r₂ η ζ Δb Δ δ : ℝ}
    (hv₀0 : 0 ≤ 1 - alo + δmax + Δmax) (hsu : 0 < su) (hη : 0 < η) (hζ : 0 < ζ)
    (hΔb0 : 0 < Δb) :
    (1 + η) * (2 * (Δ / su + Δ ^ 2 / ε₂ ^ 2 + δ ^ 2 / ε₁ ^ 2) * (1 - alo + δmax + Δmax)) +
        (1 + 1 / η) * (2 * (r₁ ^ 2 * Δ ^ 2 + (r₁ * Δ + r₂ * (δ + 2 * Δ)) ^ 2)) ≤
      K0 alo Δmax δmax su η Δb + K1 alo Δmax δmax ε₂ su r₁ r₂ η ζ Δb * Δ ^ 2 +
        K3 alo Δmax δmax ε₁ r₂ η ζ * δ ^ 2 := by
  unfold K0 K1 K3
  set A0 : ℝ := (1 + η) * (2 * (1 - alo + δmax + Δmax)) with hA0
  set B0 : ℝ := (1 + 1 / η) * 2 with hB0
  have hA00 : 0 ≤ A0 := by rw [hA0]; positivity
  have hB00 : 0 ≤ B0 := by rw [hB0]; positivity
  have h1 : Δ ≤ Δb / 2 + Δ ^ 2 / (2 * Δb) := by
    have e1 : Δb / 2 + Δ ^ 2 / (2 * Δb) - Δ = (Δ - Δb) ^ 2 / (2 * Δb) := by
      field_simp
      ring
    have : 0 ≤ (Δ - Δb) ^ 2 / (2 * Δb) := by positivity
    linarith
  have h2 : (r₁ * Δ + r₂ * (δ + 2 * Δ)) ^ 2 ≤
      (1 + ζ) * (r₁ + 2 * r₂) ^ 2 * Δ ^ 2 + (1 + 1 / ζ) * r₂ ^ 2 * δ ^ 2 := by
    have h3 := BstLean.Part133.L2le.sq_add_le (x := (r₁ + 2 * r₂) * Δ) (y := r₂ * δ)
      (a := 1) (b := ζ) one_pos hζ
    have e3 : (r₁ * Δ + r₂ * (δ + 2 * Δ)) = (r₁ + 2 * r₂) * Δ + r₂ * δ := by ring
    rw [e3]
    calc ((r₁ + 2 * r₂) * Δ + r₂ * δ) ^ 2
        ≤ (1 + ζ / 1) * ((r₁ + 2 * r₂) * Δ) ^ 2 + (1 + 1 / ζ) * (r₂ * δ) ^ 2 := h3
      _ = _ := by ring
  have t1 : A0 * (Δ / su) ≤ A0 / su * (Δb / 2) + A0 / su / (2 * Δb) * Δ ^ 2 := by
    have h4 := mul_le_mul_of_nonneg_left h1 (div_nonneg hA00 hsu.le)
    have e4 : A0 * (Δ / su) = A0 / su * Δ := by ring
    have e5 : A0 / su * (Δb / 2 + Δ ^ 2 / (2 * Δb)) =
        A0 / su * (Δb / 2) + A0 / su / (2 * Δb) * Δ ^ 2 := by ring
    rw [e4, ← e5]
    exact h4
  have t2 := mul_le_mul_of_nonneg_left h2 hB00
  have eL : (1 + η) * (2 * (Δ / su + Δ ^ 2 / ε₂ ^ 2 + δ ^ 2 / ε₁ ^ 2) *
      (1 - alo + δmax + Δmax)) +
      (1 + 1 / η) * (2 * (r₁ ^ 2 * Δ ^ 2 + (r₁ * Δ + r₂ * (δ + 2 * Δ)) ^ 2)) =
      A0 * (Δ / su) + A0 / ε₂ ^ 2 * Δ ^ 2 + A0 / ε₁ ^ 2 * δ ^ 2 + B0 * r₁ ^ 2 * Δ ^ 2 +
        B0 * (r₁ * Δ + r₂ * (δ + 2 * Δ)) ^ 2 := by
    rw [hA0, hB0]
    ring
  have eR2 : A0 / su * (Δb / 2) + (A0 / su / (2 * Δb) + A0 / ε₂ ^ 2 +
        B0 * (r₁ ^ 2 + (1 + ζ) * (r₁ + 2 * r₂) ^ 2)) * Δ ^ 2 +
        (A0 / ε₁ ^ 2 + B0 * ((1 + 1 / ζ) * r₂ ^ 2)) * δ ^ 2 =
      (A0 / su * (Δb / 2) + A0 / su / (2 * Δb) * Δ ^ 2) + A0 / ε₂ ^ 2 * Δ ^ 2 +
        A0 / ε₁ ^ 2 * δ ^ 2 + B0 * r₁ ^ 2 * Δ ^ 2 +
        B0 * ((1 + ζ) * (r₁ + 2 * r₂) ^ 2 * Δ ^ 2 + (1 + 1 / ζ) * r₂ ^ 2 * δ ^ 2) := by ring
  rw [eL, eR2]
  linarith [t1, t2]

/-- The linearized error bound as a function of the two kernel errors. -/
noncomputable def linB (n : ℕ) (k₀ k₁ k₃ : ℝ) (W : MlpParam (2 * n) (mW n) n)
    (θ : HidParam n (mA n)) : ℝ :=
  2 / (n : ℝ) * (k₀ + k₁ * (eK W θ / ((mA n : ℝ) / n) ^ 2) + k₃ * (eD W θ / ((mA n : ℝ) / n) ^ 2))

/-- The stage of `A` at fixed `(W, A₁, A₂)`, integrated over `(A₃, F)`. -/
lemma errA_key (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))}
    {qlo alo ahi Δmax δmax ε₁ ε₂ su r₁ r₂ : ℝ} (hwin : WinOK n G qlo alo ahi)
    (hP : POK qlo alo ahi Δmax δmax ε₁ ε₂ su r₁ r₂) {η ζ : ℝ} (hη : 0 < η) (hζ : 0 < ζ)
    {Δb : ℝ} (hΔb0 : 0 < Δb) (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)) :
    ∫⁻ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        ENNReal.ofReal (dOut G Δmax δmax (W, (θ.1, θ.2, y.1), y.2))
        ∂((gaussMat n (mA n) (2 / (mA n : ℝ))).prod (mlpGauss n (mF n) 1)) ≤
      (goodWAG G).indicator
        (fun _ => ENNReal.ofReal (linB n (K0 alo Δmax δmax su η Δb)
          (K1 alo Δmax δmax ε₂ su r₁ r₂ η ζ Δb) (K3 alo Δmax δmax ε₁ r₂ η ζ) W θ)) W := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := BstLean.Part132.mF_ge hn; omega
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  have hd0 : (0 : ℝ) < (mA n : ℝ) / n := by positivity
  have hv₀0 : 0 ≤ 1 - alo + δmax + Δmax := by
    have := hP.halo1; have := hP.hΔmax; have := hP.hδmax
    linarith
  by_cases hx : (W, θ) ∈ goodX G Δmax δmax
  · obtain ⟨hW, hK, hD⟩ := hx
    have hx' : (W, θ) ∈ goodX G Δmax δmax := ⟨hW, hK, hD⟩
    rw [Set.indicator_of_mem hW]
    have hmem : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        ((W, (θ.1, θ.2, y.1), y.2) : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) ∈ goodT G Δmax δmax := fun y => hx'
    have e : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        dOut G Δmax δmax (W, (θ.1, θ.2, y.1), y.2) =
          (gT (stdGauss (Fin n)) (hA (cenA W) (tauWA W) θ) y -
            gO (bbar (cenA W) (tauWA W) θ) (tauOut (cenA W) (tauWA W) θ) y) ^ 2 := by
      intro y
      unfold dOut
      rw [Set.indicator_of_mem (hmem y)]
      simp only []
      rw [gA_eq_gT hn1]
      show (gO (bbar (cenA W) (tauWA W) θ) (tauOut (cenA W) (tauWA W) θ) y -
        gT (stdGauss (Fin n)) (hA (cenA W) (tauWA W) θ) y) ^ 2 = _
      ring
    simp_rw [e]
    obtain ⟨_, _, _, hal, hah⟩ := hwin (W.1, W.2.1) hW
    have hK0 := eK_nonneg W θ
    have hD0 := eD_nonneg W θ
    have hΔ0 : 0 ≤ √(eK W θ) / ((mA n : ℝ) / n) := div_nonneg (Real.sqrt_nonneg _) hd0.le
    have hδ0 : 0 ≤ √(eD W θ) / ((mA n : ℝ) / n) := div_nonneg (Real.sqrt_nonneg _) hd0.le
    have edΔ : (mA n : ℝ) / n * (√(eK W θ) / ((mA n : ℝ) / n)) = √(eK W θ) := by
      field_simp
    have edδ : (mA n : ℝ) / n * (√(eD W θ) / ((mA n : ℝ) / n)) = √(eD W θ) := by
      field_simp
    have hΔle : √(eK W θ) / ((mA n : ℝ) / n) ≤ Δmax := by
      rw [div_le_iff₀ hd0, mul_comm]
      exact Real.sqrt_le_iff.mpr ⟨mul_nonneg hd0.le hP.hΔmax.le, hK⟩
    have hδle : √(eD W θ) / ((mA n : ℝ) / n) ≤ δmax := by
      rw [div_le_iff₀ hd0, mul_comm]
      exact Real.sqrt_le_iff.mpr ⟨mul_nonneg hd0.le hP.hδmax.le, hD⟩
    have hK' : errKc ((mA n : ℝ) / n * kappa (kappa (qTh (W.1, W.2.1)))) (cenA W) (tauWA W) θ ≤
        ((mA n : ℝ) / n * (√(eK W θ) / ((mA n : ℝ) / n))) ^ 2 := by
      rw [edΔ, Real.sq_sqrt hK0]
      exact le_rfl
    have hD' : errDc (cenA W) (tauWA W) θ ≤
        ((mA n : ℝ) / n * (√(eD W θ) / ((mA n : ℝ) / n))) ^ 2 := by
      rw [edδ, Real.sq_sqrt hD0]
      exact le_rfl
    have hpt := stagePt (mF := mF n) hn1 hmA hmF (cenA W) (tauWA W) θ hal hah hP.hΔmax.le
      hP.hδmax.le hP.hA1 hP.hA2 hP.hε₁ hP.hε₂ hP.hsu hP.hsle hP.hr₁ hP.hr₁' hP.hr₂ hP.hr₂' hη
      hΔ0 hΔle hδ0 hδle hK' hD'
    refine hpt.trans (ENNReal.ofReal_le_ofReal ?_)
    unfold linB
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hlin := stage_lin (alo := alo) (Δmax := Δmax) (δmax := δmax) (ε₁ := ε₁) (ε₂ := ε₂)
      (r₁ := r₁) (r₂ := r₂) (Δ := √(eK W θ) / ((mA n : ℝ) / n))
      (δ := √(eD W θ) / ((mA n : ℝ) / n)) hv₀0 hP.hsu hη hζ hΔb0
    have e1 : eK W θ / ((mA n : ℝ) / n) ^ 2 = (√(eK W θ) / ((mA n : ℝ) / n)) ^ 2 := by
      rw [div_pow (√(eK W θ)), Real.sq_sqrt hK0]
    have e2 : eD W θ / ((mA n : ℝ) / n) ^ 2 = (√(eD W θ) / ((mA n : ℝ) / n)) ^ 2 := by
      rw [div_pow (√(eD W θ)), Real.sq_sqrt hD0]
    rw [e1, e2]
    exact hlin
  · have hmem : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        ((W, (θ.1, θ.2, y.1), y.2) : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) ∉ goodT G Δmax δmax := fun y => hx
    have e : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        dOut G Δmax δmax (W, (θ.1, θ.2, y.1), y.2) = 0 := fun y => by
      unfold dOut
      rw [Set.indicator_of_notMem (hmem y)]
    simp_rw [e]
    simp

/-- The stage of `A` at fixed `W`, integrated over `(A, F)`. -/
lemma errA_inner (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {Δmax δmax k₀ k₁ k₃ : ℝ} (hk₀ : 0 ≤ k₀) (hk₁ : 0 ≤ k₁) (hk₃ : 0 ≤ k₃)
    (hkey : ∀ (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)),
      ∫⁻ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        ENNReal.ofReal (dOut G Δmax δmax (W, (θ.1, θ.2, y.1), y.2))
        ∂((gaussMat n (mA n) (2 / (mA n : ℝ))).prod (mlpGauss n (mF n) 1)) ≤
      (goodWAG G).indicator (fun _ => ENNReal.ofReal (linB n k₀ k₁ k₃ W θ)) W)
    {δb : ℝ} (hδb : cF2o (mA n) ≤ δb) (W : MlpParam (2 * n) (mW n) n) :
    ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1, ENNReal.ofReal (dOut G Δmax δmax (W, p))
        ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) ≤
      ENNReal.ofReal (2 / (n : ℝ) * k₀) +
        ENNReal.ofReal (2 / (n : ℝ) * (k₁ / ((mA n : ℝ) / n) ^ 2)) * (goodWAG G).indicator
          (fun W => ∫⁻ θ, ENNReal.ofReal (eK W θ) ∂hidGauss n (mA n)) W +
        ENNReal.ofReal (2 / (n : ℝ) * (k₃ / ((mA n : ℝ) / n) ^ 2)) *
          ENNReal.ofReal (((mA n : ℝ) / n * δb) ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  have hd0 : (0 : ℝ) < (mA n : ℝ) / n := by positivity
  have mOD : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ENNReal.ofReal (dOut G Δmax δmax t)) :=
    ENNReal.measurable_ofReal.comp (measurable_dOut hG hn1 Δmax δmax)
  have mgW : Measurable (fun p : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      ENNReal.ofReal (dOut G Δmax δmax (W, p))) := mOD.comp measurable_prodMk_left
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
    have mK : Measurable (fun θ : HidParam n (mA n) => ENNReal.ofReal (eK W θ)) :=
      ENNReal.measurable_ofReal.comp mK0
    have mDD : Measurable (fun θ : HidParam n (mA n) => ENNReal.ofReal (eD W θ)) :=
      ENNReal.measurable_ofReal.comp mD0
    have e3 : ∀ θ : HidParam n (mA n), ENNReal.ofReal (linB n k₀ k₁ k₃ W θ) =
        ENNReal.ofReal (2 / (n : ℝ) * k₀) +
          ENNReal.ofReal (2 / (n : ℝ) * (k₁ / ((mA n : ℝ) / n) ^ 2)) * ENNReal.ofReal (eK W θ) +
          ENNReal.ofReal (2 / (n : ℝ) * (k₃ / ((mA n : ℝ) / n) ^ 2)) *
            ENNReal.ofReal (eD W θ) := by
      intro θ
      have := eK_nonneg W θ
      have := eD_nonneg W θ
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      unfold linB
      ring
    simp_rw [e3]
    rw [lintegral_add_right _ (mDD.const_mul _), lintegral_add_right _ (mK.const_mul _),
      lintegral_const_mul _ mK, lintegral_const_mul _ mDD, lintegral_const, measure_univ,
      mul_one]
    exact add_le_add le_rfl (mul_le_mul' le_rfl (eD_le hn1 hδb W))
  · simp only [Set.indicator_of_notMem hW]
    simp

/-- **The mean squared error of the stage of `A` on the good event**:
`E_{W, A, F}[1_good·(gOutA − gA)²] ≤ (2/n)·EA`. -/
theorem errA_lint (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {qlo alo ahi Δmax δmax ε₁ ε₂ su r₁ r₂ : ℝ} (hwin : WinOK n G qlo alo ahi)
    (hP : POK qlo alo ahi Δmax δmax ε₁ ε₂ su r₁ r₂) {η ζ : ℝ} (hη : 0 < η) (hζ : 0 < ζ)
    {Δb δb : ℝ} (hΔb : cF2o (mA n) + ((1 - qlo ^ 2) / √(n : ℝ) + jCosC n) ≤ Δb)
    (hδb : cF2o (mA n) ≤ δb) :
    ∫⁻ t, ENNReal.ofReal (dOut G Δmax δmax t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (2 / (n : ℝ) * EA alo Δmax δmax ε₁ ε₂ su r₁ r₂ η ζ Δb δb) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  have hd0 : (0 : ℝ) < (mA n : ℝ) / n := by positivity
  have hcF := BstLean.Part136.cF2o_pos hmA
  have hΔb0 : 0 < Δb := by
    have h1 := jCosC_nonneg n
    have h2 : 0 ≤ (1 - qlo ^ 2) / √(n : ℝ) :=
      div_nonneg (by nlinarith [hP.hqlo, hP.hqlo1]) (Real.sqrt_nonneg _)
    linarith
  have hv₀0 : 0 ≤ 1 - alo + δmax + Δmax := by
    have := hP.halo1; have := hP.hΔmax; have := hP.hδmax
    linarith
  have hsu := hP.hsu
  have hε₁ := hP.hε₁
  have hε₂ := hP.hε₂
  have hk₀0 : 0 ≤ K0 alo Δmax δmax su η Δb := by unfold K0; positivity
  have hk₁0 : 0 ≤ K1 alo Δmax δmax ε₂ su r₁ r₂ η ζ Δb := by unfold K1; positivity
  have hk₃0 : 0 ≤ K3 alo Δmax δmax ε₁ r₂ η ζ := by unfold K3; positivity
  have inner := errA_inner hn hG hk₀0 hk₁0 hk₃0
    (fun W θ => errA_key hn hwin hP hη hζ hΔb0 W θ) hδb
  have mOD : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ENNReal.ofReal (dOut G Δmax δmax t)) :=
    ENNReal.measurable_ofReal.comp (measurable_dOut hG hn1 Δmax δmax)
  have mIK : Measurable (fun W : MlpParam (2 * n) (mW n) n =>
      ∫⁻ θ, ENNReal.ofReal (eK W θ) ∂hidGauss n (mA n)) :=
    (ENNReal.measurable_ofReal.comp measurable_eK).lintegral_prod_right'
  have mInd : Measurable (fun W : MlpParam (2 * n) (mW n) n => (goodWAG G).indicator
      (fun W => ∫⁻ θ, ENNReal.ofReal (eK W θ) ∂hidGauss n (mA n)) W) :=
    mIK.indicator (goodWAG0_meas hG hn1)
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
  rw [e0, lintegral_prod _ mOD.aemeasurable]
  refine (lintegral_mono inner).trans ?_
  rw [lintegral_add_right _ measurable_const, lintegral_add_left measurable_const,
    lintegral_const_mul _ mInd, lintegral_const, lintegral_const, measure_univ, mul_one, mul_one]
  have hKm := eK_mean hn hG hwin hP.hqlo hΔb
  refine (add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hKm)) le_rfl).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [EA_eq _ _ _ _ _ _ _ _ _ _ hΔb0.ne']
  field_simp

/-! ## The probability of the bad event -/

/-- **The bad event of the stage of `A`.** -/
theorem badT_prob (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {qlo alo ahi : ℝ} (hwin : WinOK n G qlo alo ahi) (hqlo : 0 ≤ qlo) (hqlo1 : qlo ≤ 1) {Δmax δmax : ℝ}
    (hΔmax : 0 < Δmax) (hδmax : 0 < δmax) {Δb δb : ℝ}
    (hΔb : cF2o (mA n) + ((1 - qlo ^ 2) / √(n : ℝ) + jCosC n) ≤ Δb)
    (hδb : cF2o (mA n) ≤ δb) {p : ℝ} (h1 : (hidGauss (2 * n) (mW n)).real Gᶜ ≤ p) :
    (mlpTriple 2 n).real (goodT G Δmax δmax)ᶜ ≤
      p + 68000000 / (qA n : ℝ) ^ 2 + Δb ^ 2 / Δmax ^ 2 + δb ^ 2 / δmax ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  set d : ℝ := (mA n : ℝ) / n with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have mGW := goodWAG0_meas hG hn1
  set fK : MlpParam (2 * n) (mW n) n × HidParam n (mA n) → ℝ≥0∞ := fun x =>
    (goodWAG G).indicator (fun _ => ENNReal.ofReal (eK x.1 x.2)) x.1 with hfK
  set fD : MlpParam (2 * n) (mW n) n × HidParam n (mA n) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (eD x.1 x.2) with hfD
  have mfK : Measurable fK := by
    have e : fK = ({x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) |
        x.1 ∈ goodWAG G}).indicator (fun x => ENNReal.ofReal (eK x.1 x.2)) := by
      funext x
      by_cases hx : x.1 ∈ goodWAG G
      · simp [hfK, Set.indicator_of_mem, hx]
      · simp [hfK, Set.indicator_of_notMem, hx]
    rw [e]
    exact (ENNReal.measurable_ofReal.comp measurable_eK).indicator (measurable_fst mGW)
  have mfD : Measurable fD := ENNReal.measurable_ofReal.comp measurable_eD
  set μ := mlpTriple 2 n with hμ
  -- Markov for the two kernel errors
  have iK : ∫⁻ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      fK (t.1, thA t.2.1) ∂μ ≤ ENNReal.ofReal ((d * Δb) ^ 2) := by
    rw [hμ, lint_WX mfK]
    have e : ∀ W : MlpParam (2 * n) (mW n) n, ∫⁻ θ, fK (W, θ) ∂hidGauss n (mA n) =
        (goodWAG G).indicator
          (fun W => ∫⁻ θ, ENNReal.ofReal (eK W θ) ∂hidGauss n (mA n)) W := by
      intro W
      by_cases hW : W ∈ goodWAG G
      · simp [hfK, Set.indicator_of_mem, hW]
      · simp [hfK, Set.indicator_of_notMem, hW]
    simp_rw [e]
    exact eK_mean hn hG hwin hqlo hΔb
  have iD : ∫⁻ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      fD (t.1, thA t.2.1) ∂μ ≤ ENNReal.ofReal ((d * δb) ^ 2) := by
    rw [hμ, lint_WX mfD]
    calc ∫⁻ W, ∫⁻ θ, fD (W, θ) ∂hidGauss n (mA n) ∂mlpGauss (2 * n) (mW n) n
        ≤ ∫⁻ _W, ENNReal.ofReal ((d * δb) ^ 2) ∂mlpGauss (2 * n) (mW n) n :=
          lintegral_mono fun W => eD_le hn1 hδb W
      _ = _ := by simp
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
  have mD' : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => fD (t.1, thA t.2.1)) := mfD.comp measurable_WX
  have hcF := BstLean.Part136.cF2o_pos hmA
  have hδb0 : 0 ≤ δb := (hcF.trans_le hδb).le
  have hΔb0 : 0 ≤ Δb := by
    have h1 := jCosC_nonneg n
    have h2 : 0 ≤ (1 - qlo ^ 2) / √(n : ℝ) :=
      div_nonneg (by nlinarith) (Real.sqrt_nonneg _)
    linarith
  have pK := markov mK' hΔmax hΔb0 iK
  have pD := markov mD' hδmax hδb0 iD
  have hbad := badAG0_prob_gen hn hG h1
  have hsub : (goodT G Δmax δmax)ᶜ ⊆
      {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
        t.1 ∉ goodWAG G} ∪
      ({t | ENNReal.ofReal ((d * Δmax) ^ 2) < fK (t.1, thA t.2.1)} ∪
        {t | ENNReal.ofReal ((d * δmax) ^ 2) < fD (t.1, thA t.2.1)}) := by
    intro t ht
    by_cases hW : t.1 ∈ goodWAG G
    swap
    · exact Or.inl hW
    refine Or.inr ?_
    by_cases hK : eK t.1 (thA t.2.1) ≤ (d * Δmax) ^ 2
    · refine Or.inr ?_
      have hD : ¬ eD t.1 (thA t.2.1) ≤ (d * δmax) ^ 2 := fun hD => ht ⟨hW, hK, hD⟩
      push Not at hD
      change ENNReal.ofReal ((d * δmax) ^ 2) < ENNReal.ofReal (eD t.1 (thA t.2.1))
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (sq_nonneg _) hD)).mpr hD
    · refine Or.inl ?_
      push Not at hK
      change ENNReal.ofReal ((d * Δmax) ^ 2) <
        (goodWAG G).indicator (fun _ => ENNReal.ofReal (eK t.1 (thA t.2.1))) t.1
      rw [Set.indicator_of_mem hW]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (sq_nonneg _) hK)).mpr hK
  calc μ.real (goodT G Δmax δmax)ᶜ
      ≤ μ.real ({t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
        t.1 ∉ goodWAG G} ∪
        ({t | ENNReal.ofReal ((d * Δmax) ^ 2) < fK (t.1, thA t.2.1)} ∪
          {t | ENNReal.ofReal ((d * δmax) ^ 2) < fD (t.1, thA t.2.1)})) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
        t.1 ∉ goodWAG G} +
        (μ.real {t | ENNReal.ofReal ((d * Δmax) ^ 2) < fK (t.1, thA t.2.1)} +
          μ.real {t | ENNReal.ofReal ((d * δmax) ^ 2) < fD (t.1, thA t.2.1)}) :=
        (measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le _ _))
    _ ≤ _ := by linarith

end BstLean.Part149

open BstLean.Part149 in
#print axioms eK_mean
open BstLean.Part149 in
#print axioms errA_lint
open BstLean.Part149 in
#print axioms badT_prob
