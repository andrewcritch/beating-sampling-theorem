import BstLean.Part149Asm2
import BstLean.Part149OutB
import BstLean.Part149Centre
import BstLean.Part149Layer1
import BstLean.Part149CentreDet

/-!
# Part 149, item 5: the program with the mean-field centre of `A` (computed in one pass)

Do not use `sorry`, `native_decide` or `axiom`.

Role: `delegations/statements/p149-spec.md`, item 5 (`onePassA149`, the mathematical part). The
centre of the stage of `A` is the MEAN-FIELD centre `bMF = ψ_s(A₂ b1)` of `Part149CDefs` (one
product with `A₂`; the exact first-layer mean `b1`, the number `N2` and the function `ψ_s` are
oracles). The output is `gOutB W A F = E_γ' F(A₃ bMF + τ·γ')`, `τ = tauOutOf n bMF`.

* `gOutB`, `eCW`, `qkW`, `d1W`; `goodX1`, `goodX3`, `goodT3`, `goodT23`; `dOut3`.
* `xiB`: the bound of `E[1_good·|bMF − b̄|²]/(m/n)`; `centre_mean`.
* `errB_lint`: `E[1_good·(gOutB − gOutA)²] ≤ (2/n)·(2/(1 − yhi))·xiB`.
* `badT3_prob`: the probability of the bad event.
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

/-- The mean-field centre at the stand-in inputs of `W`. -/
noncomputable def bMFW (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n) :
    Fin (mA n) → ℝ :=
  bMF (cenA W) (tauWA W) (thA A)

/-- **The output of the program with the mean-field centre**:
`E_γ' F(A₃ bMF + tauOutOf n bMF·γ')`. -/
noncomputable def gOutB {mF : ℕ} (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (F : MlpParam n mF 1) : ℝ :=
  gO (bMFW W A) (tauOutOf n (bMFW W A)) (A.2.2, F)

/-- The squared distance of the mean-field centre to the exact centre. -/
noncomputable def eCW (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)) : ℝ :=
  eC (cenA W) (tauWA W) θ

/-- The first-layer kernel error against `κ(q)·|a||a'|`. -/
noncomputable def qkW (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)) : ℝ :=
  Qk (kappa (qTh (W.1, W.2.1))) (cenA W) (tauWA W) θ.1

/-- The first-layer diagonal error. -/
noncomputable def d1W (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)) : ℝ :=
  errD1 (cenA W) (tauWA W) θ.1

lemma eCW_nonneg (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)) : 0 ≤ eCW W θ := by
  unfold eCW eC
  exact normSq_nonneg _

lemma qkW_nonneg (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)) : 0 ≤ qkW W θ :=
  integral_nonneg fun _ => sq_nonneg _

lemma d1W_nonneg (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)) : 0 ≤ d1W W θ :=
  integral_nonneg fun _ => sq_nonneg _

/-- The good event of `(W, A₁)` for the first layer. -/
def goodX1 (G : Set (HidParam (2 * n) (mW n))) (εD εQ : ℝ) :
    Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n)) :=
  {x | x.1 ∈ goodWAG G ∧ d1W x.1 x.2 ≤ ((mA n : ℝ) / n * εD) ^ 2 ∧
    qkW x.1 x.2 ≤ ((mA n : ℝ) / n * εQ) ^ 2}

/-- The good event of `(W, A₁, A₂)` for the mean-field centre. -/
def goodX3 (G : Set (HidParam (2 * n) (mW n))) (εD εQ Dmax : ℝ) :
    Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n)) :=
  {x | x ∈ goodX1 G εD εQ ∧ eCW x.1 x.2 ≤ (mA n : ℝ) / n * Dmax ^ 2}

/-- The same as an event of `(W, A, F)`. -/
def goodT3 (G : Set (HidParam (2 * n) (mW n))) (εD εQ Dmax : ℝ) :
    Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :=
  {t | (t.1, thA t.2.1) ∈ goodX3 G εD εQ Dmax}

/-- The good event of the program with the mean-field centre. -/
def goodT23 (G : Set (HidParam (2 * n) (mW n))) (Δmax ΔXmax εD εQ Dmax : ℝ) :
    Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :=
  goodT2 G Δmax ΔXmax ∩ goodT3 G εD εQ Dmax

/-- `1_good·(gOutB − gOutA)²`. -/
noncomputable def dOut3 (G : Set (HidParam (2 * n) (mW n))) (Δmax ΔXmax εD εQ Dmax : ℝ)
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) : ℝ :=
  (goodT23 G Δmax ΔXmax εD εQ Dmax).indicator
    (fun t => (gOutB t.1 t.2.1 t.2.2 - gOutA t.1 t.2.1 t.2.2) ^ 2) t

/-! ## Measurability -/

lemma measurable_cτθ :
    Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) =>
      ((cenA x.1, tauWA x.1), x.2)) :=
  ((measurable_cenA.comp measurable_fst).prodMk (measurable_tauWA.comp measurable_fst)).prodMk
    measurable_snd

lemma measurable_eCW :
    Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) => eCW x.1 x.2) := by
  have h := (measurable_eC (n := n) (m := mA n)).comp measurable_cτθ
  simp only [Function.comp_def] at h
  exact h

lemma measurable_d1W :
    Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) => d1W x.1 x.2) := by
  have t4 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) =>
      ((cenA x.1, tauWA x.1), x.2.1)) :=
    ((measurable_cenA.comp measurable_fst).prodMk (measurable_tauWA.comp measurable_fst)).prodMk
      (measurable_fst.comp measurable_snd)
  have h := (measurable_errD1 (n := n) (m := mA n)).comp t4
  simp only [Function.comp_def] at h
  exact h

lemma measurable_qkW :
    Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) => qkW x.1 x.2) := by
  have t1 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) =>
      kappa (qTh (x.1.1, x.1.2.1))) :=
    continuous_kappa.measurable.comp (measurable_qTh.comp (measurable_thW.comp measurable_fst))
  have t4 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) =>
      ((kappa (qTh (x.1.1, x.1.2.1)), cenA x.1, tauWA x.1), x.2.1)) :=
    (t1.prodMk ((measurable_cenA.comp measurable_fst).prodMk
      (measurable_tauWA.comp measurable_fst))).prodMk (measurable_fst.comp measurable_snd)
  have h := (measurable_Qk (n := n) (m := mA n)).comp t4
  simp only [Function.comp_def] at h
  exact h

lemma goodX1_meas {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤ n)
    (εD εQ : ℝ) : MeasurableSet (goodX1 G εD εQ) := by
  have h1 : MeasurableSet {x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) |
      x.1 ∈ goodWAG G} := measurable_fst (goodWAG0_meas hG hn)
  have h2 : MeasurableSet {x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) |
      d1W x.1 x.2 ≤ ((mA n : ℝ) / n * εD) ^ 2} := measurableSet_le measurable_d1W measurable_const
  have h3 : MeasurableSet {x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) |
      qkW x.1 x.2 ≤ ((mA n : ℝ) / n * εQ) ^ 2} := measurableSet_le measurable_qkW measurable_const
  exact h1.inter (h2.inter h3)

lemma goodX3_meas {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤ n)
    (εD εQ Dmax : ℝ) : MeasurableSet (goodX3 G εD εQ Dmax) :=
  (goodX1_meas hG hn εD εQ).inter (measurableSet_le measurable_eCW measurable_const)

lemma goodT3_meas {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤ n)
    (εD εQ Dmax : ℝ) : MeasurableSet (goodT3 G εD εQ Dmax) :=
  measurable_WX (goodX3_meas hG hn εD εQ Dmax)

lemma goodT23_meas {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤ n)
    (Δmax ΔXmax εD εQ Dmax : ℝ) : MeasurableSet (goodT23 G Δmax ΔXmax εD εQ Dmax) :=
  (goodT2_meas hG hn Δmax ΔXmax).inter (goodT3_meas hG hn εD εQ Dmax)

lemma measurable_tauOutOf {m : ℕ} : Measurable (tauOutOf (m := m) n) := by
  unfold tauOutOf
  exact (measurable_const.max (measurable_const.sub (measurable_normSq.const_mul _))).sqrt

lemma measurable_gOutB :
    Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      gOutB t.1 t.2.1 t.2.2) := by
  have hX : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ((cenA t.1, tauWA t.1), thA t.2.1)) :=
    ((measurable_cenA.comp measurable_fst).prodMk (measurable_tauWA.comp measurable_fst)).prodMk
      (measurable_thA.comp (measurable_fst.comp measurable_snd))
  have hp : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => (t.2.1.2.2, t.2.2)) :=
    (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  have hb : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => bMF (cenA t.1) (tauWA t.1) (thA t.2.1)) := by
    have h2 := (measurable_bMF (n := n) (m := mA n)).comp hX
    simp only [Function.comp_def] at h2
    exact h2
  have hτ : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => tauOutOf n (bMF (cenA t.1) (tauWA t.1) (thA t.2.1))) :=
    measurable_tauOutOf.comp hb
  have h3 := (measurable_gO_joint (n := n) (m := mA n) (mF := mF n)).comp
    ((hb.prodMk hτ).prodMk hp)
  simp only [Function.comp_def] at h3
  exact h3

lemma measurable_dOut3 {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤ n)
    (Δmax ΔXmax εD εQ Dmax : ℝ) : Measurable (dOut3 G Δmax ΔXmax εD εQ Dmax) :=
  ((measurable_gOutB.sub measurable_gOutA).pow_const 2).indicator
    (goodT23_meas hG hn Δmax ΔXmax εD εQ Dmax)

lemma dOut3_nonneg (G : Set (HidParam (2 * n) (mW n))) (Δmax ΔXmax εD εQ Dmax : ℝ)
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :
    0 ≤ dOut3 G Δmax ΔXmax εD εQ Dmax t := Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

/-! ## Means of functions of `(W, A₁)` -/

/-- A function of the first hidden matrix, integrated over both hidden matrices. -/
lemma lint_hid_fst {g : Matrix (Fin (mA n)) (Fin n) ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ θ : HidParam n (mA n), g θ.1 ∂hidGauss n (mA n) =
      ∫⁻ A₁, g A₁ ∂gaussMat (mA n) n (2 / (n : ℝ)) := by
  have e : hidGauss n (mA n) = (gaussMat (mA n) n (2 / (n : ℝ))).prod
      (gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) := rfl
  rw [e, lintegral_prod (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
    Matrix (Fin (mA n)) (Fin (mA n)) ℝ => g θ.1) (hg.comp measurable_fst).aemeasurable]
  simp

/-- The mean of the first-layer kernel error on the good hidden event of `W`. -/
lemma qk_mean (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {alo ahi : ℝ} (hwin : WinOK2 n G alo ahi) {dQb : ℝ}
    (hdQ : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dQ1 n (mA n) q ≤ dQb)
    (hQ0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dQ1 n (mA n) q) :
    ∫⁻ W, (goodWAG G).indicator
        (fun W => ∫⁻ θ, ENNReal.ofReal (qkW W θ) ∂hidGauss n (mA n)) W
        ∂mlpGauss (2 * n) (mW n) n ≤ ENNReal.ofReal (((mA n : ℝ) / n * dQb) ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hd : (0 : ℝ) ≤ (mA n : ℝ) / n := by positivity
  refine W_mean hn1 hG measurable_qkW
    (Φ := fun x c θ => Qk (kappa (qTh x)) c (tauA n x) θ.1)
    (fun W θ => rfl) (fun x => ?_) (fun x hx => (hwin x hx).1) (fun x hx β hβ0 hβ2 => ?_)
  · have h0 : Measurable (fun q : (Fin n → ℝ) × HidParam n (mA n) =>
        ((kappa (qTh x), q.1, tauA n x), q.2.1)) :=
      (measurable_const.prodMk (measurable_fst.prodMk measurable_const)).prodMk
        (measurable_fst.comp measurable_snd)
    have h2 := (measurable_Qk (n := n) (m := mA n)).comp h0
    simp only [Function.comp_def] at h2
    exact h2
  · obtain ⟨_, hτ, hq1, hq2, _, _⟩ := hwin x hx
    have hq1' : 462 / 1000 ≤ β ^ 2 / (β ^ 2 + tauA n x ^ 2) := by rw [hβ2]; exact hq1
    have hq2' : β ^ 2 / (β ^ 2 + tauA n x ^ 2) ≤ 527 / 1000 := by rw [hβ2]; exact hq2
    have hmean := Qk_mean (m := mA n) hn1 hmA hβ0 hτ hq1' hq2'
    rw [hβ2] at hmean
    have mQ : ∀ ξ : Fin n → ℝ, Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
        ENNReal.ofReal (Qk (kappa (qTh x)) (β • ξ) (tauA n x) A₁)) := by
      intro ξ
      have h0 : Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
          ((kappa (qTh x), β • ξ, tauA n x), A₁)) := measurable_const.prodMk measurable_id
      have h2 := (measurable_Qk (n := n) (m := mA n)).comp h0
      simp only [Function.comp_def] at h2
      exact ENNReal.measurable_ofReal.comp h2
    have e : ∀ ξ : Fin n → ℝ,
        ∫⁻ θ : HidParam n (mA n), ENNReal.ofReal (Qk (kappa (qTh x)) (β • ξ) (tauA n x) θ.1)
          ∂hidGauss n (mA n) =
        ∫⁻ A₁, ENNReal.ofReal (Qk (kappa (qTh x)) (β • ξ) (tauA n x) A₁)
          ∂gaussMat (mA n) n (2 / (n : ℝ)) := fun ξ => lint_hid_fst (mQ ξ)
    simp_rw [e]
    refine hmean.trans (ENNReal.ofReal_le_ofReal ?_)
    exact pow_le_pow_left₀ (mul_nonneg hd (hQ0 _ hq1 hq2))
      (mul_le_mul_of_nonneg_left (hdQ _ hq1 hq2) hd) 2

/-- The mean of the first-layer diagonal error. -/
lemma d1_mean (hn : 1 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    (hβ : ∀ x ∈ goodAG G, 0 < betaSq x) :
    ∫⁻ W, (goodWAG G).indicator
        (fun W => ∫⁻ θ, ENNReal.ofReal (d1W W θ) ∂hidGauss n (mA n)) W
        ∂mlpGauss (2 * n) (mW n) n ≤
      ENNReal.ofReal (((mA n : ℝ) / n) ^ 2 * (5 / (mA n : ℝ))) := by
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  refine W_mean hn hG measurable_d1W
    (Φ := fun x c θ => errD1 c (tauA n x) θ.1)
    (fun W θ => rfl) (fun x => ?_) hβ (fun x hx β hβ0 hβ2 => ?_)
  · have h0 : Measurable (fun q : (Fin n → ℝ) × HidParam n (mA n) =>
        ((q.1, tauA n x), q.2.1)) :=
      (measurable_fst.prodMk measurable_const).prodMk (measurable_fst.comp measurable_snd)
    have h2 := (measurable_errD1 (n := n) (m := mA n)).comp h0
    simp only [Function.comp_def] at h2
    exact h2
  · have mQ : ∀ ξ : Fin n → ℝ, Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
        ENNReal.ofReal (errD1 (β • ξ) (tauA n x) A₁)) := by
      intro ξ
      have h0 : Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
          ((β • ξ, tauA n x), A₁)) := measurable_const.prodMk measurable_id
      have h2 := (measurable_errD1 (n := n) (m := mA n)).comp h0
      simp only [Function.comp_def] at h2
      exact ENNReal.measurable_ofReal.comp h2
    have e : ∀ ξ : Fin n → ℝ,
        ∫⁻ θ : HidParam n (mA n), ENNReal.ofReal (errD1 (β • ξ) (tauA n x) θ.1)
          ∂hidGauss n (mA n) =
        ∫⁻ A₁, ENNReal.ofReal (errD1 (β • ξ) (tauA n x) A₁)
          ∂gaussMat (mA n) n (2 / (n : ℝ)) := fun ξ => lint_hid_fst (mQ ξ)
    simp_rw [e]
    calc ∫⁻ ξ, ∫⁻ A₁, ENNReal.ofReal (errD1 (β • ξ) (tauA n x) A₁)
          ∂gaussMat (mA n) n (2 / (n : ℝ)) ∂stdGauss (Fin n)
        ≤ ∫⁻ _ξ, ENNReal.ofReal (((mA n : ℝ) / n) ^ 2 * (5 / (mA n : ℝ))) ∂stdGauss (Fin n) :=
          lintegral_mono fun ξ => errD1_mean hn hmA (β • ξ) (tauA n x)
      _ = _ := by simp

/-! ## The mean of the centre distance -/

/-- The hypotheses on the parameters of the mean-field centre. -/
structure POK3 (ahi Δmax εD εQ π₀ Dmax ρhi yhi : ℝ) : Prop where
  hεD0 : 0 < εD
  hεD1 : εD < 1
  hεQ0 : 0 < εQ
  hcond : 62714 / 100000 * (1 - εD) + εQ ≤ 3 / 4 * (1 - εD)
  hπ0 : 0 < π₀
  hπ1 : π₀ < 1
  hDmax : 0 < Dmax
  hρ0 : 0 ≤ ρhi
  hρ : ahi + Δmax ≤ ρhi ^ 2
  hy : (ρhi + Dmax) ^ 2 ≤ yhi
  hy1 : yhi < 1

/-- The coefficient of the first-layer kernel error in the centre distance. -/
noncomputable def cQ3 (π₀ ζ : ℝ) : ℝ := 4 * Kq * (1 + ζ) / π₀

/-- The coefficient of the first-layer diagonal error in the centre distance. -/
noncomputable def cD3 (εD π₀ ζ : ℝ) : ℝ :=
  1 + Kq * ((1 + 1 / ζ) * εD ^ 2 / π₀ + 8 * π₀ / (1 - π₀) ^ 2)

/-- The bound of `E[1_good·|bMF − b̄|²]/(m/n)`. -/
noncomputable def xiB (n : ℕ) (εD π₀ ζ dQb : ℝ) : ℝ :=
  cQ3 π₀ ζ * dQb ^ 2 + cD3 εD π₀ ζ * (5 / (mA n : ℝ))

lemma Kq_nonneg : (0 : ℝ) ≤ Kq := by unfold Kq; norm_num

/-- The mean over `A₂` of the centre distance, on the good event of `(W, A₁)`. -/
lemma centre_inner (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))}
    {alo ahi : ℝ} (hwin : WinOK2 n G alo ahi) {Δmax εD εQ π₀ Dmax ρhi yhi : ℝ}
    (hP : POK3 ahi Δmax εD εQ π₀ Dmax ρhi yhi) {ζ : ℝ} (hζ : 0 < ζ)
    (W : MlpParam (2 * n) (mW n) n) :
    ∫⁻ θ, (goodX1 G εD εQ).indicator (fun x => ENNReal.ofReal (eCW x.1 x.2)) (W, θ)
        ∂hidGauss n (mA n) ≤
      (goodWAG G).indicator (fun W =>
        ENNReal.ofReal (cQ3 π₀ ζ / ((mA n : ℝ) / n)) *
            ∫⁻ θ, ENNReal.ofReal (qkW W θ) ∂hidGauss n (mA n) +
          ENNReal.ofReal (cD3 εD π₀ ζ / ((mA n : ℝ) / n)) *
            ∫⁻ θ, ENNReal.ofReal (d1W W θ) ∂hidGauss n (mA n)) W := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  have hd0 : (0 : ℝ) < (mA n : ℝ) / n := by positivity
  have hK := Kq_nonneg
  have hπ0 := hP.hπ0
  have hπ1 : 0 < 1 - π₀ := by linarith [hP.hπ1]
  have hcQ : 0 ≤ cQ3 π₀ ζ := by unfold cQ3; positivity
  have hcD : 0 ≤ cD3 εD π₀ ζ := by unfold cD3; positivity
  by_cases hW : W ∈ goodWAG G
  swap
  · have e : ∀ θ : HidParam n (mA n), (goodX1 G εD εQ).indicator
        (fun x => ENNReal.ofReal (eCW x.1 x.2)) (W, θ) = 0 := fun θ =>
      Set.indicator_of_notMem (fun h => hW h.1) _
    simp_rw [e]
    simp
  rw [Set.indicator_of_mem hW]
  obtain ⟨_, _, hq1, hq2, _, _⟩ := hwin (W.1, W.2.1) hW
  have hkq0 : 0 ≤ kappa (qTh (W.1, W.2.1)) :=
    (kappa_mem (by linarith) (by linarith)).1
  have hkq1 : kappa (qTh (W.1, W.2.1)) ≤ 62714 / 100000 :=
    BstLean.Part135.kappa_le_of_le9 (a := 527 / 1000) (by linarith) hq2 (by norm_num)
      (by norm_num)
  -- the integrand as a function of `(A₁, A₂)`
  have mind : Measurable (fun θ : HidParam n (mA n) => (goodX1 G εD εQ).indicator
      (fun x => ENNReal.ofReal (eCW x.1 x.2)) (W, θ)) := by
    have m0 : Measurable (fun θ : HidParam n (mA n) => ENNReal.ofReal (eCW W θ)) := by
      have h := (measurable_eCW (n := n)).comp (measurable_prodMk_left (x := W))
      simp only [Function.comp_def] at h
      exact ENNReal.measurable_ofReal.comp h
    have ms : MeasurableSet {θ : HidParam n (mA n) |
        d1W W θ ≤ ((mA n : ℝ) / n * εD) ^ 2 ∧ qkW W θ ≤ ((mA n : ℝ) / n * εQ) ^ 2} := by
      have h1 : Measurable (fun θ : HidParam n (mA n) => d1W W θ) := by
        have h := (measurable_d1W (n := n)).comp (measurable_prodMk_left (x := W))
        simp only [Function.comp_def] at h
        exact h
      have h2 : Measurable (fun θ : HidParam n (mA n) => qkW W θ) := by
        have h := (measurable_qkW (n := n)).comp (measurable_prodMk_left (x := W))
        simp only [Function.comp_def] at h
        exact h
      exact (measurableSet_le h1 measurable_const).inter (measurableSet_le h2 measurable_const)
    have e : (fun θ : HidParam n (mA n) => (goodX1 G εD εQ).indicator
        (fun x => ENNReal.ofReal (eCW x.1 x.2)) (W, θ)) =
        ({θ : HidParam n (mA n) | d1W W θ ≤ ((mA n : ℝ) / n * εD) ^ 2 ∧
          qkW W θ ≤ ((mA n : ℝ) / n * εQ) ^ 2}).indicator
          (fun θ => ENNReal.ofReal (eCW W θ)) := by
      funext θ
      by_cases hθ : d1W W θ ≤ ((mA n : ℝ) / n * εD) ^ 2 ∧ qkW W θ ≤ ((mA n : ℝ) / n * εQ) ^ 2
      · have h1 : (W, θ) ∈ goodX1 G εD εQ := ⟨hW, hθ.1, hθ.2⟩
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem (by exact hθ)]
      · have h1 : (W, θ) ∉ goodX1 G εD εQ := fun h => hθ ⟨h.2.1, h.2.2⟩
        rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (by exact hθ)]
    rw [e]
    exact m0.indicator ms
  have e0 : hidGauss n (mA n) = (gaussMat (mA n) n (2 / (n : ℝ))).prod
      (gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) := rfl
  -- pointwise in `A₁`
  have key : ∀ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ,
      ∫⁻ A₂, (goodX1 G εD εQ).indicator (fun x => ENNReal.ofReal (eCW x.1 x.2)) (W, (A₁, A₂))
          ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ)) ≤
        ENNReal.ofReal (cQ3 π₀ ζ / ((mA n : ℝ) / n)) *
            ENNReal.ofReal (Qk (kappa (qTh (W.1, W.2.1))) (cenA W) (tauWA W) A₁) +
          ENNReal.ofReal (cD3 εD π₀ ζ / ((mA n : ℝ) / n)) *
            ENNReal.ofReal (errD1 (cenA W) (tauWA W) A₁) := by
    intro A₁
    by_cases hA : errD1 (cenA W) (tauWA W) A₁ ≤ ((mA n : ℝ) / n * εD) ^ 2 ∧
        Qk (kappa (qTh (W.1, W.2.1))) (cenA W) (tauWA W) A₁ ≤ ((mA n : ℝ) / n * εQ) ^ 2
    · have hmem : ∀ A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ,
          ((W, (A₁, A₂)) : MlpParam (2 * n) (mW n) n × HidParam n (mA n)) ∈ goodX1 G εD εQ :=
        fun A₂ => ⟨hW, hA.1, hA.2⟩
      simp only [Set.indicator_of_mem (hmem _)]
      have hcond : kappa (qTh (W.1, W.2.1)) * (1 - εD) + εQ ≤ 3 / 4 * (1 - εD) := by
        have h1 : 0 ≤ 1 - εD := by linarith [hP.hεD1]
        have := mul_le_mul_of_nonneg_right hkq1 h1
        linarith [hP.hcond]
      obtain ⟨hN2, hu, hlin⟩ := centre_det hn1 hmA (cenA W) (tauWA W) A₁ hkq0
        (hkq1.trans (by norm_num)) hP.hεD0.le hP.hεD1 hP.hεQ0.le hcond hπ0 hP.hπ1 hζ hK hA.1 hA.2
      have hc := centreDist_cond hn1 hmA (cenA W) (tauWA W) A₁ hN2 hu
        (plo := (mA n : ℝ) / n * π₀) (by positivity)
      have hQ0 : 0 ≤ Qk (kappa (qTh (W.1, W.2.1))) (cenA W) (tauWA W) A₁ :=
        integral_nonneg fun _ => sq_nonneg _
      have hD0 : 0 ≤ errD1 (cenA W) (tauWA W) A₁ := integral_nonneg fun _ => sq_nonneg _
      refine (hc.trans (ENNReal.ofReal_le_ofReal hlin)).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      unfold cQ3 cD3
      ring
    · have hmem : ∀ A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ,
          ((W, (A₁, A₂)) : MlpParam (2 * n) (mW n) n × HidParam n (mA n)) ∉ goodX1 G εD εQ :=
        fun A₂ h => hA ⟨h.2.1, h.2.2⟩
      simp only [Set.indicator_of_notMem (hmem _)]
      simp
  have mQ : Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
      ENNReal.ofReal (Qk (kappa (qTh (W.1, W.2.1))) (cenA W) (tauWA W) A₁)) := by
    have h0 : Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
        ((kappa (qTh (W.1, W.2.1)), cenA W, tauWA W), A₁)) :=
      measurable_const.prodMk measurable_id
    have h2 := (measurable_Qk (n := n) (m := mA n)).comp h0
    simp only [Function.comp_def] at h2
    exact ENNReal.measurable_ofReal.comp h2
  have mD : Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
      ENNReal.ofReal (errD1 (cenA W) (tauWA W) A₁)) := by
    have h0 : Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
        ((cenA W, tauWA W), A₁)) := measurable_const.prodMk measurable_id
    have h2 := (measurable_errD1 (n := n) (m := mA n)).comp h0
    simp only [Function.comp_def] at h2
    exact ENNReal.measurable_ofReal.comp h2
  have eq1 : ∫⁻ θ : HidParam n (mA n), ENNReal.ofReal (qkW W θ) ∂hidGauss n (mA n) =
      ∫⁻ A₁, ENNReal.ofReal (Qk (kappa (qTh (W.1, W.2.1))) (cenA W) (tauWA W) A₁)
        ∂gaussMat (mA n) n (2 / (n : ℝ)) := lint_hid_fst mQ
  have eq2 : ∫⁻ θ : HidParam n (mA n), ENNReal.ofReal (d1W W θ) ∂hidGauss n (mA n) =
      ∫⁻ A₁, ENNReal.ofReal (errD1 (cenA W) (tauWA W) A₁)
        ∂gaussMat (mA n) n (2 / (n : ℝ)) := lint_hid_fst mD
  rw [eq1, eq2, e0, lintegral_prod _ mind.aemeasurable]
  refine (lintegral_mono key).trans (le_of_eq ?_)
  rw [lintegral_add_right _ (mD.const_mul _), lintegral_const_mul _ mQ, lintegral_const_mul _ mD]

/-- **The mean of the squared distance of the mean-field centre to the exact centre**, on the
good event of `(W, A₁)`: `E[1_good·|bMF − b̄|²] ≤ (m/n)·xiB`. -/
theorem centre_mean (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {alo ahi : ℝ} (hwin : WinOK2 n G alo ahi) {Δmax εD εQ π₀ Dmax ρhi yhi : ℝ}
    (hP : POK3 ahi Δmax εD εQ π₀ Dmax ρhi yhi) {ζ : ℝ} (hζ : 0 < ζ) {dQb : ℝ}
    (hdQ : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dQ1 n (mA n) q ≤ dQb)
    (hQ0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dQ1 n (mA n) q) :
    ∫⁻ W, ∫⁻ θ, (goodX1 G εD εQ).indicator (fun x => ENNReal.ofReal (eCW x.1 x.2)) (W, θ)
        ∂hidGauss n (mA n) ∂mlpGauss (2 * n) (mW n) n ≤
      ENNReal.ofReal ((mA n : ℝ) / n * xiB n εD π₀ ζ dQb) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  have hd0 : (0 : ℝ) < (mA n : ℝ) / n := by positivity
  have hK := Kq_nonneg
  have hπ0 := hP.hπ0
  have hπ1 : 0 < 1 - π₀ := by linarith [hP.hπ1]
  have hcQ : 0 ≤ cQ3 π₀ ζ := by unfold cQ3; positivity
  have hcD : 0 ≤ cD3 εD π₀ ζ := by unfold cD3; positivity
  have mGW := goodWAG0_meas hG hn1
  have mIQ : Measurable (fun W : MlpParam (2 * n) (mW n) n =>
      ∫⁻ θ, ENNReal.ofReal (qkW W θ) ∂hidGauss n (mA n)) :=
    (ENNReal.measurable_ofReal.comp measurable_qkW).lintegral_prod_right'
  have mID : Measurable (fun W : MlpParam (2 * n) (mW n) n =>
      ∫⁻ θ, ENNReal.ofReal (d1W W θ) ∂hidGauss n (mA n)) :=
    (ENNReal.measurable_ofReal.comp measurable_d1W).lintegral_prod_right'
  refine (lintegral_mono fun W => centre_inner hn hwin hP hζ W).trans ?_
  have e : ∀ W : MlpParam (2 * n) (mW n) n, (goodWAG G).indicator (fun W =>
        ENNReal.ofReal (cQ3 π₀ ζ / ((mA n : ℝ) / n)) *
            ∫⁻ θ, ENNReal.ofReal (qkW W θ) ∂hidGauss n (mA n) +
          ENNReal.ofReal (cD3 εD π₀ ζ / ((mA n : ℝ) / n)) *
            ∫⁻ θ, ENNReal.ofReal (d1W W θ) ∂hidGauss n (mA n)) W =
      ENNReal.ofReal (cQ3 π₀ ζ / ((mA n : ℝ) / n)) * (goodWAG G).indicator
          (fun W => ∫⁻ θ, ENNReal.ofReal (qkW W θ) ∂hidGauss n (mA n)) W +
        ENNReal.ofReal (cD3 εD π₀ ζ / ((mA n : ℝ) / n)) * (goodWAG G).indicator
          (fun W => ∫⁻ θ, ENNReal.ofReal (d1W W θ) ∂hidGauss n (mA n)) W := by
    intro W
    by_cases hW : W ∈ goodWAG G
    · simp only [Set.indicator_of_mem hW]
    · simp only [Set.indicator_of_notMem hW, mul_zero, add_zero]
  rw [lintegral_congr e, lintegral_add_right _ ((mID.indicator mGW).const_mul _),
    lintegral_const_mul _ (mIQ.indicator mGW), lintegral_const_mul _ (mID.indicator mGW)]
  have h1 := qk_mean hn hG hwin hdQ hQ0
  have h2 := d1_mean hn1 hG (fun x hx => (hwin x hx).1)
  refine (add_le_add (mul_le_mul' le_rfl h1) (mul_le_mul' le_rfl h2)).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold xiB
  field_simp

/-! ## The error of the mean-field output against the exact-centre output -/

/-- The stage at fixed `(W, A₁, A₂)`, integrated over `(A₃, F)`. -/
lemma errB_key (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))}
    {alo ahi : ℝ} (hwin : WinOK2 n G alo ahi) {Δmax ΔXmax εD εQ π₀ Dmax ρhi yhi : ℝ}
    (hΔmax : 0 < Δmax) (hA1 : Δmax < alo) (hA2 : ahi + Δmax < 1)
    (hP : POK3 ahi Δmax εD εQ π₀ Dmax ρhi yhi)
    (W : MlpParam (2 * n) (mW n) n) (θ : HidParam n (mA n)) :
    ∫⁻ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        ENNReal.ofReal (dOut3 G Δmax ΔXmax εD εQ Dmax (W, (θ.1, θ.2, y.1), y.2))
        ∂((gaussMat n (mA n) (2 / (mA n : ℝ))).prod (mlpGauss n (mF n) 1)) ≤
      ENNReal.ofReal (2 / (n : ℝ) * (2 / (1 - yhi)) / ((mA n : ℝ) / n)) *
        (goodX1 G εD εQ).indicator (fun x => ENNReal.ofReal (eCW x.1 x.2)) (W, θ) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := BstLean.Part132.mF_ge hn; omega
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  have hd0 : (0 : ℝ) < (mA n : ℝ) / n := by positivity
  have hy1 : 0 < 1 - yhi := by linarith [hP.hy1]
  by_cases hx : (W, θ) ∈ goodX2 G Δmax ΔXmax ∧ (W, θ) ∈ goodX3 G εD εQ Dmax
  · obtain ⟨⟨hW, hK, _⟩, hx1, hC⟩ := hx
    have hx2 : (W, θ) ∈ goodX2 G Δmax ΔXmax := by
      refine ⟨hW, hK, ?_⟩
      assumption
    rw [Set.indicator_of_mem hx1]
    have hmem : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        ((W, (θ.1, θ.2, y.1), y.2) : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) ∈ goodT23 G Δmax ΔXmax εD εQ Dmax :=
      fun y => ⟨hx2, hx1, hC⟩
    have e : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        dOut3 G Δmax ΔXmax εD εQ Dmax (W, (θ.1, θ.2, y.1), y.2) =
          (gO (bMF (cenA W) (tauWA W) θ) (tauOutOf n (bMF (cenA W) (tauWA W) θ)) y -
            gO (bbar (cenA W) (tauWA W) θ) (tauOutOf n (bbar (cenA W) (tauWA W) θ)) y) ^ 2 := by
      intro y
      unfold dOut3
      rw [Set.indicator_of_mem (hmem y)]
      rfl
    simp_rw [e]
    obtain ⟨_, _, _, _, hal, hah⟩ := hwin (W.1, W.2.1) hW
    -- the two centres are at most `d·yhi` in squared length
    have hK0 := eK_nonneg W θ
    have hD0 := eD_nonneg W θ
    set d : ℝ := (mA n : ℝ) / n with hd
    set au : ℝ := kappa (kappa (qTh (W.1, W.2.1))) with hau
    have hsc := scalarsA (stdGauss (Fin n)) (h := hA (cenA W) (tauWA W) θ)
      (fun j => bm_hA hn1 (cenA W) (tauWA W) θ j) (a := d * au) (Δ := d * Δmax) (d := d)
      (δ := √(eD W θ)) (by positivity) (Real.sqrt_nonneg _)
      (by nlinarith) (by nlinarith) hK (by rw [Real.sq_sqrt hD0]; exact le_rfl)
    have hY : normSq (bbar (cenA W) (tauWA W) θ) ≤ d * (ahi + Δmax) := by
      have h1 := (abs_le.mp hsc.1).2
      have h2 : normSq (bbar (cenA W) (tauWA W) θ) ≤ d * au + d * Δmax := by
        change normSq (hbar (stdGauss (Fin n)) (hA (cenA W) (tauWA W) θ)) ≤ d * au + d * Δmax
        linarith
      nlinarith
    have hρ := hP.hρ
    have hYb : normSq (bbar (cenA W) (tauWA W) θ) ≤ d * yhi := by
      refine hY.trans (mul_le_mul_of_nonneg_left ?_ hd0.le)
      have : ρhi ^ 2 ≤ (ρhi + Dmax) ^ 2 := by nlinarith [hP.hρ0, hP.hDmax]
      linarith [hP.hy]
    have hYm : normSq (bMF (cenA W) (tauWA W) θ) ≤ d * yhi := by
      have t1 := BstLean.Part140.nrm_add_le' (bbar (cenA W) (tauWA W) θ)
        (bMF (cenA W) (tauWA W) θ - bbar (cenA W) (tauWA W) θ)
      have eb : bbar (cenA W) (tauWA W) θ + (bMF (cenA W) (tauWA W) θ -
          bbar (cenA W) (tauWA W) θ) = bMF (cenA W) (tauWA W) θ := by abel
      rw [eb] at t1
      have n1 := nrm_sq (bMF (cenA W) (tauWA W) θ)
      have n2 := nrm_sq (bbar (cenA W) (tauWA W) θ)
      have n3 := nrm_sq (bMF (cenA W) (tauWA W) θ - bbar (cenA W) (tauWA W) θ)
      have p1 := nrm_nonneg (bMF (cenA W) (tauWA W) θ)
      have p2 := nrm_nonneg (bbar (cenA W) (tauWA W) θ)
      have p3 := nrm_nonneg (bMF (cenA W) (tauWA W) θ - bbar (cenA W) (tauWA W) θ)
      have q2 : nrm (bbar (cenA W) (tauWA W) θ) ≤ √d * ρhi := by
        refine Real.sqrt_le_sqrt (hY.trans (mul_le_mul_of_nonneg_left hρ hd0.le)) |>.trans
          (le_of_eq ?_)
        rw [Real.sqrt_mul hd0.le, Real.sqrt_sq hP.hρ0]
      have q3 : nrm (bMF (cenA W) (tauWA W) θ - bbar (cenA W) (tauWA W) θ) ≤ √d * Dmax := by
        have hC' : normSq (bMF (cenA W) (tauWA W) θ - bbar (cenA W) (tauWA W) θ) ≤
            d * Dmax ^ 2 := hC
        refine (Real.sqrt_le_sqrt hC').trans (le_of_eq ?_)
        rw [Real.sqrt_mul hd0.le, Real.sqrt_sq hP.hDmax.le]
      have hsd := Real.sq_sqrt hd0.le
      have hsd0 := Real.sqrt_nonneg d
      have q1 : nrm (bMF (cenA W) (tauWA W) θ) ≤ √d * (ρhi + Dmax) := by linarith
      have : nrm (bMF (cenA W) (tauWA W) θ) ^ 2 ≤ (√d * (ρhi + Dmax)) ^ 2 :=
        pow_le_pow_left₀ p1 q1 2
      rw [n1, mul_pow, hsd] at this
      exact this.trans (mul_le_mul_of_nonneg_left hP.hy hd0.le)
    have hYd : d * yhi < (mA n : ℝ) / n := by rw [← hd]; nlinarith [hP.hy1]
    have hcmp := outCompare_tau (mF := mF n) hn1 hmA hmF hYm hYb hYd
    refine hcmp.trans (le_of_eq ?_)
    have hC0 := eCW_nonneg W θ
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have e1 : normSq (bMF (cenA W) (tauWA W) θ - bbar (cenA W) (tauWA W) θ) = eCW W θ := rfl
    rw [e1, ← hd]
    have hyne : (1 - yhi) ≠ 0 := hy1.ne'
    have e2 : d / (d - d * yhi) = 1 / (1 - yhi) := by
      rw [show d - d * yhi = d * (1 - yhi) by ring]
      field_simp
    rw [e2, hd]
    field_simp
  · have hmem : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        ((W, (θ.1, θ.2, y.1), y.2) : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) ∉ goodT23 G Δmax ΔXmax εD εQ Dmax :=
      fun y h => hx ⟨h.1, h.2⟩
    have e : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
        dOut3 G Δmax ΔXmax εD εQ Dmax (W, (θ.1, θ.2, y.1), y.2) = 0 := fun y => by
      unfold dOut3
      rw [Set.indicator_of_notMem (hmem y)]
    simp_rw [e]
    simp

/-- **The mean squared difference of the output with the mean-field centre and the output with
the exact centre, on the good event**:
`E[1_good·(gOutB − gOutA)²] ≤ (2/n)·(2/(1 − yhi))·xiB`. -/
theorem errB_lint (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {alo ahi : ℝ} (hwin : WinOK2 n G alo ahi) {Δmax ΔXmax εD εQ π₀ Dmax ρhi yhi : ℝ}
    (hΔmax : 0 < Δmax) (hA1 : Δmax < alo) (hA2 : ahi + Δmax < 1)
    (hP : POK3 ahi Δmax εD εQ π₀ Dmax ρhi yhi) {ζ : ℝ} (hζ : 0 < ζ) {dQb : ℝ}
    (hdQ : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dQ1 n (mA n) q ≤ dQb)
    (hQ0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dQ1 n (mA n) q) :
    ∫⁻ t, ENNReal.ofReal (dOut3 G Δmax ΔXmax εD εQ Dmax t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (2 / (n : ℝ) * (2 / (1 - yhi)) * xiB n εD π₀ ζ dQb) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  have hd0 : (0 : ℝ) < (mA n : ℝ) / n := by positivity
  have hy1 : 0 < 1 - yhi := by linarith [hP.hy1]
  have mOD : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ENNReal.ofReal (dOut3 G Δmax ΔXmax εD εQ Dmax t)) :=
    ENNReal.measurable_ofReal.comp (measurable_dOut3 hG hn1 Δmax ΔXmax εD εQ Dmax)
  have mind : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) =>
      (goodX1 G εD εQ).indicator (fun x => ENNReal.ofReal (eCW x.1 x.2)) x) :=
    (ENNReal.measurable_ofReal.comp measurable_eCW).indicator (goodX1_meas hG hn1 εD εQ)
  have inner : ∀ W : MlpParam (2 * n) (mW n) n,
      ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
          ENNReal.ofReal (dOut3 G Δmax ΔXmax εD εQ Dmax (W, p))
          ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) ≤
        ENNReal.ofReal (2 / (n : ℝ) * (2 / (1 - yhi)) / ((mA n : ℝ) / n)) *
          ∫⁻ θ, (goodX1 G εD εQ).indicator (fun x => ENNReal.ofReal (eCW x.1 x.2)) (W, θ)
            ∂hidGauss n (mA n) := by
    intro W
    have mgW : Measurable (fun p : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
        ENNReal.ofReal (dOut3 G Δmax ΔXmax εD εQ Dmax (W, p))) :=
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
    refine (lintegral_mono fun θ => errB_key hn hwin hΔmax hA1 hA2 hP W θ).trans (le_of_eq ?_)
    exact lintegral_const_mul _ (mind.comp measurable_prodMk_left)
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
  rw [e0, lintegral_prod _ mOD.aemeasurable]
  refine (lintegral_mono inner).trans ?_
  rw [lintegral_const_mul _ mind.lintegral_prod_right']
  refine (mul_le_mul' le_rfl (centre_mean hn hG hwin hP hζ hdQ hQ0)).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  field_simp

/-! ## The probability of the bad event -/

/-- Markov's inequality in the form used here. -/
lemma markov_real {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ≥0∞} (mf : Measurable f) {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B)
    (hint : ∫⁻ t, f t ∂μ ≤ ENNReal.ofReal B) :
    μ.real {t | ENNReal.ofReal ε < f t} ≤ B / ε := by
  have hε0 : ENNReal.ofReal ε ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hε
  have h := meas_ge_le_lintegral_div (μ := μ) mf.aemeasurable hε0 ENNReal.ofReal_ne_top
  have hsub0 : {t | ENNReal.ofReal ε < f t} ⊆ {t | ENNReal.ofReal ε ≤ f t} := by
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht ⊢
    exact le_of_lt ht
  have h2 : μ {t | ENNReal.ofReal ε < f t} ≤ ENNReal.ofReal B / ENNReal.ofReal ε :=
    (measure_mono hsub0).trans (h.trans (ENNReal.div_le_div_right hint _))
  rw [← ENNReal.ofReal_div_of_pos hε] at h2
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h2

/-- **The bad event of the mean-field centre.** -/
theorem badT3_prob (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {alo ahi : ℝ} (hwin : WinOK2 n G alo ahi) {Δmax εD εQ π₀ Dmax ρhi yhi : ℝ}
    (hP : POK3 ahi Δmax εD εQ π₀ Dmax ρhi yhi) {ζ : ℝ} (hζ : 0 < ζ) {dQb : ℝ}
    (hdQ : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dQ1 n (mA n) q ≤ dQb)
    (hQ0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dQ1 n (mA n) q)
    {p : ℝ} (h1 : (hidGauss (2 * n) (mW n)).real Gᶜ ≤ p) :
    (mlpTriple 2 n).real (goodT3 G εD εQ Dmax)ᶜ ≤
      p + 68000000 / (qA n : ℝ) ^ 2 + dQb ^ 2 / εQ ^ 2 + 5 / (mA n : ℝ) / εD ^ 2 +
        xiB n εD π₀ ζ dQb / Dmax ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  set d : ℝ := (mA n : ℝ) / n with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have hK := Kq_nonneg
  have hπ0 := hP.hπ0
  have hπ1 : 0 < 1 - π₀ := by linarith [hP.hπ1]
  have hcQ : 0 ≤ cQ3 π₀ ζ := by unfold cQ3; positivity
  have hcD : 0 ≤ cD3 εD π₀ ζ := by unfold cD3; positivity
  have hxi : 0 ≤ xiB n εD π₀ ζ dQb := by unfold xiB; positivity
  have mGW := goodWAG0_meas hG hn1
  have mWs : MeasurableSet {x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) |
      x.1 ∈ goodWAG G} := measurable_fst mGW
  set fQ : MlpParam (2 * n) (mW n) n × HidParam n (mA n) → ℝ≥0∞ :=
    ({x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) | x.1 ∈ goodWAG G}).indicator
      (fun x => ENNReal.ofReal (qkW x.1 x.2)) with hfQ
  set fD : MlpParam (2 * n) (mW n) n × HidParam n (mA n) → ℝ≥0∞ :=
    ({x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) | x.1 ∈ goodWAG G}).indicator
      (fun x => ENNReal.ofReal (d1W x.1 x.2)) with hfD
  set fC : MlpParam (2 * n) (mW n) n × HidParam n (mA n) → ℝ≥0∞ :=
    (goodX1 G εD εQ).indicator (fun x => ENNReal.ofReal (eCW x.1 x.2)) with hfC
  have mfQ : Measurable fQ := (ENNReal.measurable_ofReal.comp measurable_qkW).indicator mWs
  have mfD : Measurable fD := (ENNReal.measurable_ofReal.comp measurable_d1W).indicator mWs
  have mfC : Measurable fC :=
    (ENNReal.measurable_ofReal.comp measurable_eCW).indicator (goodX1_meas hG hn1 εD εQ)
  set μ := mlpTriple 2 n with hμ
  have iQ : ∫⁻ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      fQ (t.1, thA t.2.1) ∂μ ≤ ENNReal.ofReal ((d * dQb) ^ 2) := by
    rw [hμ, lint_WX mfQ]
    have e : ∀ W : MlpParam (2 * n) (mW n) n, ∫⁻ θ, fQ (W, θ) ∂hidGauss n (mA n) =
        (goodWAG G).indicator
          (fun W => ∫⁻ θ, ENNReal.ofReal (qkW W θ) ∂hidGauss n (mA n)) W := by
      intro W
      by_cases hW : W ∈ goodWAG G
      · simp [hfQ, Set.indicator_of_mem, hW]
      · simp [hfQ, Set.indicator_of_notMem, hW]
    simp_rw [e]
    exact qk_mean hn hG hwin hdQ hQ0
  have iD : ∫⁻ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      fD (t.1, thA t.2.1) ∂μ ≤ ENNReal.ofReal (d ^ 2 * (5 / (mA n : ℝ))) := by
    rw [hμ, lint_WX mfD]
    have e : ∀ W : MlpParam (2 * n) (mW n) n, ∫⁻ θ, fD (W, θ) ∂hidGauss n (mA n) =
        (goodWAG G).indicator
          (fun W => ∫⁻ θ, ENNReal.ofReal (d1W W θ) ∂hidGauss n (mA n)) W := by
      intro W
      by_cases hW : W ∈ goodWAG G
      · simp [hfD, Set.indicator_of_mem, hW]
      · simp [hfD, Set.indicator_of_notMem, hW]
    simp_rw [e]
    exact d1_mean hn1 hG (fun x hx => (hwin x hx).1)
  have iC : ∫⁻ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      fC (t.1, thA t.2.1) ∂μ ≤ ENNReal.ofReal (d * xiB n εD π₀ ζ dQb) := by
    rw [hμ, lint_WX mfC]
    exact centre_mean hn hG hwin hP hζ hdQ hQ0
  have mQ' : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => fQ (t.1, thA t.2.1)) := mfQ.comp measurable_WX
  have mD' : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => fD (t.1, thA t.2.1)) := mfD.comp measurable_WX
  have mC' : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => fC (t.1, thA t.2.1)) := mfC.comp measurable_WX
  have hεQ := hP.hεQ0
  have hεD := hP.hεD0
  have hDm := hP.hDmax
  have pQ := markov_real μ mQ' (ε := (d * εQ) ^ 2) (by positivity) (by positivity) iQ
  have pD := markov_real μ mD' (ε := (d * εD) ^ 2) (by positivity) (by positivity) iD
  have pC := markov_real μ mC' (ε := d * Dmax ^ 2) (by positivity) (by positivity) iC
  have eQ : (d * dQb) ^ 2 / (d * εQ) ^ 2 = dQb ^ 2 / εQ ^ 2 := by field_simp
  have eD' : d ^ 2 * (5 / (mA n : ℝ)) / (d * εD) ^ 2 = 5 / (mA n : ℝ) / εD ^ 2 := by field_simp
  have eC' : d * xiB n εD π₀ ζ dQb / (d * Dmax ^ 2) = xiB n εD π₀ ζ dQb / Dmax ^ 2 := by
    field_simp
  rw [eQ] at pQ
  rw [eD'] at pD
  rw [eC'] at pC
  have hbad := badAG0_prob_gen hn hG h1
  have hsub : (goodT3 G εD εQ Dmax)ᶜ ⊆
      {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
        t.1 ∉ goodWAG G} ∪
      ({t | ENNReal.ofReal ((d * εQ) ^ 2) < fQ (t.1, thA t.2.1)} ∪
        ({t | ENNReal.ofReal ((d * εD) ^ 2) < fD (t.1, thA t.2.1)} ∪
          {t | ENNReal.ofReal (d * Dmax ^ 2) < fC (t.1, thA t.2.1)})) := by
    intro t ht
    by_cases hW : t.1 ∈ goodWAG G
    swap
    · exact Or.inl hW
    refine Or.inr ?_
    have hWx : (t.1, thA t.2.1) ∈ {x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) |
        x.1 ∈ goodWAG G} := hW
    by_cases hQ : qkW t.1 (thA t.2.1) ≤ (d * εQ) ^ 2
    swap
    · refine Or.inl ?_
      push Not at hQ
      change ENNReal.ofReal ((d * εQ) ^ 2) < fQ (t.1, thA t.2.1)
      rw [hfQ, Set.indicator_of_mem hWx]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (sq_nonneg _) hQ)).mpr hQ
    refine Or.inr ?_
    by_cases hD : d1W t.1 (thA t.2.1) ≤ (d * εD) ^ 2
    swap
    · refine Or.inl ?_
      push Not at hD
      change ENNReal.ofReal ((d * εD) ^ 2) < fD (t.1, thA t.2.1)
      rw [hfD, Set.indicator_of_mem hWx]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (sq_nonneg _) hD)).mpr hD
    refine Or.inr ?_
    have hX1 : (t.1, thA t.2.1) ∈ goodX1 G εD εQ := ⟨hW, hD, hQ⟩
    have hC : ¬ eCW t.1 (thA t.2.1) ≤ d * Dmax ^ 2 := fun hC => ht ⟨hX1, hC⟩
    push Not at hC
    change ENNReal.ofReal (d * Dmax ^ 2) < fC (t.1, thA t.2.1)
    rw [hfC, Set.indicator_of_mem hX1]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (by positivity) hC)).mpr hC
  have hm := measureReal_mono (μ := μ) hsub (measure_ne_top _ _)
  have u1 := measureReal_union_le (μ := μ)
    {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
      t.1 ∉ goodWAG G}
    ({t | ENNReal.ofReal ((d * εQ) ^ 2) < fQ (t.1, thA t.2.1)} ∪
      ({t | ENNReal.ofReal ((d * εD) ^ 2) < fD (t.1, thA t.2.1)} ∪
        {t | ENNReal.ofReal (d * Dmax ^ 2) < fC (t.1, thA t.2.1)}))
  have u2 := measureReal_union_le (μ := μ)
    {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
      ENNReal.ofReal ((d * εQ) ^ 2) < fQ (t.1, thA t.2.1)}
    ({t | ENNReal.ofReal ((d * εD) ^ 2) < fD (t.1, thA t.2.1)} ∪
      {t | ENNReal.ofReal (d * Dmax ^ 2) < fC (t.1, thA t.2.1)})
  have u3 := measureReal_union_le (μ := μ)
    {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
      ENNReal.ofReal ((d * εD) ^ 2) < fD (t.1, thA t.2.1)}
    {t | ENNReal.ofReal (d * Dmax ^ 2) < fC (t.1, thA t.2.1)}
  linarith

end BstLean.Part149

open BstLean.Part149 in
#print axioms centre_mean
open BstLean.Part149 in
#print axioms errB_lint
open BstLean.Part149 in
#print axioms badT3_prob
