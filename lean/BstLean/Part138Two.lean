import BstLean.Part138Num

/-!
# Part 138, item 5: the cheap stand-in with the scalar from one uniform input

Role: `delegations/statements/p138-spec.md`. Paper source: `onW16c-cx.md` §5 (the calibration of
the two-pass program: `w₀ = w(u₁)`, `τ₀² = t|b|²·max(0, w₀)`). The centre is the exact mean
hidden vector `h̄` (NOT the arithmetic centre of the programs).

* `tau1 N m u₁ θ = √(t|h̄|²·max(0, w(u₁)))`: the scalar from one input `u₁`.
* `wUp = 1/0.4936 − 1`; `rLow1 ζ = (wLow − ζ′)/(wUp + ζ′)` (the paper's `r_low`);
  `cRho1 ζ = (1 + √r_low)²(1 + r_low)`; `C1 n ζ = n/((wLow − ζ′)²·cRho1 ζ)`.
* `cheap_fixed`: the theorem for fixed `(M₁, M₂)`, every constant `τ₀ > 0` and every bound `K`
  of the squared Hellinger distance at the inputs.
* `good_pt1`: for `θ ∈ good136 n` and `u, u₁ ∈ G_ζ`:
  `hellG n (σ(u)/λ(u)) (tau1 u₁) ≤ C1·2((w(u) − w̄)² + (w(u₁) − w̄)²)`.
* `EH1 n ζ = 4·C1·Omega2 + Beta` (the paper's `EH2 = 4nω_r²/((w_low − ζ′)²(1 + √r_low)²(1 + r_low))
  + 4β_r`, with `β_r` in place of `4β_r`: here the bad inputs `u₁` are outside the indicator).
* **`cheapTwo138`**: over `(u₁, M₁, M₂, M₃)`, `u₁` uniform on the sphere and independent of `W`:
  `E[1_{good, u₁ ∈ G_ζ}·(E_{μ_W} φ − E_{ν′} φ)²] ≤
     2·(0.99/n)·E_W[1_good·Var_{ν_W} φ] + 8B²·EH1 n ζ`.
* **`cheapTwo138_tail`**: `Pr(|E_{μ_W} φ − E_{ν′} φ| ≥ t) ≤
     0.002 + Beta n ζ + (2·(0.99/n)·E_W Var_{ν_W} φ + 8B²·EH1 n ζ)/t²`.
* `EH1_le`: `EH1 n (1/20) ≤ 5200·n/m`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part138

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137

/-! ## Definitions -/

/-- **The scalar from one input `u₁`**: `τ₀ = √(t|h̄|²·max(0, w(u₁)))`. -/
noncomputable def tau1 (N m : ℕ) (u₁ : Fin N → ℝ) (θ : HidParam N m) : ℝ :=
  √(2 / (m : ℝ) * normSq (hbarW θ) * max 0 (wn N m u₁ θ))

/-- The upper bound of `w̄` on `good136 n`. -/
noncomputable def wUp : ℝ := 1 / (4936 / 10000) - 1

/-- The paper's `r_low` for a scalar from one good input. -/
noncomputable def rLow1 (ζ : ℝ) : ℝ := (wLow - zetaP ζ) / (wUp + zetaP ζ)

noncomputable def cRho1 (ζ : ℝ) : ℝ := (1 + √(rLow1 ζ)) ^ 2 * (1 + rLow1 ζ)

/-- `C1 n ζ = n/((wLow − ζ′)²·cRho1 ζ)`. -/
noncomputable def C1 (n : ℕ) (ζ : ℝ) : ℝ := (n : ℝ) / ((wLow - zetaP ζ) ^ 2 * cRho1 ζ)

/-- **`EH1 n ζ = 4·C1·Omega2 + Beta`**. -/
noncomputable def EH1 (n : ℕ) (ζ : ℝ) : ℝ := 4 * C1 n ζ * Omega2 n ζ + Beta n ζ

lemma wUp_pos : 0 < wUp := by unfold wUp; norm_num

lemma rLow1_nonneg {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) (hz : zetaP ζ < wLow) : 0 ≤ rLow1 ζ := by
  unfold rLow1
  have := zetaP_nonneg hζ0 hζ1
  have := wUp_pos
  exact div_nonneg (by linarith) (by linarith)

lemma cRho1_pos {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) (hz : zetaP ζ < wLow) : 0 < cRho1 ζ := by
  unfold cRho1
  have h1 := rLow1_nonneg hζ0 hζ1 hz
  have h2 := Real.sqrt_nonneg (rLow1 ζ)
  positivity

lemma C1_nonneg {n : ℕ} {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) (hz : zetaP ζ < wLow) :
    0 ≤ C1 n ζ := by
  unfold C1
  have := cRho1_pos hζ0 hζ1 hz
  positivity

lemma measurable_tau1 {N m : ℕ} (hN : 1 ≤ N) :
    Measurable (fun p : (Fin N → ℝ) × HidParam N m => tau1 N m p.1 p.2) := by
  unfold tau1
  exact (((measurable_normSq.comp ((measurable_hbarW hN).comp measurable_snd)).const_mul _).mul
    (measurable_const.max (measurable_wn hN))).sqrt

/-- `(w − w̄)²` on the good event and the good inputs. -/
noncomputable def Fsq (n : ℕ) (ζ : ℝ) : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) → ℝ :=
  (goodS (good136 n) ζ).indicator
    (fun p => (wn (2 * n) (mW n) p.1 p.2 - wbar (2 * n) (mW n) p.2) ^ 2)

/-- The bad set: `θ` in the good event, `u` not a good input. -/
def badS (n : ℕ) (ζ : ℝ) : Set ((Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) :=
  {p | p.2 ∈ good136 n ∧ p ∉ goodU (2 * n) (mW n) ζ}

/-- The indicator of the bad set. -/
noncomputable def Fbad (n : ℕ) (ζ : ℝ) : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) → ℝ :=
  (badS n ζ).indicator (fun _ => (1 : ℝ))

/-- `Gm n ζ C θ = E_u[C·Fsq(u, θ) + Fbad(u, θ)]`. -/
noncomputable def Gm (n : ℕ) (ζ C : ℝ) (θ : HidParam (2 * n) (mW n)) : ℝ :=
  ∫ u, (C * Fsq n ζ (u, θ) + Fbad n ζ (u, θ)) ∂uniformSphere (2 * n)

/-- The bound of the squared Hellinger distance at the input `u`, for the scalar from an input
with `(w(u₁) − w̄)² = d`. -/
noncomputable def K1fun (n : ℕ) (ζ d : ℝ) (p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) : ℝ :=
  (goodU (2 * n) (mW n) ζ).indicator
      (fun p => C1 n ζ *
        (2 * ((wn (2 * n) (mW n) p.1 p.2 - wbar (2 * n) (mW n) p.2) ^ 2 + d))) p +
    (goodU (2 * n) (mW n) ζ)ᶜ.indicator (fun _ => (1 : ℝ)) p

lemma Fsq_nonneg (n : ℕ) (ζ : ℝ) (p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) :
    0 ≤ Fsq n ζ p := Set.indicator_nonneg (fun _ _ => sq_nonneg _) p

lemma Fbad_nonneg (n : ℕ) (ζ : ℝ) (p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) :
    0 ≤ Fbad n ζ p := Set.indicator_nonneg (fun _ _ => zero_le_one) p

lemma Fbad_le_one (n : ℕ) (ζ : ℝ) (p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) :
    Fbad n ζ p ≤ 1 := by
  unfold Fbad
  by_cases hp : p ∈ badS n ζ
  · rw [Set.indicator_of_mem hp]
  · rw [Set.indicator_of_notMem hp]; exact zero_le_one

lemma measurable_Fsq {n : ℕ} (hn : 1 ≤ n) (ζ : ℝ) : Measurable (Fsq n ζ) := by
  have hN : 1 ≤ 2 * n := by omega
  unfold Fsq
  exact (((measurable_wn hN).sub ((measurable_wbar hN).comp measurable_snd)).pow_const
    2).indicator (goodS_meas hN (good136_meas hn) ζ)

lemma badS_meas {n : ℕ} (hn : 1 ≤ n) (ζ : ℝ) : MeasurableSet (badS n ζ) :=
  (measurable_snd (good136_meas hn)).inter (goodU_meas (by omega) ζ).compl

lemma measurable_Fbad {n : ℕ} (hn : 1 ≤ n) (ζ : ℝ) : Measurable (Fbad n ζ) :=
  measurable_const.indicator (badS_meas hn ζ)

lemma measurable_K1fun {n : ℕ} (hn : 1 ≤ n) (ζ d : ℝ) : Measurable (K1fun n ζ d) := by
  have hN : 1 ≤ 2 * n := by omega
  unfold K1fun
  exact ((((((measurable_wn hN).sub ((measurable_wbar hN).comp measurable_snd)).pow_const
    2).add_const d).const_mul 2).const_mul _).indicator (goodU_meas hN ζ) |>.add
    (measurable_const.indicator (goodU_meas hN ζ).compl)

/-! ## The means over `(u, θ)` -/

section mean

variable {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)

include hn hζ0 hζ1

lemma Fsq_int :
    Integrable (Fsq n ζ) ((uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n))) ∧
      ∫ p, Fsq n ζ p ∂((uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n))) ≤ Omega2 n ζ := by
  have hN : 1 ≤ 2 * n := by omega
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have mE := good136_meas (n := n) (by omega)
  refine ⟨?_, tauFluct137 hn hζ0.le hζ1⟩
  have h := (tauFluct_gen hN hm mE (by norm_num : (0 : ℝ) < 4936 / 10000) hζ0.le hζ1
    (fun θ hθ => (Bn136 hn hθ).1)).int_sq
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  unfold Fsq
  by_cases hp : p ∈ goodS (good136 n) ζ
  · simp [Set.indicator_of_mem hp]
  · simp [Set.indicator_of_notMem hp]

omit hζ1 in
lemma Fbad_int :
    Integrable (Fbad n ζ) ((uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n))) ∧
      ∫ p, Fbad n ζ p ∂((uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n))) ≤ Beta n ζ := by
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  have mB := badS_meas (n := n) (by omega) ζ
  refine ⟨(integrable_const (1 : ℝ)).indicator mB, ?_⟩
  have e : ∫ p, Fbad n ζ p ∂((uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n))) =
      ((uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n))).real (badS n ζ) := by
    unfold Fbad
    rw [integral_indicator mB, setIntegral_const, smul_eq_mul, mul_one]
  rw [e]
  exact tauBad137 hn hζ0

/-- `θ ↦ Gm n ζ C θ` is integrable, and `E_θ Gm ≤ C·Omega2 + Beta` for `C ≥ 0`. -/
lemma Gm_mean {C : ℝ} (hC : 0 ≤ C) :
    Integrable (Gm n ζ C) (hidGauss (2 * n) (mW n)) ∧
      ∫ θ, Gm n ζ C θ ∂hidGauss (2 * n) (mW n) ≤ C * Omega2 n ζ + Beta n ζ := by
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  obtain ⟨i1, h1⟩ := Fsq_int hn hζ0 hζ1
  obtain ⟨i2, h2⟩ := Fbad_int hn hζ0
  have i1' : Integrable (fun p => C * Fsq n ζ p)
      ((uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n))) := i1.const_mul C
  have iF : Integrable (fun p => C * Fsq n ζ p + Fbad n ζ p)
      ((uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n))) := i1'.add i2
  refine ⟨iF.integral_prod_right, ?_⟩
  unfold Gm
  rw [← integral_prod_symm _ iF, integral_add i1' i2, integral_const_mul]
  have := mul_le_mul_of_nonneg_left h1 hC
  linarith

end mean

lemma Gm_nonneg (n : ℕ) (ζ : ℝ) {C : ℝ} (hC : 0 ≤ C) (θ : HidParam (2 * n) (mW n)) :
    0 ≤ Gm n ζ C θ :=
  integral_nonneg fun _ => add_nonneg (mul_nonneg hC (Fsq_nonneg n ζ _)) (Fbad_nonneg n ζ _)

/-! ## Fixed `(M₁, M₂)` -/

section fixed

variable {n : ℕ} (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ good136 n)

include hn hθ

/-- **The cheap stand-in theorem for fixed `(M₁, M₂)`, a general constant `τ₀ > 0`.** `K` is a
measurable integrable function of the input with: at every `u`, either `λ(u) > 0` and
`hellG n (σ(u)/λ(u)) τ₀ ≤ K(u)`, or `1 ≤ K(u)`. Then for measurable `φ` with `|φ| ≤ B`:
`E_{M₃}(E_{μ_W} φ − E_{ν′} φ)² ≤ 2·(0.99/n)·E_c Var_{ν_c} φ + 8B²·E_u K`. -/
theorem cheap_fixed {τ₀ : ℝ} (hτ₀ : 0 < τ₀) {K : (Fin (2 * n) → ℝ) → ℝ} (hKm : Measurable K)
    (hKi : Integrable K (uniformSphere (2 * n)))
    (hK : ∀ u, (0 < lam (hbarW θ) (hid2 θ.1 θ.2 u) ∧
        hellG n (sig (2 / (mW n : ℝ)) (hbarW θ) (hid2 θ.1 θ.2 u) /
          lam (hbarW θ) (hid2 θ.1 θ.2 u)) τ₀ ≤ K u) ∨ 1 ≤ K u)
    {φ : (Fin n → ℝ) → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, |φ x| ≤ B) :
    ∫ M₃, ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂cheapIn (M₃.mulVec (hbarW θ)) τ₀) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)) ≤
      2 * (99 / 100 / (n : ℝ) *
        ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
          (hbarW θ) c] ∂cDist n (2 / (mW n : ℝ)) (hbarW θ)) +
      8 * B ^ 2 * ∫ u, K u ∂uniformSphere (2 * n) := by
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  have hh : Measurable (hid2 θ.1 θ.2) := (continuous_hid2 θ.1 θ.2).measurable
  have hφb : BM φ := ⟨hφ, B, hB⟩
  set P := gaussMat n (mW n) (2 / (mW n : ℝ)) with hP
  set b := hbarW θ with hb
  have hK0 : ∀ u, 0 ≤ K u := by
    intro u
    rcases hK u with ⟨_, h2⟩ | h2
    · exact (hellG_nonneg _ _ _).trans h2
    · linarith
  have hKint0 : 0 ≤ ∫ u, K u ∂uniformSphere (2 * n) := integral_nonneg hK0
  have hb2 : ∀ x, φ x ^ 2 ≤ B ^ 2 := fun x => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
  -- at one `c`
  have hc : ∀ c : Fin n → ℝ,
      (∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b c -
        ∫ x, φ x ∂cheapIn c τ₀) ^ 2 ≤ 4 * B ^ 2 * ∫ u, K u ∂uniformSphere (2 * n) := by
    intro c
    have p1 := standIn_prob (n := n) (uniformSphere (2 * n)) hh (2 / (mW n : ℝ)) b c
    have p2 := cheapIn_prob c τ₀
    have h := cheap_mix (uniformSphere (2 * n)) (by omega : 2 ≤ n) (2 / (mW n : ℝ)) b c hh
      hτ₀ hKm hKi hK hφb
    have h1 := integral_mono (hφb.sq.integrable
      (standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b c))
      (integrable_const (B ^ 2)) hb2
    have h2 := integral_mono (hφb.sq.integrable (cheapIn c τ₀)) (integrable_const (B ^ 2)) hb2
    simp only [integral_const, probReal_univ, one_smul] at h1 h2
    have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 h2)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hKint0)
    linarith
  have bX : BM (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      ∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) :=
    (bm_muW hN hφb).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have mb : Measurable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ => M₃.mulVec b) :=
    measurable_mulVec_right b
  have bY := (bm_standIn (n := n) (uniformSphere (2 * n)) (2 / (mW n : ℝ)) b hh hφb).comp mb
  have bZ := (bm_cheapIn (cc := fun c : Fin n → ℝ => c) (tt := fun _ => τ₀) measurable_id
    measurable_const hφb).comp mb
  have hpt : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
      ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂cheapIn (M₃.mulVec b) τ₀) ^ 2 ≤
      2 * ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2 +
      8 * B ^ 2 * ∫ u, K u ∂uniformSphere (2 * n) := by
    intro M₃
    have h1 := hc (M₃.mulVec b)
    nlinarith [sq_nonneg ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
      2 * ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b) + ∫ x, φ x ∂cheapIn (M₃.mulVec b) τ₀)]
  have i1 : Integrable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      2 * ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2) P := ((BM.const 2).mul (bX.sub bY).sq).integrable P
  have i2 : Integrable (fun _ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      8 * B ^ 2 * ∫ u, K u ∂uniformSphere (2 * n)) P := integrable_const _
  have i12 : Integrable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      2 * ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2 +
      8 * B ^ 2 * ∫ u, K u ∂uniformSphere (2 * n)) P := i1.add i2
  have hmono := integral_mono ((bX.sub bZ).sq.integrable P) i12 hpt
  rw [integral_add i1 i2, integral_const_mul] at hmono
  simp only [integral_const, probReal_univ, one_smul] at hmono
  have h136 : ∫ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
      ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2 ∂P ≤
      99 / 100 / (n : ℝ) *
        ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b c]
          ∂cDist n (2 / (mW n : ℝ)) b := standIn136 hn hθ hφb
  linarith

/-- **The good inputs, for the scalar from one good input `u₁`.** For `θ ∈ good136 n`,
`u, u₁ ∈ G_ζ` and `ζ′ < wLow`: `tau1 u₁ > 0`, `λ(u) > 0`, and
`hellG n (σ(u)/λ(u)) (tau1 u₁) ≤ C1 n ζ·2((w(u) − w̄)² + (w(u₁) − w̄)²)`. -/
theorem good_pt1 {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) (hz : zetaP ζ < wLow)
    {u u₁ : Fin (2 * n) → ℝ} (hu : (u, θ) ∈ goodU (2 * n) (mW n) ζ)
    (hu₁ : (u₁, θ) ∈ goodU (2 * n) (mW n) ζ) :
    0 < tau1 (2 * n) (mW n) u₁ θ ∧ 0 < lam (hbarW θ) (hid2 θ.1 θ.2 u) ∧
      hellG n (sig (2 / (mW n : ℝ)) (hbarW θ) (hid2 θ.1 θ.2 u) /
          lam (hbarW θ) (hid2 θ.1 θ.2 u)) (tau1 (2 * n) (mW n) u₁ θ) ≤
        C1 n ζ * (2 * ((wn (2 * n) (mW n) u θ - wbar (2 * n) (mW n) θ) ^ 2 +
          (wn (2 * n) (mW n) u₁ θ - wbar (2 * n) (mW n) θ) ^ 2)) := by
  have hN : 1 ≤ 2 * n := by omega
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have hnpos : (0 : ℝ) < n := by
    have : (4096 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hul := hu.2
  have hlam : lamn (2 * n) (mW n) u θ = lam (hbarW θ) (hid2 θ.1 θ.2 u) := rfl
  simp only at hul
  rw [hlam] at hul
  set l := lam (hbarW θ) (hid2 θ.1 θ.2 u) with hl
  set s := sig (2 / (mW n : ℝ)) (hbarW θ) (hid2 θ.1 θ.2 u) with hs
  have hl0 : 0 < l := by
    have := abs_le.mp hul
    linarith
  have hs0 : 0 ≤ s := by rw [hs]; unfold sig; positivity
  set τ := s / l with hτ
  have hτ0 : 0 ≤ τ := div_nonneg hs0 hl0.le
  set K := 2 / (mW n : ℝ) * normSq (hbarW θ) with hK
  have hKpos : 0 < K := Kth_pos hn hθ
  set w := wn (2 * n) (mW n) u θ with hw
  set w₁ := wn (2 * n) (mW n) u₁ θ with hw₁
  set wb := wbar (2 * n) (mW n) θ with hwb
  have hτ2 : τ ^ 2 = K * w := by
    rw [hτ, div_pow]
    exact tau_sq_eq hN hm u (hbarW_ne hn hθ) (by rw [hlam]; exact hl0.ne')
  obtain ⟨hwb1, hwb2⟩ := wbar_window hn hθ
  have hz0 := zetaP_nonneg hζ0 hζ1
  have hclose : |w - wb| ≤ zetaP ζ := (wClose137 hn hζ1 (p := (u, θ)) ⟨hθ, hu⟩).1
  have hclose₁ : |w₁ - wb| ≤ zetaP ζ := (wClose137 hn hζ1 (p := (u₁, θ)) ⟨hθ, hu₁⟩).1
  have a := abs_le.mp hclose
  have a₁ := abs_le.mp hclose₁
  have hd : 0 < wLow - zetaP ζ := by linarith
  have hw₁lo : wLow - zetaP ζ ≤ w₁ := by linarith
  have hw₁0 : 0 < w₁ := by linarith
  have hw₁up : w₁ ≤ wUp + zetaP ζ := by
    have : wb ≤ wUp := hwb2
    linarith
  have hwlo : wLow - zetaP ζ ≤ w := by linarith
  have hmax : max 0 w₁ = w₁ := max_eq_right hw₁0.le
  have hτ1sq : tau1 (2 * n) (mW n) u₁ θ ^ 2 = K * w₁ := by
    unfold tau1
    rw [← hw₁, hmax]
    exact Real.sq_sqrt (mul_nonneg hKpos.le hw₁0.le)
  have hτ1pos : 0 < tau1 (2 * n) (mW n) u₁ θ := by
    unfold tau1
    rw [← hw₁, hmax]
    exact Real.sqrt_pos.mpr (mul_pos hKpos hw₁0)
  refine ⟨hτ1pos, hl0, ?_⟩
  have hUp : 0 < wUp + zetaP ζ := by have := wUp_pos; linarith
  have hr0 := rLow1_nonneg hζ0 hζ1 hz
  have hr : rLow1 ζ * w₁ ≤ w := by
    have h1 : rLow1 ζ * w₁ ≤ rLow1 ζ * (wUp + zetaP ζ) := mul_le_mul_of_nonneg_left hw₁up hr0
    have h2 : rLow1 ζ * (wUp + zetaP ζ) = wLow - zetaP ζ := by
      unfold rLow1
      field_simp
    linarith
  have hr2 : rLow1 ζ * tau1 (2 * n) (mW n) u₁ θ ^ 2 ≤ τ ^ 2 := by
    rw [hτ2, hτ1sq]
    have := mul_le_mul_of_nonneg_left hr hKpos.le
    linarith
  have h1 := hellG_le (by omega : 2 ≤ n) hτ0 hτ1pos
  have h2 := hell_ratio hτ0 hτ1pos hr0 hr2
  have hc := cRho1_pos hζ0 hζ1 hz
  have e4 : tau1 (2 * n) (mW n) u₁ θ ^ 4 = (K * w₁) ^ 2 := by
    rw [← hτ1sq]; ring
  have h3 : (τ ^ 2 - tau1 (2 * n) (mW n) u₁ θ ^ 2) ^ 2 /
      (tau1 (2 * n) (mW n) u₁ θ ^ 4 * ((1 + √(rLow1 ζ)) ^ 2 * (1 + rLow1 ζ))) =
      (w - w₁) ^ 2 / (w₁ ^ 2 * cRho1 ζ) := by
    rw [e4, hτ2, hτ1sq]
    unfold cRho1
    unfold cRho1 at hc
    field_simp
  have h4 : (w - w₁) ^ 2 / (w₁ ^ 2 * cRho1 ζ) ≤
      (w - w₁) ^ 2 / ((wLow - zetaP ζ) ^ 2 * cRho1 ζ) := by
    refine div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos (by positivity) hc) ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd.le hw₁lo 2) hc.le
  have h5 : (w - w₁) ^ 2 / ((wLow - zetaP ζ) ^ 2 * cRho1 ζ) ≤
      2 * ((w - wb) ^ 2 + (w₁ - wb) ^ 2) / ((wLow - zetaP ζ) ^ 2 * cRho1 ζ) := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    nlinarith [sq_nonneg ((w - wb) + (w₁ - wb))]
  calc hellG n τ (tau1 (2 * n) (mW n) u₁ θ)
      ≤ (n : ℝ) * (τ - tau1 (2 * n) (mW n) u₁ θ) ^ 2 /
          (τ ^ 2 + tau1 (2 * n) (mW n) u₁ θ ^ 2) := h1
    _ = (n : ℝ) * ((τ - tau1 (2 * n) (mW n) u₁ θ) ^ 2 /
          (τ ^ 2 + tau1 (2 * n) (mW n) u₁ θ ^ 2)) := by rw [mul_div_assoc]
    _ ≤ (n : ℝ) * (2 * ((w - wb) ^ 2 + (w₁ - wb) ^ 2) / ((wLow - zetaP ζ) ^ 2 * cRho1 ζ)) :=
      mul_le_mul_of_nonneg_left (((h2.trans (le_of_eq h3)).trans h4).trans h5) hnpos.le
    _ = _ := by unfold C1; ring

omit hn in
/-- On the good event: `K1fun ≤ 2·C1·Fsq + Fbad + 2·C1·d`. -/
lemma K1fun_le {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) (hz : zetaP ζ < wLow) {d : ℝ} (hd : 0 ≤ d)
    (u : Fin (2 * n) → ℝ) :
    K1fun n ζ d (u, θ) ≤ 2 * C1 n ζ * Fsq n ζ (u, θ) + Fbad n ζ (u, θ) + 2 * C1 n ζ * d := by
  have hC := C1_nonneg (n := n) hζ0 hζ1 hz
  unfold K1fun Fsq Fbad
  by_cases hp : (u, θ) ∈ goodU (2 * n) (mW n) ζ
  · have h1 : (u, θ) ∈ goodS (good136 n) ζ := ⟨hθ, hp⟩
    have h2 : (u, θ) ∉ badS n ζ := fun h => h.2 hp
    rw [Set.indicator_of_mem hp, Set.indicator_of_notMem (by simpa using hp),
      Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
    simp only
    linarith
  · have h1 : (u, θ) ∉ goodS (good136 n) ζ := fun h => hp h.2
    have h2 : (u, θ) ∈ badS n ζ := ⟨hθ, hp⟩
    rw [Set.indicator_of_notMem hp, Set.indicator_of_mem (by simpa using hp),
      Set.indicator_of_notMem h1, Set.indicator_of_mem h2]
    have : 0 ≤ 2 * C1 n ζ * d := by positivity
    linarith

omit hn hθ in
lemma K1fun_nonneg {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) (hz : zetaP ζ < wLow) {d : ℝ}
    (hd : 0 ≤ d) (p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) : 0 ≤ K1fun n ζ d p := by
  have hC := C1_nonneg (n := n) hζ0 hζ1 hz
  unfold K1fun
  refine add_nonneg (Set.indicator_nonneg (fun p _ => ?_) p)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) p)
  positivity

omit hθ in
lemma Fsq_le {ζ : ℝ} (hζ1 : ζ < 1) (u : Fin (2 * n) → ℝ) : Fsq n ζ (u, θ) ≤ zetaP ζ ^ 2 := by
  unfold Fsq
  by_cases hp : (u, θ) ∈ goodS (good136 n) ζ
  · rw [Set.indicator_of_mem hp]
    have hclose := (wClose137 hn hζ1 hp).1
    simp only
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hclose 2
  · rw [Set.indicator_of_notMem hp]; positivity

/-- `E_u K1fun ≤ Gm (2·C1) + 2·C1·d`, and `K1fun` is integrable in `u`. -/
lemma K1fun_int {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) (hz : zetaP ζ < wLow) {d : ℝ}
    (hd : 0 ≤ d) :
    Integrable (fun u => K1fun n ζ d (u, θ)) (uniformSphere (2 * n)) ∧
      ∫ u, K1fun n ζ d (u, θ) ∂uniformSphere (2 * n) ≤
        Gm n ζ (2 * C1 n ζ) θ + 2 * C1 n ζ * d := by
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  have hC := C1_nonneg (n := n) hζ0 hζ1 hz
  have hbd : ∀ u : Fin (2 * n) → ℝ,
      2 * C1 n ζ * Fsq n ζ (u, θ) + Fbad n ζ (u, θ) ≤ 2 * C1 n ζ * zetaP ζ ^ 2 + 1 := by
    intro u
    have h1 := mul_le_mul_of_nonneg_left (Fsq_le hn (θ := θ) hζ1 u)
      (by positivity : (0 : ℝ) ≤ 2 * C1 n ζ)
    have h2 := Fbad_le_one n ζ (u, θ)
    linarith
  have iK : Integrable (fun u => K1fun n ζ d (u, θ)) (uniformSphere (2 * n)) := by
    refine Integrable.of_bound ((measurable_K1fun (by omega) ζ d).comp
      measurable_prodMk_right).aestronglyMeasurable
      (2 * C1 n ζ * zetaP ζ ^ 2 + 1 + 2 * C1 n ζ * d) (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (K1fun_nonneg hζ0 hζ1 hz hd (u, θ))]
    have := K1fun_le hθ hζ0 hζ1 hz hd u
    have := hbd u
    linarith
  have iG : Integrable (fun u => 2 * C1 n ζ * Fsq n ζ (u, θ) + Fbad n ζ (u, θ))
      (uniformSphere (2 * n)) := by
    refine Integrable.of_bound ((((measurable_Fsq (by omega) ζ).const_mul _).add
      (measurable_Fbad (by omega) ζ)).comp measurable_prodMk_right).aestronglyMeasurable
      (2 * C1 n ζ * zetaP ζ ^ 2 + 1) (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (mul_nonneg (by positivity)
      (Fsq_nonneg n ζ _)) (Fbad_nonneg n ζ _))]
    exact hbd u
  have iGd : Integrable (fun u => 2 * C1 n ζ * Fsq n ζ (u, θ) + Fbad n ζ (u, θ) +
      2 * C1 n ζ * d) (uniformSphere (2 * n)) := iG.add (integrable_const _)
  refine ⟨iK, ?_⟩
  have h := integral_mono iK iGd (K1fun_le hθ hζ0 hζ1 hz hd)
  rw [integral_add iG (integrable_const _)] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  exact h

end fixed

/-! ## The joint theorem over `(u₁, M₁, M₂, M₃)` -/

section two

variable {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (hz : zetaP ζ < wLow)
  {φ : (Fin n → ℝ) → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, |φ x| ≤ B)

/-- The squared error of the cheap stand-in with the scalar from `u₁`, at
`q = ((u₁, (M₁, M₂)), M₃)`. -/
noncomputable def err2 (φ : (Fin n → ℝ) → ℝ)
    (q : ((Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) × Matrix (Fin n) (Fin (mW n)) ℝ) : ℝ :=
  ((∫ x, φ x ∂muWn ((q.1.2.1, q.1.2.2, q.2) : MlpParam (2 * n) (mW n) n)) -
    ∫ x, φ x ∂cheapIn (q.2.mulVec (hbarW q.1.2)) (tau1 (2 * n) (mW n) q.1.1 q.1.2)) ^ 2

/-- The good event of `(u₁, M₁, M₂, M₃)`: `(M₁, M₂) ∈ good136 n` and `u₁ ∈ G_ζ`. -/
def S1 (n : ℕ) (ζ : ℝ) :
    Set (((Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) × Matrix (Fin n) (Fin (mW n)) ℝ) :=
  {q | q.1 ∈ goodS (good136 n) ζ}

lemma bm_err2 (hn1 : 1 ≤ n) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) : BM (err2 (n := n) φ) := by
  have hN : 1 ≤ 2 * n := by omega
  have m1 : Measurable (fun q : ((Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) ×
      Matrix (Fin n) (Fin (mW n)) ℝ => ((q.1.2.1, q.1.2.2, q.2) : MlpParam (2 * n) (mW n) n)) :=
    (measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  have m2 : Measurable (fun q : ((Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) ×
      Matrix (Fin n) (Fin (mW n)) ℝ => q.2.mulVec (hbarW q.1.2)) :=
    measurable_mulVec_joint.comp (measurable_snd.prodMk
      ((measurable_hbarW hN).comp (measurable_snd.comp measurable_fst)))
  have m3 : Measurable (fun q : ((Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) ×
      Matrix (Fin n) (Fin (mW n)) ℝ => tau1 (2 * n) (mW n) q.1.1 q.1.2) :=
    (measurable_tau1 hN).comp measurable_fst
  exact (((bm_muW hN hφ).comp m1).sub (bm_cheapIn m2 m3 hφ)).sq

include hn hζ0 hζ1 hz hφ hB

/-- **The cheap stand-in with the scalar from one uniform input (item 5).** `u₁` is uniform on
the sphere and independent of `W = (M₁, M₂, M₃)`; `τ₀² = t|h̄|²·max(0, w(u₁))`. For `n ≥ 4096`,
`0 < ζ < 1` with `ζ′ < wLow`, and measurable `φ` with `|φ| ≤ B`:
`E[1_{good, u₁ ∈ G_ζ}·(E_{μ_W} φ − E_{ν′} φ)²] ≤
   2·(0.99/n)·E_W[1_good·Var_{ν_W} φ] + 8B²·EH1 n ζ`. -/
theorem cheapTwo138 :
    ∫ q, (S1 n ζ).indicator (err2 φ) q
        ∂(((uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n))).prod
          (gaussMat n (mW n) (2 / (mW n : ℝ)))) ≤
      2 * (99 / 100 / (n : ℝ) *
        ∫ W, (goodW n).indicator (fun W => Var[φ; nuW W]) W ∂mlpGauss (2 * n) (mW n) n) +
      8 * B ^ 2 * EH1 n ζ := by
  have hN : 1 ≤ 2 * n := by omega
  have hn1 : 1 ≤ n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  have hnpos : (0 : ℝ) < n := by
    have : (4096 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hφb : BM φ := ⟨hφ, B, hB⟩
  have hC := C1_nonneg (n := n) hζ0.le hζ1 hz
  set μP := (uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n)) with hμP
  set G3 := gaussMat n (mW n) (2 / (mW n : ℝ)) with hG3
  have mS : MeasurableSet (S1 n ζ) :=
    measurable_fst (goodS_meas hN (good136_meas hn1) ζ)
  have bI : BM ((S1 n ζ).indicator (err2 φ)) := bm_indicator mS (bm_err2 hn1 hφb)
  have mG := goodW_meas (n := n) hn1
  have b2 : BM ((goodW n).indicator (fun W => Var[φ; nuW W])) :=
    bm_indicator mG (bm_varW hN hφb)
  -- `R θ`: the stand-in variance on the good event, integrated over `M₃`
  set R : HidParam (2 * n) (mW n) → ℝ := fun θ =>
    ∫ M₃, (goodW n).indicator (fun W => Var[φ; nuW W]) (θ.1, θ.2, M₃) ∂G3 with hR
  have iR : Integrable R (hidGauss (2 * n) (mW n)) :=
    ((b2.comp MeasurableEquiv.prodAssoc.measurable).integral_right G3).integrable _
  have hR0 : ∀ θ, 0 ≤ R θ := fun θ => integral_nonneg fun M₃ =>
    Set.indicator_nonneg (fun W _ => variance_nonneg _ _) _
  obtain ⟨iGm, hGm⟩ := Gm_mean hn hζ0 hζ1 (C := 2 * C1 n ζ) (by positivity)
  obtain ⟨iFs, hFs⟩ := Fsq_int hn hζ0 hζ1
  rw [integral_prod _ (bI.integrable _)]
  -- pointwise in `p = (u₁, θ)`
  have hpt : ∀ p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n),
      ∫ M₃, (S1 n ζ).indicator (err2 φ) (p, M₃) ∂G3 ≤
        2 * (99 / 100 / (n : ℝ)) * R p.2 +
          8 * B ^ 2 * (Gm n ζ (2 * C1 n ζ) p.2 + 2 * C1 n ζ * Fsq n ζ p) := by
    intro p
    by_cases hp : p ∈ goodS (good136 n) ζ
    · obtain ⟨hθ, hu₁⟩ := hp
      have hq : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ, (p, M₃) ∈ S1 n ζ := fun M₃ => ⟨hθ, hu₁⟩
      have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ, (p.2.1, p.2.2, M₃) ∈ goodW n :=
        fun M₃ => hθ
      simp only [Set.indicator_of_mem (hq _)]
      set d : ℝ := (wn (2 * n) (mW n) p.1 p.2 - wbar (2 * n) (mW n) p.2) ^ 2 with hd
      have hd0 : 0 ≤ d := sq_nonneg _
      have hFd : Fsq n ζ p = d := by
        unfold Fsq
        rw [Set.indicator_of_mem (show p ∈ goodS (good136 n) ζ from ⟨hθ, hu₁⟩)]
      obtain ⟨iK, hKle⟩ := K1fun_int hn hθ hζ0.le hζ1 hz hd0
      have hτpos : 0 < tau1 (2 * n) (mW n) p.1 p.2 := by
        have := (good_pt1 hn hθ hζ0.le hζ1 hz (u := p.1) (u₁ := p.1) hu₁ hu₁).1
        exact this
      have hK : ∀ u : Fin (2 * n) → ℝ,
          (0 < lam (hbarW p.2) (hid2 p.2.1 p.2.2 u) ∧
            hellG n (sig (2 / (mW n : ℝ)) (hbarW p.2) (hid2 p.2.1 p.2.2 u) /
              lam (hbarW p.2) (hid2 p.2.1 p.2.2 u)) (tau1 (2 * n) (mW n) p.1 p.2) ≤
              K1fun n ζ d (u, p.2)) ∨ 1 ≤ K1fun n ζ d (u, p.2) := by
        intro u
        by_cases hu : (u, p.2) ∈ goodU (2 * n) (mW n) ζ
        · left
          obtain ⟨-, h2, h3⟩ := good_pt1 hn hθ hζ0.le hζ1 hz hu hu₁
          refine ⟨h2, ?_⟩
          unfold K1fun
          rw [Set.indicator_of_mem hu, Set.indicator_of_notMem (by simpa using hu), add_zero]
          exact h3
        · right
          unfold K1fun
          rw [Set.indicator_of_notMem hu, Set.indicator_of_mem (by simpa using hu), zero_add]
      have h := cheap_fixed hn hθ hτpos (K := fun u => K1fun n ζ d (u, p.2))
        ((measurable_K1fun hn1 ζ d).comp measurable_prodMk_right) iK hK hφ hB
      rw [← hG3] at h
      rw [← cDist_eq, ← hG3, integral_map (measurable_mulVec_right _).aemeasurable
        (bm_var_standIn (uniformSphere (2 * n)) _ _ (continuous_hid2 p.2.1 p.2.2).measurable
          hφb).meas.aestronglyMeasurable] at h
      have eR : R p.2 = ∫ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          Var[φ; standIn (uniformSphere (2 * n)) (hid2 p.2.1 p.2.2) (2 / (mW n : ℝ)) (hbarW p.2)
            (M₃.mulVec (hbarW p.2))] ∂G3 := by
        simp only [hR, Set.indicator_of_mem (hW _)]
        rfl
      rw [eR, hFd]
      have h2 := mul_le_mul_of_nonneg_left hKle (by positivity : (0 : ℝ) ≤ 8 * B ^ 2)
      have e : (2 : ℝ) * (99 / 100 / (n : ℝ)) *
          (∫ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
            Var[φ; standIn (uniformSphere (2 * n)) (hid2 p.2.1 p.2.2) (2 / (mW n : ℝ))
              (hbarW p.2) (M₃.mulVec (hbarW p.2))] ∂G3) =
          2 * (99 / 100 / (n : ℝ) *
            ∫ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
              Var[φ; standIn (uniformSphere (2 * n)) (hid2 p.2.1 p.2.2) (2 / (mW n : ℝ))
                (hbarW p.2) (M₃.mulVec (hbarW p.2))] ∂G3) := by ring
      rw [e]
      have h' : ∫ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ, err2 φ (p, M₃) ∂G3 ≤ _ := h
      linarith
    · have hq : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ, (p, M₃) ∉ S1 n ζ := fun M₃ => hp
      simp only [Set.indicator_of_notMem (hq _), integral_zero]
      have h1 := hR0 p.2
      have h2 := Gm_nonneg n ζ (by positivity : (0 : ℝ) ≤ 2 * C1 n ζ) p.2
      have h3 := Fsq_nonneg n ζ p
      positivity
  have j1 : Integrable (fun p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) =>
      2 * (99 / 100 / (n : ℝ)) * R p.2) μP := (iR.comp_snd _).const_mul _
  have j2 : Integrable (fun p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) =>
      Gm n ζ (2 * C1 n ζ) p.2) μP := iGm.comp_snd _
  have j3 : Integrable (fun p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) =>
      2 * C1 n ζ * Fsq n ζ p) μP := iFs.const_mul _
  have j23 : Integrable (fun p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) =>
      Gm n ζ (2 * C1 n ζ) p.2 + 2 * C1 n ζ * Fsq n ζ p) μP := j2.add j3
  have j4 : Integrable (fun p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) =>
      8 * B ^ 2 * (Gm n ζ (2 * C1 n ζ) p.2 + 2 * C1 n ζ * Fsq n ζ p)) μP := j23.const_mul _
  have j14 : Integrable (fun p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) =>
      2 * (99 / 100 / (n : ℝ)) * R p.2 +
        8 * B ^ 2 * (Gm n ζ (2 * C1 n ζ) p.2 + 2 * C1 n ζ * Fsq n ζ p)) μP := j1.add j4
  have hmono := integral_mono ((bI.integral_right G3).integrable μP) j14 hpt
  refine hmono.trans ?_
  rw [integral_add j1 j4, integral_const_mul, integral_const_mul, integral_add j2 j3,
    integral_const_mul, integral_fun_snd, integral_fun_snd, probReal_univ, one_smul, one_smul]
  have eW : ∫ θ, R θ ∂hidGauss (2 * n) (mW n) =
      ∫ W, (goodW n).indicator (fun W => Var[φ; nuW W]) W ∂mlpGauss (2 * n) (mW n) n :=
    (integral_mlp_split b2).symm
  rw [eW]
  have hB0 : (0 : ℝ) ≤ 8 * B ^ 2 := by positivity
  have h5 : ∫ θ, Gm n ζ (2 * C1 n ζ) θ ∂hidGauss (2 * n) (mW n) +
      2 * C1 n ζ * ∫ p, Fsq n ζ p ∂μP ≤ EH1 n ζ := by
    unfold EH1
    have := mul_le_mul_of_nonneg_left hFs (by positivity : (0 : ℝ) ≤ 2 * C1 n ζ)
    linarith
  have h6 := mul_le_mul_of_nonneg_left h5 hB0
  linarith

/-- **The tail form (item 5).** For `t > 0`, over `(u₁, M₁, M₂, M₃)`:
`Pr(|E_{μ_W} φ − E_{ν′} φ| ≥ t) ≤
   0.002 + Beta n ζ + (2·(0.99/n)·E_W Var_{ν_W} φ + 8B²·EH1 n ζ)/t²`. -/
theorem cheapTwo138_tail {t : ℝ} (ht : 0 < t) :
    (((uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n))).prod
          (gaussMat n (mW n) (2 / (mW n : ℝ)))).real {q | t ^ 2 ≤ err2 φ q} ≤
      2 / 1000 + Beta n ζ +
        (2 * (99 / 100 / (n : ℝ) * ∫ W, Var[φ; nuW W] ∂mlpGauss (2 * n) (mW n) n) +
          8 * B ^ 2 * EH1 n ζ) / t ^ 2 := by
  have hN : 1 ≤ 2 * n := by omega
  have hn1 : 1 ≤ n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  have hnpos : (0 : ℝ) < n := by
    have : (4096 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hφb : BM φ := ⟨hφ, B, hB⟩
  set μP := (uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n)) with hμP
  set G3 := gaussMat n (mW n) (2 / (mW n : ℝ)) with hG3
  set PP := μP.prod G3 with hPP
  have mE := good136_meas (n := n) hn1
  have mS : MeasurableSet (S1 n ζ) := measurable_fst (goodS_meas hN mE ζ)
  have bI : BM ((S1 n ζ).indicator (err2 φ)) := bm_indicator mS (bm_err2 hn1 hφb)
  have hg0 : ∀ q, 0 ≤ (S1 n ζ).indicator (err2 φ) q := fun q =>
    Set.indicator_nonneg (fun q _ => sq_nonneg _) q
  -- the complement of the good event
  set A1 : Set (((Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) ×
      Matrix (Fin n) (Fin (mW n)) ℝ) :=
    ((Set.univ : Set (Fin (2 * n) → ℝ)) ×ˢ (good136 n)ᶜ) ×ˢ Set.univ with hA1
  set A2 : Set (((Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) ×
      Matrix (Fin n) (Fin (mW n)) ℝ) := (badS n ζ) ×ˢ Set.univ with hA2
  have hsub : {q | t ^ 2 ≤ err2 φ q} ⊆ (A1 ∪ A2) ∪ {q | t ^ 2 ≤ (S1 n ζ).indicator (err2 φ) q} := by
    intro q hq
    by_cases hqS : q ∈ S1 n ζ
    · right
      change t ^ 2 ≤ (S1 n ζ).indicator (err2 φ) q
      rw [Set.indicator_of_mem hqS]
      exact hq
    · left
      by_cases hθ : q.1.2 ∈ good136 n
      · right
        refine ⟨⟨hθ, fun hu => hqS ⟨hθ, hu⟩⟩, Set.mem_univ _⟩
      · left
        exact ⟨⟨Set.mem_univ _, hθ⟩, Set.mem_univ _⟩
  have hA1 : PP.real A1 ≤ 2 / 1000 := by
    have e : PP.real A1 = (hidGauss (2 * n) (mW n)).real (good136 n)ᶜ := by
      simp only [hPP, hμP, hA1, Measure.real, Measure.prod_prod, measure_univ, one_mul, mul_one]
    rw [e, measureReal_compl mE, probReal_univ]
    have := good136_prob hn
    linarith
  have hA2 : PP.real A2 ≤ Beta n ζ := by
    have e : PP.real A2 = μP.real (badS n ζ) := by
      simp only [hPP, hA2, Measure.real, Measure.prod_prod, measure_univ, mul_one]
    rw [e]
    exact tauBad137 hn hζ0
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := PP) (f := (S1 n ζ).indicator (err2 φ))
    (Filter.Eventually.of_forall hg0) (bI.integrable PP) (t ^ 2)
  have e3 := var_ind_le hn hφ hB
  have e4 := cheapTwo138 hn hζ0 hζ1 hz hφ hB
  have e5 : 99 / 100 / (n : ℝ) *
      ∫ W, (goodW n).indicator (fun W => Var[φ; nuW W]) W ∂mlpGauss (2 * n) (mW n) n ≤
      99 / 100 / (n : ℝ) * ∫ W, Var[φ; nuW W] ∂mlpGauss (2 * n) (mW n) n :=
    mul_le_mul_of_nonneg_left e3 (by positivity)
  have ht2 : 0 < t ^ 2 := by positivity
  have h2 : PP.real {q | t ^ 2 ≤ (S1 n ζ).indicator (err2 φ) q} ≤
      (2 * (99 / 100 / (n : ℝ) * ∫ W, Var[φ; nuW W] ∂mlpGauss (2 * n) (mW n) n) +
        8 * B ^ 2 * EH1 n ζ) / t ^ 2 := by
    rw [le_div_iff₀ ht2]
    linarith
  calc PP.real {q | t ^ 2 ≤ err2 φ q}
      ≤ PP.real ((A1 ∪ A2) ∪ {q | t ^ 2 ≤ (S1 n ζ).indicator (err2 φ) q}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ PP.real (A1 ∪ A2) + PP.real {q | t ^ 2 ≤ (S1 n ζ).indicator (err2 φ) q} :=
        measureReal_union_le _ _
    _ ≤ (PP.real A1 + PP.real A2) + PP.real {q | t ^ 2 ≤ (S1 n ζ).indicator (err2 φ) q} :=
        add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ _ := by linarith

end two

/-! ## The explicit size at `ζ = 1/20` -/

lemma zetaP_lt : zetaP (1 / 20) < wLow := by
  unfold zetaP wLow
  norm_num

lemma rLow1_ge : 498 / 1000 ≤ rLow1 (1 / 20) := by
  unfold rLow1 zetaP wLow wUp
  norm_num

lemma cRho1_ge : 435 / 100 ≤ cRho1 (1 / 20) := by
  have hr := rLow1_ge
  have hs : 705 / 1000 ≤ √(rLow1 (1 / 20)) := by
    refine Real.le_sqrt_of_sq_le ?_
    refine le_trans ?_ hr
    norm_num
  unfold cRho1
  have h1 : ((1 : ℝ) + 705 / 1000) ^ 2 ≤ (1 + √(rLow1 (1 / 20))) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have h2 : (1 : ℝ) + 498 / 1000 ≤ 1 + rLow1 (1 / 20) := by linarith
  have h3 := mul_le_mul h1 h2 (by norm_num) (by positivity)
  refine le_trans ?_ h3
  norm_num

/-- **The explicit size of `EH1`**: `EH1 n (1/20) ≤ 5200·n/m` for `n ≥ 4096`. -/
theorem EH1_le {n : ℕ} (hn : 4096 ≤ n) : EH1 n (1 / 20) ≤ 5200 * (n : ℝ) / (mW n : ℝ) := by
  have hm6 : (1000000 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_million hn
  have hm0 : (0 : ℝ) < mW n := by linarith
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set x : ℝ := 1 / (mW n : ℝ) with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have h1 := Omega2_le hn
  have h2 := Beta_le hn
  rw [div_eq_mul_one_div (2623 : ℝ), ← hx] at h1
  rw [div_eq_mul_one_div (40700 : ℝ), ← hx] at h2
  have hc := cRho1_ge
  have hd : (0 : ℝ) < wLow - zetaP (1 / 20) := by linarith [zetaP_lt]
  have hk : C1 n (1 / 20) ≤ (n : ℝ) * (4944 / 10000) := by
    unfold C1
    have a1 : (n : ℝ) / ((wLow - zetaP (1 / 20)) ^ 2 * cRho1 (1 / 20)) ≤
        (n : ℝ) / ((wLow - zetaP (1 / 20)) ^ 2 * (435 / 100)) :=
      div_le_div_of_nonneg_left hn0.le (by positivity)
        (mul_le_mul_of_nonneg_left hc (by positivity))
    refine a1.trans ?_
    rw [div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ hn0.le
    unfold wLow zetaP
    norm_num
  have hO0 := Omega2_nonneg n (1 / 20)
  have hC0 : 0 ≤ C1 n (1 / 20) := C1_nonneg (by norm_num) (by norm_num) zetaP_lt
  have h3 : C1 n (1 / 20) * Omega2 n (1 / 20) ≤ (n : ℝ) * (4944 / 10000) * (2623 * x) :=
    mul_le_mul hk h1 hO0 (by positivity)
  unfold EH1
  rw [div_eq_mul_one_div (5200 * (n : ℝ)), ← hx]
  have h4 : 40700 * x ≤ 10 * (n : ℝ) * x := by
    refine mul_le_mul_of_nonneg_right ?_ hx0.le
    linarith
  have h5 : 0 ≤ (n : ℝ) * x := by positivity
  nlinarith

/-- **The tail form of item 5 with explicit terms** (`ζ = 1/20`): for `n ≥ 4096`, measurable `φ`
with `|φ| ≤ B` and `t > 0`, over `(u₁, M₁, M₂, M₃)`:
`Pr(|E_{μ_W} φ − E_{ν′} φ| ≥ t) ≤
   0.002 + 40700/m + (2·(0.99/n)·E_W Var_{ν_W} φ + 41600·B²·n/m)/t²`. -/
theorem cheapTwo138_tail_num {n : ℕ} (hn : 4096 ≤ n) {φ : (Fin n → ℝ) → ℝ} (hφ : Measurable φ)
    {B : ℝ} (hB : ∀ x, |φ x| ≤ B) {t : ℝ} (ht : 0 < t) :
    (((uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n))).prod
          (gaussMat n (mW n) (2 / (mW n : ℝ)))).real {q | t ^ 2 ≤ err2 φ q} ≤
      2 / 1000 + 40700 / (mW n : ℝ) +
        (2 * (99 / 100 / (n : ℝ) * ∫ W, Var[φ; nuW W] ∂mlpGauss (2 * n) (mW n) n) +
          41600 * B ^ 2 * ((n : ℝ) / (mW n : ℝ))) / t ^ 2 := by
  have h := cheapTwo138_tail hn (by norm_num : (0 : ℝ) < 1 / 20) (by norm_num) zetaP_lt hφ hB ht
  have h2 := mul_le_mul_of_nonneg_left (EH1_le hn) (by positivity : (0 : ℝ) ≤ 8 * B ^ 2)
  have e : 8 * B ^ 2 * (5200 * (n : ℝ) / (mW n : ℝ)) =
      41600 * B ^ 2 * ((n : ℝ) / (mW n : ℝ)) := by ring
  refine h.trans (add_le_add (add_le_add le_rfl (Beta_le hn))
    (div_le_div_of_nonneg_right ?_ (by positivity)))
  linarith

end BstLean.Part138

open BstLean.Part138 in
#print axioms cheap_fixed
open BstLean.Part138 in
#print axioms good_pt1
open BstLean.Part138 in
#print axioms cheapTwo138
open BstLean.Part138 in
#print axioms cheapTwo138_tail
open BstLean.Part138 in
#print axioms EH1_le
open BstLean.Part138 in
#print axioms cheapTwo138_tail_num
