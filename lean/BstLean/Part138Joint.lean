import BstLean.Part138Cheap

/-!
# Part 138, items 3 and 4: the cheap stand-in over the whole World network

Role: `delegations/statements/p138-spec.md`. Paper source: `onW16c-cx.md` §§4–5. The centre is
the exact mean hidden vector `h̄` (NOT the arithmetic centre of the programs).

* `cheapW W`: the cheap stand-in `ν′` of `W = (M₁, M₂, M₃)`: the distribution of
  `sphPt(M₃h̄ + τ₀γ)`, `τ₀² = t|h̄|²·w̄(M₁, M₂)`.
* `Omega2 n ζ`, `Beta n ζ`: the right sides of `tauFluct137` and `tauBad137` of Part 137
  (the paper's `ω_r²` and `β_r`).
* `EH n ζ = n·Omega2/(wLow²·cRho ζ) + Beta`: the bound of the mean of `Hbar` (the paper's `EH2`
  for a constant `τ₀`, in the convention `H² ≤ 1` on the bad inputs).
* **`Hbar_mean`**: `E_θ[1_good·Hbar n ζ θ] ≤ EH n ζ`.
* **`cheapStandIn138_joint`**: for `|φ| ≤ B`:
  `E_W[1_good·(E_{μ_W} φ − E_{ν′_W} φ)²] ≤ 2·(0.99/n)·E_W[1_good·Var_{ν_W} φ] + 8B²·EH n ζ`.
* `cheapStandIn138_total`: the same with no indicator, plus `0.008·B²`.
* **`cheapStandIn138_tail`** (item 4):
  `Pr_W(|E_{μ_W} φ − E_{ν′_W} φ| ≥ t) ≤ 0.002 + (2·(0.99/n)·E_W Var_{ν_W} φ + 8B²·EH n ζ)/t²`.
* `good138 n ζ p`, `good138_prob`, **`cheapStandIn138_event`**: an event of `(M₁, M₂)` of
  probability at least `0.998 − p` on which, for fixed `(M₁, M₂)`:
  `E_{M₃}(E_{μ_W} φ − E_{ν′} φ)² ≤ 2·(0.99/n)·E_c Var_{ν_c} φ + 8B²·EH n ζ/p`.
* File `Part138Num`: `EH n (1/20) ≤ 470·n/m` for `n ≥ 4096` (`EH_le`), and the joint and the
  tail form with the explicit second term `3760·B²·n/m`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part138

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137

/-! ## The cheap stand-in of `W` -/

section defs

variable {N m n : ℕ}

/-- **The cheap stand-in of the World network `W = (M₁, M₂, M₃)`**: the distribution of
`sphPt(M₃h̄ + τ₀γ)`, with the constant `τ₀² = t|h̄|²·w̄(M₁, M₂)`. -/
noncomputable def cheapW (W : MlpParam N m n) : Measure (Fin n → ℝ) :=
  cheapIn (W.2.2.mulVec (hbarW (W.1, W.2.1))) (tau0 N m (W.1, W.2.1))

lemma cheapW_prob (W : MlpParam N m n) : IsProbabilityMeasure (cheapW W) := cheapIn_prob _ _

lemma measurable_tau0 (hN : 1 ≤ N) : Measurable (tau0 N m) := by
  unfold tau0
  exact (((measurable_normSq.comp (measurable_hbarW hN)).const_mul _).mul
    (measurable_wbar hN)).sqrt

/-- `W ↦ E_{ν′_W} φ` is bounded and measurable. -/
lemma bm_cheapW (hN : 1 ≤ N) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    BM (fun W : MlpParam N m n => ∫ x, φ x ∂cheapW W) := by
  have hθ : Measurable (fun W : MlpParam N m n => ((W.1, W.2.1) : HidParam N m)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hc : Measurable (fun W : MlpParam N m n => W.2.2.mulVec (hbarW (W.1, W.2.1))) :=
    measurable_mulVec_joint.comp
      ((measurable_snd.comp measurable_snd).prodMk ((measurable_hbarW hN).comp hθ))
  exact bm_cheapIn hc ((measurable_tau0 hN).comp hθ) hφ

end defs

/-! ## The mean of `Hbar` on the good event -/

/-- The right side of `tauFluct137` (the paper's `ω_r²`). -/
noncomputable def Omega2 (n : ℕ) (ζ : ℝ) : ℝ :=
  (1 / (4936 / 10000 * (1 - ζ) ^ 2) *
    (√(10 / (mW n : ℝ) + 25 / (mW n : ℝ) ^ 2) +
      (2 + ζ) * (√(2235 / 100 / (mW n : ℝ)) / (4936 / 10000)))) ^ 2

/-- The right side of `tauBad137` (the paper's `β_r`). -/
noncomputable def Beta (n : ℕ) (ζ : ℝ) : ℝ :=
  (10 / (mW n : ℝ) + 25 / (mW n : ℝ) ^ 2 +
    2235 / 100 / (mW n : ℝ) / (4936 / 10000) ^ 2) / ζ ^ 2

/-- **`EH n ζ`**: the bound of `E_θ[1_good·Hbar]`: `n·ω_r²/(wLow²·cRho ζ) + β_r`. -/
noncomputable def EH (n : ℕ) (ζ : ℝ) : ℝ :=
  (n : ℝ) / (wLow ^ 2 * cRho ζ) * Omega2 n ζ + Beta n ζ

lemma Omega2_nonneg (n : ℕ) (ζ : ℝ) : 0 ≤ Omega2 n ζ := sq_nonneg _

lemma Beta_pos {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ : 0 < ζ) : 0 < Beta n ζ := by
  have hm : (0 : ℝ) < mW n := by
    have := mW_ge_million hn
    exact_mod_cast (by omega : 0 < mW n)
  unfold Beta
  positivity

lemma EH_pos {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ : 0 < ζ) : 0 < EH n ζ := by
  unfold EH
  have h1 := Beta_pos hn hζ
  have h2 := Omega2_nonneg n ζ
  have h3 := cRho_pos ζ
  have h4 := wLow_pos
  have : 0 ≤ (n : ℝ) / (wLow ^ 2 * cRho ζ) * Omega2 n ζ := by positivity
  linarith

section mean

variable {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)

include hn hζ0 hζ1

/-- **The mean of `Hbar` on the good event.** `θ ↦ 1_good(θ)·Hbar n ζ θ` is integrable, and
`E_θ[1_good·Hbar n ζ θ] ≤ EH n ζ`. -/
theorem Hbar_mean :
    Integrable ((good136 n).indicator (Hbar n ζ)) (hidGauss (2 * n) (mW n)) ∧
      ∫ θ, (good136 n).indicator (Hbar n ζ) θ ∂hidGauss (2 * n) (mW n) ≤ EH n ζ := by
  have hN : 1 ≤ 2 * n := by omega
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have := uniformSphere_isProbability (2 * n) hN
  have mE := good136_meas (n := n) (by omega)
  set μP := (uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n)) with hμP
  set C : ℝ := (n : ℝ) / (wLow ^ 2 * cRho ζ) with hC
  have hC0 : 0 ≤ C := by
    have := cRho_pos ζ
    have := wLow_pos
    rw [hC]; positivity
  set S := goodS (good136 n) ζ with hS
  set Bd : Set ((Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) :=
    {p | p.2 ∈ good136 n ∧ p ∉ goodU (2 * n) (mW n) ζ} with hBd
  have mS : MeasurableSet S := goodS_meas hN mE ζ
  have mBd : MeasurableSet Bd := (measurable_snd mE).inter (goodU_meas hN ζ).compl
  set F1 : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) → ℝ :=
    S.indicator (fun p => (wn (2 * n) (mW n) p.1 p.2 - wbar (2 * n) (mW n) p.2) ^ 2) with hF1
  set F2 : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) → ℝ :=
    Bd.indicator (fun _ => (1 : ℝ)) with hF2
  have iF1 : Integrable F1 μP := by
    have h := (tauFluct_gen hN hm mE (by norm_num : (0 : ℝ) < 4936 / 10000) hζ0.le hζ1
      (fun θ hθ => (Bn136 hn hθ).1)).int_sq
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    by_cases hp : p ∈ S
    · simp [hF1, Set.indicator_of_mem hp, Set.indicator_of_mem (hS ▸ hp)]
    · simp [hF1, Set.indicator_of_notMem hp, Set.indicator_of_notMem (hS ▸ hp)]
  have iF2 : Integrable F2 μP := (integrable_const (1 : ℝ)).indicator mBd
  have iF : Integrable (fun p => C * F1 p + F2 p) μP := (iF1.const_mul C).add iF2
  -- the pointwise identity
  have hpt : ∀ (θ : HidParam (2 * n) (mW n)) (u : Fin (2 * n) → ℝ),
      (good136 n).indicator (fun θ => Kfun n ζ (u, θ)) θ = C * F1 (u, θ) + F2 (u, θ) := by
    intro θ u
    by_cases hθ : θ ∈ good136 n
    · rw [Set.indicator_of_mem hθ]
      by_cases hp : (u, θ) ∈ goodU (2 * n) (mW n) ζ
      · have h1 : (u, θ) ∈ S := ⟨hθ, hp⟩
        have h2 : (u, θ) ∉ Bd := fun h => h.2 hp
        rw [Kfun_of_mem hp, hF1, hF2, Set.indicator_of_mem h1, Set.indicator_of_notMem h2,
          add_zero]
      · have h1 : (u, θ) ∉ S := fun h => hp h.2
        have h2 : (u, θ) ∈ Bd := ⟨hθ, hp⟩
        rw [Kfun_of_notMem hp, hF1, hF2, Set.indicator_of_notMem h1, Set.indicator_of_mem h2,
          mul_zero, zero_add]
    · have h1 : (u, θ) ∉ S := fun h => hθ h.1
      have h2 : (u, θ) ∉ Bd := fun h => hθ h.1
      rw [Set.indicator_of_notMem hθ, hF1, hF2, Set.indicator_of_notMem h1,
        Set.indicator_of_notMem h2, mul_zero, zero_add]
  have hfun : (good136 n).indicator (Hbar n ζ) =
      fun θ => ∫ u, (C * F1 (u, θ) + F2 (u, θ)) ∂uniformSphere (2 * n) := by
    funext θ
    simp_rw [← hpt θ]
    by_cases hθ : θ ∈ good136 n
    · simp only [Set.indicator_of_mem hθ]; rfl
    · simp [Set.indicator_of_notMem hθ]
  have hint : Integrable (fun θ => ∫ u, (C * F1 (u, θ) + F2 (u, θ)) ∂uniformSphere (2 * n))
      (hidGauss (2 * n) (mW n)) := iF.integral_prod_right
  refine ⟨by rw [hfun]; exact hint, ?_⟩
  rw [hfun, ← integral_prod_symm _ iF, integral_add (iF1.const_mul C) iF2, integral_const_mul]
  have h1 : ∫ p, F1 p ∂μP ≤ Omega2 n ζ := tauFluct137 hn hζ0.le hζ1
  have h2 : ∫ p, F2 p ∂μP ≤ Beta n ζ := by
    have e : ∫ p, F2 p ∂μP = μP.real Bd := by
      rw [hF2, integral_indicator mBd, setIntegral_const, smul_eq_mul, mul_one]
    rw [e]
    exact tauBad137 hn hζ0
  unfold EH
  have := mul_le_mul_of_nonneg_left h1 hC0
  linarith

end mean

/-! ## The joint theorem -/

section joint

variable {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
  {φ : (Fin n → ℝ) → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, |φ x| ≤ B)

include hn hζ0 hζ1 hφ hB

/-- **The cheap stand-in theorem over the whole World network, on the good event (item 3).**
For `n ≥ 4096`, `0 < ζ < 1` and measurable `φ` with `|φ| ≤ B`:
`E_W[1_good·(E_{μ_W} φ − E_{ν′_W} φ)²] ≤ 2·(0.99/n)·E_W[1_good·Var_{ν_W} φ] + 8B²·EH n ζ`. -/
theorem cheapStandIn138_joint :
    ∫ W, (goodW n).indicator
        (fun W => ((∫ x, φ x ∂muWn W) - ∫ x, φ x ∂cheapW W) ^ 2) W
        ∂mlpGauss (2 * n) (mW n) n ≤
      2 * (99 / 100 / (n : ℝ) *
        ∫ W, (goodW n).indicator (fun W => Var[φ; nuW W]) W ∂mlpGauss (2 * n) (mW n) n) +
      8 * B ^ 2 * EH n ζ := by
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  have hφb : BM φ := ⟨hφ, B, hB⟩
  have mG := goodW_meas (n := n) (by omega)
  have b1 : BM ((goodW n).indicator
      (fun W => ((∫ x, φ x ∂muWn W) - ∫ x, φ x ∂cheapW W) ^ 2)) :=
    bm_indicator mG ((bm_muW hN hφb).sub (bm_cheapW hN hφb)).sq
  have b2 : BM ((goodW n).indicator (fun W => Var[φ; nuW W])) :=
    bm_indicator mG (bm_varW hN hφb)
  obtain ⟨iH, hH⟩ := Hbar_mean hn hζ0 hζ1
  rw [integral_mlp_split b1, integral_mlp_split b2]
  have i1 := ((b1.comp MeasurableEquiv.prodAssoc.measurable).integral_right
    (gaussMat n (mW n) (2 / (mW n : ℝ)))).integrable (hidGauss (2 * n) (mW n))
  have i2 := ((b2.comp MeasurableEquiv.prodAssoc.measurable).integral_right
    (gaussMat n (mW n) (2 / (mW n : ℝ)))).integrable (hidGauss (2 * n) (mW n))
  have i4 : Integrable (fun θ : HidParam (2 * n) (mW n) =>
      2 * (99 / 100 / (n : ℝ)) *
        (∫ M₃, (goodW n).indicator (fun W => Var[φ; nuW W]) (θ.1, θ.2, M₃)
          ∂gaussMat n (mW n) (2 / (mW n : ℝ)))) (hidGauss (2 * n) (mW n)) := i2.const_mul _
  have i5 : Integrable (fun θ : HidParam (2 * n) (mW n) =>
      8 * B ^ 2 * (good136 n).indicator (Hbar n ζ) θ) (hidGauss (2 * n) (mW n)) :=
    iH.const_mul _
  have i3 : Integrable (fun θ : HidParam (2 * n) (mW n) =>
      2 * (99 / 100 / (n : ℝ)) *
        (∫ M₃, (goodW n).indicator (fun W => Var[φ; nuW W]) (θ.1, θ.2, M₃)
          ∂gaussMat n (mW n) (2 / (mW n : ℝ))) +
      8 * B ^ 2 * (good136 n).indicator (Hbar n ζ) θ) (hidGauss (2 * n) (mW n)) :=
    i4.add i5
  have hmono : ∫ θ, (∫ M₃, (goodW n).indicator
        (fun W => ((∫ x, φ x ∂muWn W) - ∫ x, φ x ∂cheapW W) ^ 2) (θ.1, θ.2, M₃)
        ∂gaussMat n (mW n) (2 / (mW n : ℝ))) ∂hidGauss (2 * n) (mW n) ≤
      ∫ θ, (2 * (99 / 100 / (n : ℝ)) *
        (∫ M₃, (goodW n).indicator (fun W => Var[φ; nuW W]) (θ.1, θ.2, M₃)
          ∂gaussMat n (mW n) (2 / (mW n : ℝ))) +
      8 * B ^ 2 * (good136 n).indicator (Hbar n ζ) θ) ∂hidGauss (2 * n) (mW n) := by
    refine integral_mono i1 i3 fun θ => ?_
    by_cases hθ : θ ∈ good136 n
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ, (θ.1, θ.2, M₃) ∈ goodW n := fun M₃ => hθ
      simp only [Set.indicator_of_mem (hW _), Set.indicator_of_mem hθ]
      have h := cheapStandIn138_bdd hn hθ hζ0.le hζ1 hφ hB
      rw [← cDist_eq, integral_map (measurable_mulVec_right _).aemeasurable
        (bm_var_standIn (uniformSphere (2 * n)) _ _ (continuous_hid2 θ.1 θ.2).measurable
          hφb).meas.aestronglyMeasurable] at h
      have e : (2 : ℝ) * (99 / 100 / (n : ℝ)) *
          (∫ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
            Var[φ; nuW ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)]
            ∂gaussMat n (mW n) (2 / (mW n : ℝ))) =
          2 * (99 / 100 / (n : ℝ) *
            ∫ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
              Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (hbarW θ)
                (M₃.mulVec (hbarW θ))] ∂gaussMat n (mW n) (2 / (mW n : ℝ))) := by
        rw [mul_assoc]
        rfl
      rw [e]
      exact h
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ, (θ.1, θ.2, M₃) ∉ goodW n := fun M₃ => hθ
      simp only [Set.indicator_of_notMem (hW _), Set.indicator_of_notMem hθ]
      simp
  refine hmono.trans ?_
  rw [integral_add i4 i5, integral_const_mul, integral_const_mul]
  have := mul_le_mul_of_nonneg_left hH (by positivity : (0 : ℝ) ≤ 8 * B ^ 2)
  linarith

omit hζ0 hζ1 hφ in
/-- The square of the error is at most `4B²`. -/
lemma cheap_err_le (W : MlpParam (2 * n) (mW n) n) :
    ((∫ x, φ x ∂muWn W) - ∫ x, φ x ∂cheapW W) ^ 2 ≤ 4 * B ^ 2 := by
  have hN : 1 ≤ 2 * n := by omega
  have := muWn_isProbability hN W
  have := cheapW_prob W
  have h1 := abs_integral_le_bound (muWn W) hB
  have h2 := abs_integral_le_bound (cheapW W) hB
  have h3 : |(∫ x, φ x ∂muWn W) - ∫ x, φ x ∂cheapW W| ≤ 2 * B := by
    have := abs_sub (∫ x, φ x ∂muWn W) (∫ x, φ x ∂cheapW W)
    linarith
  rw [← sq_abs]
  have := pow_le_pow_left₀ (abs_nonneg _) h3 2
  nlinarith

omit hζ0 hζ1 in
/-- `E_W[1_good·Var_{ν_W} φ] ≤ E_W Var_{ν_W} φ`. -/
lemma var_ind_le :
    ∫ W, (goodW n).indicator (fun W => Var[φ; nuW W]) W ∂mlpGauss (2 * n) (mW n) n ≤
      ∫ W, Var[φ; nuW W] ∂mlpGauss (2 * n) (mW n) n := by
  have hN : 1 ≤ 2 * n := by omega
  have hφb : BM φ := ⟨hφ, B, hB⟩
  have mG := goodW_meas (n := n) (by omega)
  have bV : BM (fun W : MlpParam (2 * n) (mW n) n => Var[φ; nuW W]) := bm_varW hN hφb
  refine integral_mono ((bm_indicator mG bV).integrable _) (bV.integrable _) fun W => ?_
  by_cases hW : W ∈ goodW n
  · rw [Set.indicator_of_mem hW]
  · rw [Set.indicator_of_notMem hW]; exact variance_nonneg _ _

/-- **The cheap stand-in theorem over the whole World network, total form.**
`E_W(E_{μ_W} φ − E_{ν′_W} φ)² ≤ 2·(0.99/n)·E_W Var_{ν_W} φ + 8B²·EH n ζ + 0.008·B²`. -/
theorem cheapStandIn138_total :
    ∫ W, ((∫ x, φ x ∂muWn W) - ∫ x, φ x ∂cheapW W) ^ 2 ∂mlpGauss (2 * n) (mW n) n ≤
      2 * (99 / 100 / (n : ℝ) * ∫ W, Var[φ; nuW W] ∂mlpGauss (2 * n) (mW n) n) +
        8 * B ^ 2 * EH n ζ + 8 / 1000 * B ^ 2 := by
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by
    have : (4096 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hφb : BM φ := ⟨hφ, B, hB⟩
  have mG := goodW_meas (n := n) (by omega)
  set P := mlpGauss (2 * n) (mW n) n with hP
  set f : MlpParam (2 * n) (mW n) n → ℝ :=
    fun W => ((∫ x, φ x ∂muWn W) - ∫ x, φ x ∂cheapW W) ^ 2 with hf
  have bf : BM f := ((bm_muW hN hφb).sub (bm_cheapW hN hφb)).sq
  have hf4 : ∀ W, f W ≤ 4 * B ^ 2 := cheap_err_le hn hB
  have hsplit : ∀ W, f W = (goodW n).indicator f W + (goodW n)ᶜ.indicator f W := fun W =>
    (congrFun (Set.indicator_self_add_compl (goodW n) f) W).symm
  have e1 : ∫ W, f W ∂P = ∫ W, (goodW n).indicator f W ∂P + ∫ W, (goodW n)ᶜ.indicator f W ∂P := by
    rw [← integral_add ((bm_indicator mG bf).integrable P)
      ((bm_indicator mG.compl bf).integrable P)]
    exact integral_congr_ae (Filter.Eventually.of_forall hsplit)
  have e2 : ∫ W, (goodW n)ᶜ.indicator f W ∂P ≤ 8 / 1000 * B ^ 2 := by
    have h1 : ∫ W, (goodW n)ᶜ.indicator f W ∂P ≤
        ∫ W, (goodW n)ᶜ.indicator (fun _ => 4 * B ^ 2) W ∂P := by
      refine integral_mono ((bm_indicator mG.compl bf).integrable P)
        ((integrable_const _).indicator mG.compl) fun W => ?_
      by_cases hW : W ∈ (goodW n)ᶜ
      · rw [Set.indicator_of_mem hW, Set.indicator_of_mem hW]; exact hf4 W
      · rw [Set.indicator_of_notMem hW, Set.indicator_of_notMem hW]
    have e : ∫ W, (goodW n)ᶜ.indicator (fun _ => 4 * B ^ 2) W ∂P =
        P.real (goodW n)ᶜ * (4 * B ^ 2) := by
      rw [integral_indicator mG.compl, setIntegral_const, smul_eq_mul]
    rw [e] at h1
    have h2 : P.real (goodW n)ᶜ ≤ 2 / 1000 := by
      rw [measureReal_compl mG, probReal_univ]
      have := goodW_prob hn
      linarith
    have h3 : P.real (goodW n)ᶜ * (4 * B ^ 2) ≤ 2 / 1000 * (4 * B ^ 2) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    linarith
  have e3 := var_ind_le hn hφ hB
  have e4 := cheapStandIn138_joint hn hζ0 hζ1 hφ hB
  have e5 : 99 / 100 / (n : ℝ) * ∫ W, (goodW n).indicator (fun W => Var[φ; nuW W]) W ∂P ≤
      99 / 100 / (n : ℝ) * ∫ W, Var[φ; nuW W] ∂P :=
    mul_le_mul_of_nonneg_left e3 (by positivity)
  rw [e1]
  linarith

/-- **The tail form (item 4).** For `t > 0`:
`Pr_W(|E_{μ_W} φ − E_{ν′_W} φ| ≥ t) ≤
  0.002 + (2·(0.99/n)·E_W Var_{ν_W} φ + 8B²·EH n ζ)/t²`. -/
theorem cheapStandIn138_tail {t : ℝ} (ht : 0 < t) :
    (mlpGauss (2 * n) (mW n) n).real
        {W | t ≤ |(∫ x, φ x ∂muWn W) - ∫ x, φ x ∂cheapW W|} ≤
      2 / 1000 +
        (2 * (99 / 100 / (n : ℝ) * ∫ W, Var[φ; nuW W] ∂mlpGauss (2 * n) (mW n) n) +
          8 * B ^ 2 * EH n ζ) / t ^ 2 := by
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by
    have : (4096 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hφb : BM φ := ⟨hφ, B, hB⟩
  have mG := goodW_meas (n := n) (by omega)
  set P := mlpGauss (2 * n) (mW n) n with hP
  set f : MlpParam (2 * n) (mW n) n → ℝ :=
    fun W => ((∫ x, φ x ∂muWn W) - ∫ x, φ x ∂cheapW W) ^ 2 with hf
  have bf : BM f := ((bm_muW hN hφb).sub (bm_cheapW hN hφb)).sq
  have bg : BM ((goodW n).indicator f) := bm_indicator mG bf
  have hg0 : ∀ W, 0 ≤ (goodW n).indicator f W := fun W =>
    Set.indicator_nonneg (fun W _ => sq_nonneg _) W
  have hsub : {W | t ≤ |(∫ x, φ x ∂muWn W) - ∫ x, φ x ∂cheapW W|} ⊆
      (goodW n)ᶜ ∪ {W | t ^ 2 ≤ (goodW n).indicator f W} := by
    intro W hW
    by_cases hWG : W ∈ goodW n
    · right
      have hW' : t ≤ |(∫ x, φ x ∂muWn W) - ∫ x, φ x ∂cheapW W| := hW
      change t ^ 2 ≤ (goodW n).indicator f W
      rw [Set.indicator_of_mem hWG]
      have := pow_le_pow_left₀ ht.le hW' 2
      simpa only [hf, sq_abs] using this
    · left
      exact hWG
  have h1 : P.real (goodW n)ᶜ ≤ 2 / 1000 := by
    rw [measureReal_compl mG, probReal_univ]
    have := goodW_prob hn
    linarith
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := (goodW n).indicator f)
    (Filter.Eventually.of_forall hg0) (bg.integrable P) (t ^ 2)
  have e3 := var_ind_le hn hφ hB
  have e4 := cheapStandIn138_joint hn hζ0 hζ1 hφ hB
  have e5 : 99 / 100 / (n : ℝ) * ∫ W, (goodW n).indicator (fun W => Var[φ; nuW W]) W ∂P ≤
      99 / 100 / (n : ℝ) * ∫ W, Var[φ; nuW W] ∂P :=
    mul_le_mul_of_nonneg_left e3 (by positivity)
  have ht2 : 0 < t ^ 2 := by positivity
  have h2 : P.real {W | t ^ 2 ≤ (goodW n).indicator f W} ≤
      (2 * (99 / 100 / (n : ℝ) * ∫ W, Var[φ; nuW W] ∂P) + 8 * B ^ 2 * EH n ζ) / t ^ 2 := by
    rw [le_div_iff₀ ht2]
    linarith
  calc P.real {W | t ≤ |(∫ x, φ x ∂muWn W) - ∫ x, φ x ∂cheapW W|}
      ≤ P.real ((goodW n)ᶜ ∪ {W | t ^ 2 ≤ (goodW n).indicator f W}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ P.real (goodW n)ᶜ + P.real {W | t ^ 2 ≤ (goodW n).indicator f W} :=
        measureReal_union_le _ _
    _ ≤ _ := add_le_add h1 h2

end joint

/-! ## An event of `(M₁, M₂)` with an explicit bound for fixed `(M₁, M₂)` -/

/-- **The good event of Part 138**: the good event of Part 136, and `Hbar n ζ θ ≤ EH n ζ/p`. -/
def good138 (n : ℕ) (ζ p : ℝ) : Set (HidParam (2 * n) (mW n)) :=
  {θ | θ ∈ good136 n ∧ Hbar n ζ θ ≤ EH n ζ / p}

/-- `Pr(good138 n ζ p) ≥ 0.998 − p`. -/
theorem good138_prob {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {p : ℝ}
    (hp : 0 < p) :
    998 / 1000 - p ≤ (hidGauss (2 * n) (mW n)).real (good138 n ζ p) := by
  set P := hidGauss (2 * n) (mW n) with hP
  have mE := good136_meas (n := n) (by omega)
  obtain ⟨iH, hH⟩ := Hbar_mean hn hζ0 hζ1
  have hEH := EH_pos hn hζ0
  have hf0 : ∀ θ, 0 ≤ (good136 n).indicator (Hbar n ζ) θ := fun θ =>
    Set.indicator_nonneg (fun θ _ => Hbar_nonneg n ζ θ) θ
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (f := (good136 n).indicator (Hbar n ζ)) (Filter.Eventually.of_forall hf0) iH (EH n ζ / p)
  have h1 : P.real {θ | EH n ζ / p ≤ (good136 n).indicator (Hbar n ζ) θ} ≤ p := by
    have h2 : EH n ζ / p * P.real {θ | EH n ζ / p ≤ (good136 n).indicator (Hbar n ζ) θ} ≤
        EH n ζ := hmark.trans hH
    rw [div_mul_eq_mul_div, div_le_iff₀ hp] at h2
    exact le_of_mul_le_mul_left h2 hEH
  have hcov : (Set.univ : Set (HidParam (2 * n) (mW n))) ⊆
      good138 n ζ p ∪ ((good136 n)ᶜ ∪
        {θ | EH n ζ / p ≤ (good136 n).indicator (Hbar n ζ) θ}) := by
    intro θ _
    by_cases hθ : θ ∈ good136 n
    · by_cases hh : Hbar n ζ θ ≤ EH n ζ / p
      · left; exact ⟨hθ, hh⟩
      · right; right
        change EH n ζ / p ≤ (good136 n).indicator (Hbar n ζ) θ
        rw [Set.indicator_of_mem hθ]
        exact (not_le.mp hh).le
    · right; left; exact hθ
  have h3 : P.real (good136 n)ᶜ ≤ 2 / 1000 := by
    rw [measureReal_compl mE, probReal_univ]
    have := good136_prob hn
    linarith
  have h4 : (1 : ℝ) ≤ P.real (good138 n ζ p) + (P.real (good136 n)ᶜ +
      P.real {θ | EH n ζ / p ≤ (good136 n).indicator (Hbar n ζ) θ}) := by
    have a1 := measureReal_mono (μ := P) hcov (measure_ne_top _ _)
    rw [probReal_univ] at a1
    have a2 := measureReal_union_le (μ := P) (good138 n ζ p) ((good136 n)ᶜ ∪
        {θ | EH n ζ / p ≤ (good136 n).indicator (Hbar n ζ) θ})
    have a3 := measureReal_union_le (μ := P) (good136 n)ᶜ
        {θ | EH n ζ / p ≤ (good136 n).indicator (Hbar n ζ) θ}
    linarith
  linarith

/-- **The cheap stand-in theorem for fixed `(M₁, M₂)`, with an explicit second term (item 3).**
For `n ≥ 4096`, `θ = (M₁, M₂) ∈ good138 n ζ p` and measurable `φ` with `|φ| ≤ B`, with the
expectation over `M₃`:
`E(E_{μ_W} φ − E_{ν′} φ)² ≤ 2·(0.99/n)·E_c Var_{ν_c} φ + 8B²·EH n ζ/p`. -/
theorem cheapStandIn138_event {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1)
    {p : ℝ} {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ good138 n ζ p)
    {φ : (Fin n → ℝ) → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, |φ x| ≤ B) :
    ∫ M₃, ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂cheapIn (M₃.mulVec (hbarW θ)) (tau0 (2 * n) (mW n) θ)) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)) ≤
      2 * (99 / 100 / (n : ℝ) *
        ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
          (hbarW θ) c] ∂cDist n (2 / (mW n : ℝ)) (hbarW θ)) +
      8 * B ^ 2 * (EH n ζ / p) := by
  have h := cheapStandIn138_bdd hn hθ.1 hζ0 hζ1 hφ hB
  have h2 := mul_le_mul_of_nonneg_left hθ.2 (by positivity : (0 : ℝ) ≤ 8 * B ^ 2)
  linarith

end BstLean.Part138

open BstLean.Part138 in
#print axioms Hbar_mean
open BstLean.Part138 in
#print axioms cheapStandIn138_joint
open BstLean.Part138 in
#print axioms cheapStandIn138_total
open BstLean.Part138 in
#print axioms cheapStandIn138_tail
open BstLean.Part138 in
#print axioms good138_prob
open BstLean.Part138 in
#print axioms cheapStandIn138_event
