import BstLean.Part160MFPR

/-!
# Part 160 (file `MFInt`): the mean-field lemma with the integrated remainder

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-05-centre.tex`, Lemma `t7:p05:MF` (change (C)).

Setting of `MFHyp` of Part 154 (a probability space `(Ω, μ)`, `f : Ω → ℝ^m`, hypotheses (M1),
(M2), (M3)). Two more numbers `ϰ, κ₃ > 0` and two tail masses:
`μ{ς² < s²/ϰ} ≤ π_HS`, `μ{|f|² < Γ_f/κ₃} ≤ π_f` (hypotheses of the lemma).

* `gauss_exp_sq`: `E exp(−κζ²) = 1/√(1 + 2κ)`.
* `YF_var_exp`: the variance term for a fixed `ā = a` with the remainder
  `K₀·E[𝖼²/(ςς′)·exp(−a²(β²/ς² + β′²/ς′²)/4)]`.
* `rem_int_le`: the remainder integrated over `ā ∼ N(0, Γ̄_f)` is at most
  `K₀·(‖H‖²_HS/√((s²/ϰ)(Γ_f/κ₃)) + 2s(√(s²/ϰ)·π_HS + √(Γ_f/κ₃)·π_f))`.
* `lemmaMF_int`: Lemma MF with this remainder term in the place of
  `2K₀‖H‖²_HS/s² + K₀√2·s²π_g`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (relu reluV normSq)
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm nrm_nonneg nrm_sq abs_dot_le_nrm)
open BstLean.Part131 (projMat projMat_mulVec stdGauss_decomp)
open BstLean.Part154

/-- `E exp(−κζ²) = 1/√(1 + 2κ)` for a standard Gaussian `ζ`, `κ ≥ 0`. -/
theorem gauss_exp_sq {κ : ℝ} (hκ : 0 ≤ κ) :
    ∫ ζ, rexp (-(κ * ζ ^ 2)) ∂gaussianReal 0 1 = (√(1 + 2 * κ))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have e : ∀ x : ℝ, gaussianPDFReal 0 1 x • rexp (-(κ * x ^ 2)) =
      (√(2 * π))⁻¹ * rexp (-(1 / 2 + κ) * x ^ 2) := by
    intro x
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [e]
  rw [integral_const_mul, integral_gaussian]
  have hp : (0 : ℝ) < π := Real.pi_pos
  rw [← Real.sqrt_inv, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {f : Ω → Fin m → ℝ} {ℓ πg : ℝ}

/-- The Gaussian factor of the remainder at `ā = a` for a pair of inputs. -/
noncomputable def eeF (μ : Measure Ω) (f : Ω → Fin m → ℝ) (a : ℝ) (p : Ω × Ω) : ℝ :=
  rexp (-((betaF μ f p.1 * a / nrm (gF μ f p.1)) ^ 2 +
    (betaF μ f p.2 * a / nrm (gF μ f p.2)) ^ 2) / 4)

lemma eeF_le_one (μ : Measure Ω) (f : Ω → Fin m → ℝ) (a : ℝ) (p : Ω × Ω) : eeF μ f a p ≤ 1 := by
  unfold eeF
  rw [← Real.exp_zero]
  refine Real.exp_le_exp.mpr ?_
  have : 0 ≤ (betaF μ f p.1 * a / nrm (gF μ f p.1)) ^ 2 +
    (betaF μ f p.2 * a / nrm (gF μ f p.2)) ^ 2 := by positivity
  linarith

lemma eeF_pos (μ : Measure Ω) (f : Ω → Fin m → ℝ) (a : ℝ) (p : Ω × Ω) : 0 < eeF μ f a p :=
  Real.exp_pos _

/-- Joint measurability of `(ζ, (ω, ω′)) ↦ 𝖼²/(ςς′)·exp(…)` at `ā = ζ·c`. -/
lemma meas_remF (H : MFHyp μ f ℓ πg) (c : ℝ) :
    Measurable (fun q : ℝ × (Ω × Ω) => rsF μ f q.2 * eeF μ f (q.1 * c) q.2) := by
  have hg1 : Measurable (fun q : ℝ × (Ω × Ω) => gF μ f q.2.1) :=
    H.meas_g.comp (measurable_fst.comp measurable_snd)
  have hg2 : Measurable (fun q : ℝ × (Ω × Ω) => gF μ f q.2.2) :=
    H.meas_g.comp (measurable_snd.comp measurable_snd)
  have hb1 : Measurable (fun q : ℝ × (Ω × Ω) => betaF μ f q.2.1) :=
    H.meas_beta.comp (measurable_fst.comp measurable_snd)
  have hb2 : Measurable (fun q : ℝ × (Ω × Ω) => betaF μ f q.2.2) :=
    H.meas_beta.comp (measurable_snd.comp measurable_snd)
  have hn1 : Measurable (fun q : ℝ × (Ω × Ω) => nrm (gF μ f q.2.1)) := meas_nrm.comp hg1
  have hn2 : Measurable (fun q : ℝ × (Ω × Ω) => nrm (gF μ f q.2.2)) := meas_nrm.comp hg2
  have ha : Measurable (fun q : ℝ × (Ω × Ω) => q.1 * c) := measurable_fst.mul_const c
  have hrs : Measurable (fun q : ℝ × (Ω × Ω) => rsF μ f q.2) :=
    ((meas_dotV hg1 hg2).pow_const 2).div (hn1.mul hn2)
  have hee : Measurable (fun q : ℝ × (Ω × Ω) => eeF μ f (q.1 * c) q.2) := by
    unfold eeF
    exact Real.measurable_exp.comp
      ((((((hb1.mul ha).div hn1).pow_const 2).add (((hb2.mul ha).div hn2).pow_const 2)).neg).div_const 4)
  exact hrs.mul hee

/-- **The variance term** for a fixed `a`, with the Gaussian factor in the remainder. -/
theorem YF_var_exp (H : MFHyp μ f ℓ πg) (a p0 : ℝ) :
    Integrable (fun z' => (YF μ f a z' - ∫ z'', YF μ f a z'' ∂stdGauss (Fin m)) ^ 2)
      (stdGauss (Fin m)) ∧
    Integrable (fun p : Ω × Ω => rsF μ f p * eeF μ f a p) (μ.prod μ) ∧
    ∫ z', (YF μ f a z' - ∫ z'', YF μ f a z'' ∂stdGauss (Fin m)) ^ 2 ∂stdGauss (Fin m) ≤
      ℓ ^ 2 * ∫ ω, (PhiG (betaF μ f ω * a / √(sig2F μ f ω)) - p0) ^ 2 ∂μ +
        K0 * ∫ p : Ω × Ω, rsF μ f p * eeF μ f a p ∂(μ.prod μ) := by
  obtain ⟨hYi, hψi, hEY⟩ := H.YF_mean a
  have hH := H.HInt a
  obtain ⟨hRi, -⟩ := H.rs_int
  obtain ⟨hT1i, hT1le⟩ := H.lin_int a p0
  have hREm : Measurable (fun p : Ω × Ω => rsF μ f p * eeF μ f a p) := by
    have h := (meas_remF H a).comp (measurable_prodMk_left (x := (1 : ℝ)))
    have e : ((fun q : ℝ × (Ω × Ω) => rsF μ f q.2 * eeF μ f (q.1 * a) q.2) ∘ Prod.mk 1) =
        fun p : Ω × Ω => rsF μ f p * eeF μ f a p := by
      funext p
      simp only [Function.comp, one_mul]
    rw [e] at h
    exact h
  have hREi : Integrable (fun p : Ω × Ω => rsF μ f p * eeF μ f a p) (μ.prod μ) :=
    Integrable.mono' hRi hREm.aestronglyMeasurable (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (rsF_bd μ f p).1 (eeF_pos μ f a p).le)]
      calc rsF μ f p * eeF μ f a p ≤ rsF μ f p * 1 :=
            mul_le_mul_of_nonneg_left (eeF_le_one μ f a p) (rsF_bd μ f p).1
        _ = rsF μ f p := mul_one _)
  generalize hE : (∫ z'', YF μ f a z'' ∂stdGauss (Fin m)) = EY at hEY ⊢
  have hY2 : ∀ z, YF μ f a z ^ 2 =
      ∫ p : Ω × Ω, rrF μ f a p.1 z * rrF μ f a p.2 z ∂(μ.prod μ) := fun z => by
    rw [sq]
    exact (integral_prod_mul (μ := μ) (ν := μ) (fun ω => rrF μ f a ω z)
      (fun ω => rrF μ f a ω z)).symm
  have hY2i : Integrable (fun z => YF μ f a z ^ 2) (stdGauss (Fin m)) :=
    hH.integral_prod_right.congr (ae_of_all _ fun z => (hY2 z).symm)
  have e : ∀ z, (YF μ f a z - EY) ^ 2 = YF μ f a z ^ 2 - 2 * EY * YF μ f a z + EY ^ 2 :=
    fun z => by ring
  have hint : Integrable (fun z => (YF μ f a z - EY) ^ 2) (stdGauss (Fin m)) :=
    ((hY2i.sub (hYi.const_mul (2 * EY))).add (integrable_const (EY ^ 2))).congr
      (ae_of_all _ fun z => (e z).symm)
  refine ⟨hint, hREi, ?_⟩
  have hvar : ∫ z, (YF μ f a z - EY) ^ 2 ∂stdGauss (Fin m) =
      ∫ z, YF μ f a z ^ 2 ∂stdGauss (Fin m) - EY ^ 2 := by
    have hA : Integrable (fun z => YF μ f a z ^ 2 - 2 * EY * YF μ f a z) (stdGauss (Fin m)) :=
      hY2i.sub (hYi.const_mul (2 * EY))
    rw [integral_congr_ae (ae_of_all _ e), integral_add hA (integrable_const (EY ^ 2)),
      integral_sub hY2i (hYi.const_mul (2 * EY)), integral_const_mul, integral_const, hE]
    simp
    ring
  have hψψ : Integrable (fun p : Ω × Ω => psF μ f a p.1 * psF μ f a p.2) (μ.prod μ) :=
    hψi.mul_prod hψi
  have hE2 : EY ^ 2 = ∫ p : Ω × Ω, psF μ f a p.1 * psF μ f a p.2 ∂(μ.prod μ) := by
    rw [sq, hEY]
    exact (integral_prod_mul (μ := μ) (ν := μ) (fun ω => psF μ f a ω)
      (fun ω => psF μ f a ω)).symm
  have hCi : Integrable (fun p : Ω × Ω =>
      ∫ z, rrF μ f a p.1 z * rrF μ f a p.2 z ∂stdGauss (Fin m)) (μ.prod μ) :=
    hH.integral_prod_left
  have hsw : ∫ z, YF μ f a z ^ 2 ∂stdGauss (Fin m) =
      ∫ p : Ω × Ω, ∫ z, rrF μ f a p.1 z * rrF μ f a p.2 z ∂stdGauss (Fin m) ∂(μ.prod μ) := by
    rw [integral_congr_ae (ae_of_all _ hY2)]
    exact (integral_integral_swap
      (f := fun (p : Ω × Ω) (z : Fin m → ℝ) => rrF μ f a p.1 z * rrF μ f a p.2 z) hH).symm
  have hV : ∫ z, (YF μ f a z - EY) ^ 2 ∂stdGauss (Fin m) =
      ∫ p : Ω × Ω, (∫ z, rrF μ f a p.1 z * rrF μ f a p.2 z ∂stdGauss (Fin m) -
        psF μ f a p.1 * psF μ f a p.2) ∂(μ.prod μ) := by
    rw [hvar, hsw, hE2, integral_sub hCi hψψ]
  have hpt : ∀ p : Ω × Ω, ∫ z, rrF μ f a p.1 z * rrF μ f a p.2 z ∂stdGauss (Fin m) -
        psF μ f a p.1 * psF μ f a p.2 ≤
      ccF μ f p * ppF μ f a p.1 * ppF μ f a p.2 + K0 * (rsF μ f p * eeF μ f a p) := fun p => by
    have h := PRvec_exp m (gF μ f p.1) (gF μ f p.2) (betaF μ f p.1 * a) (betaF μ f p.2 * a)
    have e2 : ccF μ f p ^ 2 / (nrm (gF μ f p.1) * nrm (gF μ f p.2)) *
        (K0 * rexp (-((betaF μ f p.1 * a / nrm (gF μ f p.1)) ^ 2 +
          (betaF μ f p.2 * a / nrm (gF μ f p.2)) ^ 2) / 4)) =
        K0 * (rsF μ f p * eeF μ f a p) := by
      unfold eeF; ring
    rw [← e2]
    exact h
  rw [hV]
  calc ∫ p : Ω × Ω, (∫ z, rrF μ f a p.1 z * rrF μ f a p.2 z ∂stdGauss (Fin m) -
        psF μ f a p.1 * psF μ f a p.2) ∂(μ.prod μ)
      ≤ ∫ p : Ω × Ω, (ccF μ f p * ppF μ f a p.1 * ppF μ f a p.2 +
          K0 * (rsF μ f p * eeF μ f a p)) ∂(μ.prod μ) :=
        integral_mono (hCi.sub hψψ) (hT1i.add (hREi.const_mul K0)) hpt
    _ = ∫ p : Ω × Ω, ccF μ f p * ppF μ f a p.1 * ppF μ f a p.2 ∂(μ.prod μ) +
          K0 * ∫ p : Ω × Ω, rsF μ f p * eeF μ f a p ∂(μ.prod μ) := by
        rw [integral_add hT1i (hREi.const_mul K0), integral_const_mul]
    _ ≤ _ := add_le_add hT1le le_rfl

/-- The pointwise bound of the integrated remainder on a pair of good inputs. -/
lemma rem_point {c s1 s2 b1 b2 Gb A B f1 f2 : ℝ} (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) (hGb : 0 ≤ Gb)
    (hf1 : f1 = b1 ^ 2 * Gb + s1 ^ 2) (hf2 : f2 = b2 ^ 2 * Gb + s2 ^ 2) (hA : 0 < A) (hB : 0 < B)
    (h1 : A ≤ s1 ^ 2) (h2 : A ≤ s2 ^ 2) (h3 : B ≤ f1) (h4 : B ≤ f2) :
    c ^ 2 / (s1 * s2) * (√(1 + 2 * (Gb * ((b1 / s1) ^ 2 + (b2 / s2) ^ 2) / 4)))⁻¹ ≤
      c ^ 2 / √(A * B) := by
  have hs1p : 0 < s1 := by
    rcases hs1.eq_or_lt with e | e
    · rw [← e] at h1; norm_num at h1; linarith
    · exact e
  have hs2p : 0 < s2 := by
    rcases hs2.eq_or_lt with e | e
    · rw [← e] at h2; norm_num at h2; linarith
    · exact e
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 1 + 2 * (Gb * ((b1 / s1) ^ 2 + (b2 / s2) ^ 2) / 4) := ⟨_, rfl⟩
  rw [← hR]
  have hR1 : 1 ≤ R := by
    rw [hR]
    have : 0 ≤ Gb * ((b1 / s1) ^ 2 + (b2 / s2) ^ 2) := mul_nonneg hGb (by positivity)
    linarith
  have hsR : 0 < √R := Real.sqrt_pos.mpr (by linarith)
  have hD2 : A * B ≤ (s1 * s2 * √R) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    have e : (s1 * s2) ^ 2 * R = (f1 * s2 ^ 2 + f2 * s1 ^ 2) / 2 := by
      rw [hR, hf1, hf2]; field_simp; ring
    rw [e]
    have t1 : B * A ≤ f1 * s2 ^ 2 := mul_le_mul h3 h2 hA.le (hB.le.trans h3)
    have t2 : B * A ≤ f2 * s1 ^ 2 := mul_le_mul h4 h1 hA.le (hB.le.trans h4)
    linarith
  have hD0 : 0 < s1 * s2 * √R := by positivity
  have hAB : 0 < √(A * B) := Real.sqrt_pos.mpr (mul_pos hA hB)
  have hle : √(A * B) ≤ s1 * s2 * √R := by
    rw [← Real.sqrt_sq hD0.le]
    exact Real.sqrt_le_sqrt hD2
  have e : c ^ 2 / (s1 * s2) * (√R)⁻¹ = c ^ 2 / (s1 * s2 * √R) := by
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_left (sq_nonneg c) hAB hle

omit [IsProbabilityMeasure μ] in
lemma GamF_pos (H : MFHyp μ f ℓ πg) : 0 < GamF μ f := by
  have h1 := H.hs
  have h2 := H.hbar
  unfold sF2 at h1
  linarith

/-- **The remainder integrated over `ā ∼ N(0, Γ̄_f)`** (Lemma `t7:p05:MF`, the first two terms):
with `μ{ς² < s²/ϰ} ≤ π_HS` and `μ{|f|² < Γ_f/κ₃} ≤ π_f`,
`E_ζ E[𝖼²/(ςς′)·exp(…)] ≤ ‖H‖²_HS/√((s²/ϰ)(Γ_f/κ₃)) + 2s(√(s²/ϰ)π_HS + √(Γ_f/κ₃)π_f)`. -/
theorem rem_int_le (H : MFHyp μ f ℓ πg) {kap kap3 piHS pif : ℝ} (hk : 0 < kap) (hk3 : 0 < kap3)
    (hHS : μ.real {ω | sig2F μ f ω < sF2 μ f / kap} ≤ piHS)
    (hf : μ.real {ω | normSq (f ω) < GamF μ f / kap3} ≤ pif) :
    Integrable (fun ζ : ℝ => ∫ p : Ω × Ω, rsF μ f p * eeF μ f (ζ * √(GamBarF μ f)) p ∂(μ.prod μ))
      (gaussianReal 0 1) ∧
    ∫ ζ, (∫ p : Ω × Ω, rsF μ f p * eeF μ f (ζ * √(GamBarF μ f)) p ∂(μ.prod μ))
        ∂gaussianReal 0 1 ≤
      hsF μ f / √(sF2 μ f / kap * (GamF μ f / kap3)) +
        2 * sF μ f * (√(sF2 μ f / kap) * piHS + √(GamF μ f / kap3) * pif) := by
  classical
  obtain ⟨hRi, -⟩ := H.rs_int
  obtain ⟨hs0, hs2⟩ := H.sF_pos
  obtain ⟨hsg, hsle, -⟩ := H.sig_int
  obtain ⟨hc2i, hc2le⟩ := H.F4c
  have hΓb := H.hbar
  have hΓ := GamF_pos H
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = √(GamBarF μ f) := ⟨_, rfl⟩
  have hc2 : c ^ 2 = GamBarF μ f := by rw [hc]; exact Real.sq_sqrt hΓb.le
  rw [← hc]
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = sF2 μ f / kap := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = GamF μ f / kap3 := ⟨_, rfl⟩
  rw [← hA] at hHS ⊢
  rw [← hB] at hf ⊢
  have hA0 : 0 < A := by rw [hA]; exact div_pos H.hs hk
  have hB0 : 0 < B := by rw [hB]; exact div_pos hΓ hk3
  -- Fubini
  have hFm := meas_remF H c
  have hFi : Integrable (fun q : ℝ × (Ω × Ω) => rsF μ f q.2 * eeF μ f (q.1 * c) q.2)
      ((gaussianReal 0 1).prod (μ.prod μ)) := by
    refine Integrable.mono' (hRi.comp_snd (gaussianReal 0 1)) hFm.aestronglyMeasurable
      (ae_of_all _ fun q => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (rsF_bd μ f q.2).1 (eeF_pos μ f _ q.2).le)]
    calc rsF μ f q.2 * eeF μ f (q.1 * c) q.2 ≤ rsF μ f q.2 * 1 :=
          mul_le_mul_of_nonneg_left (eeF_le_one μ f _ q.2) (rsF_bd μ f q.2).1
      _ = rsF μ f q.2 := mul_one _
  refine ⟨hFi.integral_prod_left, ?_⟩
  rw [integral_integral_swap (f := fun (ζ : ℝ) (p : Ω × Ω) => rsF μ f p * eeF μ f (ζ * c) p) hFi]
  -- the inner Gaussian integral
  have hin : ∀ p : Ω × Ω, ∫ ζ, rsF μ f p * eeF μ f (ζ * c) p ∂gaussianReal 0 1 =
      rsF μ f p * (√(1 + 2 * (GamBarF μ f * ((betaF μ f p.1 / nrm (gF μ f p.1)) ^ 2 +
        (betaF μ f p.2 / nrm (gF μ f p.2)) ^ 2) / 4)))⁻¹ := by
    intro p
    rw [integral_const_mul]
    congr 1
    have e : ∀ ζ : ℝ, eeF μ f (ζ * c) p =
        rexp (-((GamBarF μ f * ((betaF μ f p.1 / nrm (gF μ f p.1)) ^ 2 +
          (betaF μ f p.2 / nrm (gF μ f p.2)) ^ 2) / 4) * ζ ^ 2)) := by
      intro ζ
      unfold eeF
      congr 1
      rw [← hc2]; ring
    simp_rw [e]
    exact gauss_exp_sq (by positivity)
  simp_rw [hin]
  -- the bad set
  set Bd : Set Ω := {ω | sig2F μ f ω < A} ∪ {ω | normSq (f ω) < B} with hBd
  have hB1 : MeasurableSet {ω | sig2F μ f ω < A} := measurableSet_lt H.meas_sig measurable_const
  have hB2 : MeasurableSet {ω | normSq (f ω) < B} :=
    measurableSet_lt (BstLean.Part130.measurable_normSq.comp H.hf) measurable_const
  have hBm : MeasurableSet Bd := hB1.union hB2
  have hiB : Integrable (fun ω => Bd.indicator (fun ω => sgF μ f ω) ω) μ := hsg.indicator hBm
  have hind0 : ∀ ω, 0 ≤ Bd.indicator (fun ω => sgF μ f ω) ω := fun ω =>
    Set.indicator_nonneg (fun _ _ => nrm_nonneg _) _
  have hpt : ∀ p : Ω × Ω, rsF μ f p * (√(1 + 2 * (GamBarF μ f *
        ((betaF μ f p.1 / nrm (gF μ f p.1)) ^ 2 +
        (betaF μ f p.2 / nrm (gF μ f p.2)) ^ 2) / 4)))⁻¹ ≤
      1 / √(A * B) * ccF μ f p ^ 2 +
        (Bd.indicator (fun ω => sgF μ f ω) p.1 * sgF μ f p.2 +
          sgF μ f p.1 * Bd.indicator (fun ω => sgF μ f ω) p.2) := by
    intro p
    have t0 : 0 ≤ 1 / √(A * B) * ccF μ f p ^ 2 := by positivity
    have hle := (rsF_bd μ f p).2
    have h0 := (rsF_bd μ f p).1
    have s1 : 0 ≤ sgF μ f p.1 := nrm_nonneg _
    have s2 : 0 ≤ sgF μ f p.2 := nrm_nonneg _
    have i1 := hind0 p.1
    have i2 := hind0 p.2
    have hinv : (√(1 + 2 * (GamBarF μ f * ((betaF μ f p.1 / nrm (gF μ f p.1)) ^ 2 +
        (betaF μ f p.2 / nrm (gF μ f p.2)) ^ 2) / 4)))⁻¹ ≤ 1 := by
      have h1 : (1 : ℝ) ≤ 1 + 2 * (GamBarF μ f * ((betaF μ f p.1 / nrm (gF μ f p.1)) ^ 2 +
          (betaF μ f p.2 / nrm (gF μ f p.2)) ^ 2) / 4) := by
        have : 0 ≤ GamBarF μ f * ((betaF μ f p.1 / nrm (gF μ f p.1)) ^ 2 +
          (betaF μ f p.2 / nrm (gF μ f p.2)) ^ 2) := mul_nonneg hΓb.le (by positivity)
        linarith
      have h2 : (1 : ℝ) ≤ √(1 + 2 * (GamBarF μ f * ((betaF μ f p.1 / nrm (gF μ f p.1)) ^ 2 +
          (betaF μ f p.2 / nrm (gF μ f p.2)) ^ 2) / 4)) := Real.one_le_sqrt.mpr h1
      exact inv_le_one_of_one_le₀ h2
    have hcrude : rsF μ f p * (√(1 + 2 * (GamBarF μ f *
        ((betaF μ f p.1 / nrm (gF μ f p.1)) ^ 2 +
        (betaF μ f p.2 / nrm (gF μ f p.2)) ^ 2) / 4)))⁻¹ ≤ sgF μ f p.1 * sgF μ f p.2 :=
      (mul_le_of_le_one_right h0 hinv).trans hle
    by_cases h1 : p.1 ∈ Bd
    · rw [Set.indicator_of_mem h1]
      have := mul_nonneg s1 i2
      linarith
    by_cases h2 : p.2 ∈ Bd
    · rw [Set.indicator_of_mem h2]
      have := mul_nonneg i1 s2
      linarith
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    simp only [zero_mul, mul_zero, add_zero]
    have a1 : A ≤ nrm (gF μ f p.1) ^ 2 := by
      rw [nrm_sq]; exact not_lt.1 fun h => h1 (Or.inl h)
    have a2 : A ≤ nrm (gF μ f p.2) ^ 2 := by
      rw [nrm_sq]; exact not_lt.1 fun h => h2 (Or.inl h)
    have b1 : B ≤ normSq (f p.1) := not_lt.1 fun h => h1 (Or.inr h)
    have b2 : B ≤ normSq (f p.2) := not_lt.1 fun h => h2 (Or.inr h)
    have e1 : normSq (f p.1) = betaF μ f p.1 ^ 2 * GamBarF μ f + nrm (gF μ f p.1) ^ 2 := by
      rw [nrm_sq]; exact H.normSq_split p.1
    have e2 : normSq (f p.2) = betaF μ f p.2 ^ 2 * GamBarF μ f + nrm (gF μ f p.2) ^ 2 := by
      rw [nrm_sq]; exact H.normSq_split p.2
    have key := rem_point (c := ccF μ f p) (nrm_nonneg (gF μ f p.1)) (nrm_nonneg (gF μ f p.2))
      hΓb.le e1 e2 hA0 hB0 a1 a2 b1 b2
    calc _ ≤ ccF μ f p ^ 2 / √(A * B) := key
      _ = 1 / √(A * B) * ccF μ f p ^ 2 := by ring
  have hU1 : Integrable (fun p : Ω × Ω => 1 / √(A * B) * ccF μ f p ^ 2) (μ.prod μ) :=
    hc2i.const_mul _
  have hU2 : Integrable (fun p : Ω × Ω => Bd.indicator (fun ω => sgF μ f ω) p.1 * sgF μ f p.2)
      (μ.prod μ) := hiB.mul_prod hsg
  have hU3 : Integrable (fun p : Ω × Ω => sgF μ f p.1 * Bd.indicator (fun ω => sgF μ f ω) p.2)
      (μ.prod μ) := hsg.mul_prod hiB
  have hLi : Integrable (fun p : Ω × Ω => rsF μ f p * (√(1 + 2 * (GamBarF μ f *
        ((betaF μ f p.1 / nrm (gF μ f p.1)) ^ 2 +
        (betaF μ f p.2 / nrm (gF μ f p.2)) ^ 2) / 4)))⁻¹) (μ.prod μ) :=
    (hFi.integral_prod_right).congr (ae_of_all _ hin)
  -- the integral of `ς` on the bad set
  have hIB0 : 0 ≤ ∫ ω, Bd.indicator (fun ω => sgF μ f ω) ω ∂μ := integral_nonneg hind0
  have hIS0 : 0 ≤ ∫ ω, sgF μ f ω ∂μ := integral_nonneg fun ω => nrm_nonneg _
  have hI1 : ∫ ω in {ω | sig2F μ f ω < A}, sgF μ f ω ∂μ ≤ √A * piHS := by
    calc ∫ ω in {ω | sig2F μ f ω < A}, sgF μ f ω ∂μ
        ≤ ∫ ω in {ω | sig2F μ f ω < A}, √A ∂μ :=
          setIntegral_mono_on hsg.integrableOn (integrable_const _).integrableOn hB1
            (fun ω hω => Real.sqrt_le_sqrt (le_of_lt hω))
      _ = μ.real {ω | sig2F μ f ω < A} * √A := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ piHS * √A := mul_le_mul_of_nonneg_right hHS (Real.sqrt_nonneg _)
      _ = √A * piHS := mul_comm _ _
  have hI2 : ∫ ω in {ω | normSq (f ω) < B}, sgF μ f ω ∂μ ≤ √B * pif := by
    calc ∫ ω in {ω | normSq (f ω) < B}, sgF μ f ω ∂μ
        ≤ ∫ ω in {ω | normSq (f ω) < B}, √B ∂μ :=
          setIntegral_mono_on hsg.integrableOn (integrable_const _).integrableOn hB2
            (fun ω hω => Real.sqrt_le_sqrt ((H.sig_le ω).trans (le_of_lt hω)))
      _ = μ.real {ω | normSq (f ω) < B} * √B := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ pif * √B := mul_le_mul_of_nonneg_right hf (Real.sqrt_nonneg _)
      _ = √B * pif := mul_comm _ _
  have hIBle : ∫ ω, Bd.indicator (fun ω => sgF μ f ω) ω ∂μ ≤ √A * piHS + √B * pif := by
    have hpw : ∀ ω, Bd.indicator (fun ω => sgF μ f ω) ω ≤
        ({ω | sig2F μ f ω < A} : Set Ω).indicator (fun ω => sgF μ f ω) ω +
          ({ω | normSq (f ω) < B} : Set Ω).indicator (fun ω => sgF μ f ω) ω := by
      intro ω
      have s0 : 0 ≤ sgF μ f ω := nrm_nonneg _
      have j1 : 0 ≤ ({ω | sig2F μ f ω < A} : Set Ω).indicator (fun ω => sgF μ f ω) ω :=
        Set.indicator_nonneg (fun _ _ => nrm_nonneg _) _
      have j2 : 0 ≤ ({ω | normSq (f ω) < B} : Set Ω).indicator (fun ω => sgF μ f ω) ω :=
        Set.indicator_nonneg (fun _ _ => nrm_nonneg _) _
      by_cases h : ω ∈ Bd
      · rw [Set.indicator_of_mem h]
        rcases h with h | h
        · rw [Set.indicator_of_mem h]; linarith
        · rw [Set.indicator_of_mem (s := {ω | normSq (f ω) < B}) h]; linarith
      · rw [Set.indicator_of_notMem h]; linarith
    have hj1 : Integrable (fun ω =>
        ({ω | sig2F μ f ω < A} : Set Ω).indicator (fun ω => sgF μ f ω) ω) μ := hsg.indicator hB1
    have hj2 : Integrable (fun ω =>
        ({ω | normSq (f ω) < B} : Set Ω).indicator (fun ω => sgF μ f ω) ω) μ := hsg.indicator hB2
    have hmono := integral_mono hiB (hj1.add hj2) hpw
    have hadd : ∫ ω, (({ω | sig2F μ f ω < A} : Set Ω).indicator (fun ω => sgF μ f ω) ω +
        ({ω | normSq (f ω) < B} : Set Ω).indicator (fun ω => sgF μ f ω) ω) ∂μ =
        ∫ ω, ({ω | sig2F μ f ω < A} : Set Ω).indicator (fun ω => sgF μ f ω) ω ∂μ +
        ∫ ω, ({ω | normSq (f ω) < B} : Set Ω).indicator (fun ω => sgF μ f ω) ω ∂μ :=
      integral_add hj1 hj2
    have hmono' : ∫ ω, Bd.indicator (fun ω => sgF μ f ω) ω ∂μ ≤
        ∫ ω, (({ω | sig2F μ f ω < A} : Set Ω).indicator (fun ω => sgF μ f ω) ω +
        ({ω | normSq (f ω) < B} : Set Ω).indicator (fun ω => sgF μ f ω) ω) ∂μ := hmono
    rw [hadd, integral_indicator hB1, integral_indicator hB2] at hmono'
    linarith
  have hprod : (∫ ω, Bd.indicator (fun ω => sgF μ f ω) ω ∂μ) * (∫ ω, sgF μ f ω ∂μ) ≤
      (√A * piHS + √B * pif) * sF μ f :=
    mul_le_mul hIBle hsle hIS0 (hIB0.trans hIBle)
  calc ∫ p : Ω × Ω, rsF μ f p * (√(1 + 2 * (GamBarF μ f *
          ((betaF μ f p.1 / nrm (gF μ f p.1)) ^ 2 +
          (betaF μ f p.2 / nrm (gF μ f p.2)) ^ 2) / 4)))⁻¹ ∂(μ.prod μ)
      ≤ ∫ p : Ω × Ω, (1 / √(A * B) * ccF μ f p ^ 2 +
          (Bd.indicator (fun ω => sgF μ f ω) p.1 * sgF μ f p.2 +
            sgF μ f p.1 * Bd.indicator (fun ω => sgF μ f ω) p.2)) ∂(μ.prod μ) :=
        integral_mono hLi (hU1.add (hU2.add hU3)) hpt
    _ = 1 / √(A * B) * ∫ p : Ω × Ω, ccF μ f p ^ 2 ∂(μ.prod μ) +
          ((∫ ω, Bd.indicator (fun ω => sgF μ f ω) ω ∂μ) * (∫ ω, sgF μ f ω ∂μ) +
            (∫ ω, sgF μ f ω ∂μ) * (∫ ω, Bd.indicator (fun ω => sgF μ f ω) ω ∂μ)) := by
        have hU23 : Integrable (fun p : Ω × Ω =>
            Bd.indicator (fun ω => sgF μ f ω) p.1 * sgF μ f p.2 +
              sgF μ f p.1 * Bd.indicator (fun ω => sgF μ f ω) p.2) (μ.prod μ) := hU2.add hU3
        rw [integral_add hU1 hU23, integral_add hU2 hU3, integral_const_mul,
          integral_prod_mul (fun ω => Bd.indicator (fun ω => sgF μ f ω) ω) (fun ω => sgF μ f ω),
          integral_prod_mul (fun ω => sgF μ f ω) (fun ω => Bd.indicator (fun ω => sgF μ f ω) ω)]
    _ ≤ 1 / √(A * B) * hsF μ f + ((√A * piHS + √B * pif) * sF μ f +
          (√A * piHS + √B * pif) * sF μ f) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hc2le (by positivity))
          (add_le_add hprod ?_)
        rw [mul_comm]; exact hprod
    _ = _ := by ring

/-- The inner second moment for a fixed `ζ`, with the Gaussian factor in the remainder. -/
theorem inner_sq_exp (H : MFHyp μ f ℓ πg) (ζ : ℝ) :
    ∫ z', DF μ f (ζ • eF μ f + (projMat (eF μ f)).mulVec z') ^ 2 ∂stdGauss (Fin m) ≤
      ℓ ^ 2 * (∫ ω, (PhiG (betaF μ f ω * (ζ * √(GamBarF μ f)) / √(sig2F μ f ω)) -
          PhiG (ζ * √(GamBarF μ f) / sF μ f)) ^ 2 ∂μ) +
        K0 * (∫ p : Ω × Ω, rsF μ f p * eeF μ f (ζ * √(GamBarF μ f)) p ∂(μ.prod μ)) +
        (sF μ f * (cc0 (ℓ ^ 2 / sF2 μ f) πg + cc1 (ℓ ^ 2 / sF2 μ f) πg * |ζ| +
          cc2 (ℓ ^ 2 / sF2 μ f) * ζ ^ 2)) ^ 2 := by
  have hab := H.inner_abs_le ζ
  have hn : nrm (fbar μ f) = √(GamBarF μ f) := rfl
  simp_rw [H.DF_decomp] at hab ⊢
  rw [hn] at hab ⊢
  have hm := H.YF_mean (ζ * √(GamBarF μ f))
  have hV := YF_var_exp H (ζ * √(GamBarF μ f)) (PhiG (ζ * √(GamBarF μ f) / sF μ f))
  rw [var_shift hm.1 hV.1]
  rw [integral_sub hm.1 (integrable_const _), integral_const] at hab
  simp only [probReal_univ, one_smul] at hab
  have h2 := sq_le_sq' (abs_le.mp hab).1 (abs_le.mp hab).2
  have h3 := hV.2.2
  linarith

/-- **Lemma MF with the integrated remainder** (Lemma `t7:p05:MF`, change (C)). Under the
hypotheses (M1), (M2), (M3) of `MFHyp`, and with `μ{ς² < s²/ϰ} ≤ π_HS`,
`μ{|f|² < Γ_f/κ₃} ≤ π_f` (`ϰ, κ₃ > 0`):
`E_z 𝖣² ≤ K₀·(‖H‖²_HS/√((s²/ϰ)(Γ_f/κ₃)) + 2s(√(s²/ϰ)π_HS + √(Γ_f/κ₃)π_f))
  + ℓ²[(1/π)(2ϱ + 4(√2 − 1)²(Γ̄/s²)ν) + π_g] + s²Q_B(ϱ, π_g)`. -/
theorem lemmaMF_int (H : MFHyp μ f ℓ πg) {kap kap3 piHS pif : ℝ} (hk : 0 < kap)
    (hk3 : 0 < kap3)
    (hHS : μ.real {ω | sig2F μ f ω < sF2 μ f / kap} ≤ piHS)
    (hf : μ.real {ω | normSq (f ω) < GamF μ f / kap3} ≤ pif) :
    ∫ z, DF μ f z ^ 2 ∂stdGauss (Fin m) ≤
      K0 * (hsF μ f / √(sF2 μ f / kap * (GamF μ f / kap3)) +
          2 * sF μ f * (√(sF2 μ f / kap) * piHS + √(GamF μ f / kap3) * pif)) +
        ℓ ^ 2 * (1 / π * (2 * (ℓ ^ 2 / sF2 μ f) +
          4 * (√2 - 1) ^ 2 * (GamBarF μ f / sF2 μ f) * nuR (ℓ ^ 2 / sF2 μ f)) + πg) +
        sF2 μ f * QB (ℓ ^ 2 / sF2 μ f) πg := by
  have hK0 : 0 ≤ K0 := K0_pos.le
  have hD2 := H.DF_sq_int
  obtain ⟨hRint, hRle⟩ := rem_int_le H hk hk3 hHS hf
  rw [H.int_decomp (G := fun z => DF μ f z ^ 2) (H.meas_DF.pow_const 2) hD2]
  have hp := poly_gauss (cc0 (ℓ ^ 2 / sF2 μ f) πg) (cc1 (ℓ ^ 2 / sF2 μ f) πg)
    (cc2 (ℓ ^ 2 / sF2 μ f))
  have hAm : Measurable (fun ζ : ℝ =>
      ∫ ω, (PhiG (betaF μ f ω * (ζ * √(GamBarF μ f)) / √(sig2F μ f ω)) -
        PhiG (ζ * √(GamBarF μ f) / sF μ f)) ^ 2 ∂μ) := by
    have hF : Measurable (fun q : ℝ × Ω =>
        (PhiG (betaF μ f q.2 * (q.1 * √(GamBarF μ f)) / √(sig2F μ f q.2)) -
          PhiG (q.1 * √(GamBarF μ f) / sF μ f)) ^ 2) := by
      have hb : Measurable (fun q : ℝ × Ω => betaF μ f q.2) := H.meas_beta.comp measurable_snd
      have hs : Measurable (fun q : ℝ × Ω => √(sig2F μ f q.2)) :=
        (H.meas_sig.comp measurable_snd).sqrt
      have ha : Measurable (fun q : ℝ × Ω => q.1 * √(GamBarF μ f)) :=
        measurable_fst.mul_const _
      exact ((continuous_PhiG.measurable.comp ((hb.mul ha).div hs)).sub
        (continuous_PhiG.measurable.comp (ha.div_const _))).pow_const 2
    exact hF.stronglyMeasurable.integral_prod_right'.measurable
  have hAb : ∀ ζ : ℝ, ‖∫ ω, (PhiG (betaF μ f ω * (ζ * √(GamBarF μ f)) / √(sig2F μ f ω)) -
        PhiG (ζ * √(GamBarF μ f) / sF μ f)) ^ 2 ∂μ‖ ≤ 1 := by
    intro ζ
    have := norm_integral_le_of_norm_le_const (μ := μ) (C := 1)
      (f := fun ω => (PhiG (betaF μ f ω * (ζ * √(GamBarF μ f)) / √(sig2F μ f ω)) -
        PhiG (ζ * √(GamBarF μ f) / sF μ f)) ^ 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact PhiG_diff_le_one _ _)
    simpa using this
  have hAi : Integrable (fun ζ : ℝ =>
      ∫ ω, (PhiG (betaF μ f ω * (ζ * √(GamBarF μ f)) / √(sig2F μ f ω)) -
        PhiG (ζ * √(GamBarF μ f) / sF μ f)) ^ 2 ∂μ) (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).mono' hAm.aestronglyMeasurable (ae_of_all _ hAb)
  have r1 : Integrable (fun ζ : ℝ => ℓ ^ 2 *
      ∫ ω, (PhiG (betaF μ f ω * (ζ * √(GamBarF μ f)) / √(sig2F μ f ω)) -
        PhiG (ζ * √(GamBarF μ f) / sF μ f)) ^ 2 ∂μ) (gaussianReal 0 1) := hAi.const_mul _
  have r2 : Integrable (fun ζ : ℝ => K0 *
      ∫ p : Ω × Ω, rsF μ f p * eeF μ f (ζ * √(GamBarF μ f)) p ∂(μ.prod μ))
      (gaussianReal 0 1) := hRint.const_mul _
  have r3 : Integrable (fun ζ : ℝ => sF2 μ f * (cc0 (ℓ ^ 2 / sF2 μ f) πg +
      cc1 (ℓ ^ 2 / sF2 μ f) πg * |ζ| + cc2 (ℓ ^ 2 / sF2 μ f) * ζ ^ 2) ^ 2) (gaussianReal 0 1) :=
    hp.1.const_mul _
  have r12 : Integrable (fun ζ : ℝ => ℓ ^ 2 *
      (∫ ω, (PhiG (betaF μ f ω * (ζ * √(GamBarF μ f)) / √(sig2F μ f ω)) -
        PhiG (ζ * √(GamBarF μ f) / sF μ f)) ^ 2 ∂μ) +
      K0 * ∫ p : Ω × Ω, rsF μ f p * eeF μ f (ζ * √(GamBarF μ f)) p ∂(μ.prod μ))
      (gaussianReal 0 1) := r1.add r2
  have r123 : Integrable (fun ζ : ℝ => ℓ ^ 2 *
      (∫ ω, (PhiG (betaF μ f ω * (ζ * √(GamBarF μ f)) / √(sig2F μ f ω)) -
        PhiG (ζ * √(GamBarF μ f) / sF μ f)) ^ 2 ∂μ) +
      K0 * (∫ p : Ω × Ω, rsF μ f p * eeF μ f (ζ * √(GamBarF μ f)) p ∂(μ.prod μ)) +
      sF2 μ f * (cc0 (ℓ ^ 2 / sF2 μ f) πg +
      cc1 (ℓ ^ 2 / sF2 μ f) πg * |ζ| + cc2 (ℓ ^ 2 / sF2 μ f) * ζ ^ 2) ^ 2) (gaussianReal 0 1) :=
    r12.add r3
  have hle := integral_mono_of_nonneg
    (f := fun ζ : ℝ => ∫ z', DF μ f (ζ • eF μ f + (projMat (eF μ f)).mulVec z') ^ 2
      ∂stdGauss (Fin m))
    (ae_of_all _ fun ζ => integral_nonneg fun _ => sq_nonneg _) r123
    (ae_of_all _ fun ζ => by
      have h := inner_sq_exp H ζ
      rw [mul_pow, H.sF_sq] at h
      exact h)
  rw [integral_add r12 r3, integral_add r1 r2, integral_const_mul, integral_const_mul,
    integral_const_mul, hp.2] at hle
  have hlin := mul_le_mul_of_nonneg_left H.lin_term (sq_nonneg ℓ)
  have hrem := mul_le_mul_of_nonneg_left hRle hK0
  unfold QB
  linarith

end BstLean.Part160

open BstLean.Part160 in
#print axioms gauss_exp_sq
open BstLean.Part160 in
#print axioms YF_var_exp
open BstLean.Part160 in
#print axioms rem_int_le
open BstLean.Part160 in
#print axioms lemmaMF_int
