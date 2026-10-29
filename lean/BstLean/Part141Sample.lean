import BstLean.Part141Final

/-!
# Part 141: the mean of `k` independent points of the cheap stand-in with the ARITHMETIC centre
and the ARITHMETIC scalar

Role: `delegations/statements/p141-spec.md`, items 3 and 4. The estimate is the mean of
`F(A(y_i))` over `k` independent points `y_i = sphPt(M₃ b̃ + τ̃₀γ_i)` (`γ_i` independent standard
Gaussian vectors of `ℝⁿ`, independent of `(W, A, F)`).

* `preA W γ = M₃ b̃ + τ̃₀γ`; `gSampleA k W A F γ`: the sample mean.
* **`errSampleA_lint`**: `E[1_good(W)·(g̃_k − B)²] ≤ (X + 1/k)·(4/n)`, `X` the constant of
  `errVecA_lint`.
* **`sampleA141`**: for `n ≥ 4096` and `k ≥ 1`:
  `Pr(|g̃_k − B| ≤ sd/2) ≥ 1 − (0.002 + 2031/n + 180/k)`, the probability over `(W, A, F)` and
  the `k` Gaussian vectors.
The proofs are those of `Part140Sample` with the arithmetic centre and scalar.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part141

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140

/-! ## The sample estimate -/

section defs

variable {n mA mF : ℕ}

/-- The point of the cheap stand-in of the arithmetic program from the Gaussian vector `γ`,
before the normalization: `M₃ b̃ + τ̃₀γ`. -/
noncomputable def preA (W : MlpParam (2 * n) (mW n) n) (γ : Fin n → ℝ) : Fin n → ℝ :=
  cenA W + tauWA W • γ

/-- **The sample estimate** `g̃_k`: the mean of `F(A(y_i))` over the `k` points
`y_i = sphPt(M₃ b̃ + τ̃₀γ_i)`. -/
noncomputable def gSampleA (k : ℕ) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n mA n)
    (F : MlpParam n mF 1) (γ : Fin k → Fin n → ℝ) : ℝ :=
  (k : ℝ)⁻¹ * ∑ i, phiS A F (preA W (γ i))

lemma measurable_preA :
    Measurable (fun q : MlpParam (2 * n) (mW n) n × (Fin n → ℝ) => preA q.1 q.2) := by
  unfold preA
  exact (measurable_cenA.comp measurable_fst).add
    ((measurable_tauWA.comp measurable_fst).smul measurable_snd)

lemma measurable_preA_W (W : MlpParam (2 * n) (mW n) n) : Measurable (preA W) := by
  unfold preA
  exact measurable_const.add (measurable_const_smul _)

lemma gA_eq (hn : 1 ≤ n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n mA n)
    (F : MlpParam n mF 1) :
    gA W A F = ∫ γ, phiS A F (preA W γ) ∂stdGauss (Fin n) := by
  unfold gA
  rw [← integral_phiS_cheapIn hn, integral_cheapIn _ _ (bm_phiS hn A F).meas]
  simp only [phiS, sphPt_idem hn]
  rfl

lemma measurable_gSampleA (k : ℕ) :
    Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin k → Fin n → ℝ) => gSampleA k p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold gSampleA
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
  have h1 : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n mA n ×
      MlpParam n mF 1) × (Fin k → Fin n → ℝ) => preA p.1.1 (p.2 i)) :=
    measurable_preA.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  exact BstLean.Part131.continuous_phiN_all.measurable.comp
    ((measurable_snd.comp measurable_fst).prodMk (measurable_sphPt.comp h1))

end defs

/-! ## The error of the sample estimate, joint over `(W, A, F)` and the Gaussian vectors -/

/-- `1_good(W)·(g̃_k − B)²`, a function of `((W, A, F), γ)`. -/
noncomputable def errSA (k n : ℕ)
    (p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) : ℝ :=
  (goodWA n).indicator (fun W => (gSampleA k W p.1.2.1 p.1.2.2 p.2 -
    Part130.Bn W p.1.2.1 p.1.2.2) ^ 2) p.1.1

lemma errSA_nonneg (k n : ℕ)
    (p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) : 0 ≤ errSA k n p :=
  Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

lemma measurable_errSA {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : Measurable (errSA k n) := by
  have hN : 1 ≤ 2 * n := by omega
  have e : errSA k n = ({p | p.1.1 ∈ goodWA n} : Set ((MlpParam (2 * n) (mW n) n ×
      MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ))).indicator
      (fun p => (gSampleA k p.1.1 p.1.2.1 p.1.2.2 p.2 -
        Part130.Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2) := by
    funext p
    by_cases hp : p.1.1 ∈ goodWA n
    · rw [Set.indicator_of_mem (show p ∈ {p : (MlpParam (2 * n) (mW n) n ×
        MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
        p.1.1 ∈ goodWA n} from hp)]
      unfold errSA
      rw [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem (show p ∉ {p : (MlpParam (2 * n) (mW n) n ×
        MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
        p.1.1 ∈ goodWA n} from hp)]
      unfold errSA
      rw [Set.indicator_of_notMem hp]
  rw [e]
  exact (((measurable_gSampleA k).sub
    ((BstLean.Part131.measurable_Bn hN).comp measurable_fst)).pow_const 2).indicator
    ((measurable_fst.comp measurable_fst) (goodWA_meas hn))

/-- The constant of `errVecA_lint`. -/
noncomputable def XA (n : ℕ) (ζ η η' : ℝ) : ℝ :=
  (1 + η') * ((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ) +
    (1 + 1 / η') * pertA n

lemma XA_nonneg {n : ℕ} (hn : 4096 ≤ n) (ζ : ℝ) {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') :
    0 ≤ XA n ζ η η' := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hEH := EHH_nonneg hn ζ
  have hp := pertA_nonneg n
  unfold XA
  positivity

section joint

variable {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η)
  {η' : ℝ} (hη' : 0 < η') {k : ℕ} (hk : 1 ≤ k)

include hn hζ0 hζ1 hη hη' hk

/-- **The error of the sample estimate.** For `n ≥ 4096`, `0 < ζ < 1`, `k ≥ 1`:
`E[1_good(W)·(g̃_k − B)²] ≤ (XA n ζ η η′ + 1/k)·(4/n)`, the mean over `(W, A, F)` and the `k`
Gaussian vectors. -/
theorem errSampleA_lint :
    ∫⁻ p, ENNReal.ofReal (errSA k n p) ∂((mlpTriple 2 n).prod (gamK k n)) ≤
      ENNReal.ofReal ((XA n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have hX := XA_nonneg hn ζ hη hη'
  set PW := mlpGauss (2 * n) (mW n) n with hPW
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  have e0 : mlpTriple 2 n = PW.prod PAF := rfl
  have mf : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => ENNReal.ofReal (errSA k n p)) :=
    ENNReal.measurable_ofReal.comp (measurable_errSA hn1 k)
  rw [lintegral_prod _ mf.aemeasurable]
  -- the second moment term, as a function of `(W, (A, F))`
  set L : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => Lout (stdGauss (Fin n)) (preA t.1) t.2 with hL
  have mL : Measurable L := by
    have hj : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin n → ℝ) =>
        ENNReal.ofReal (phiS q.1.2.1 q.1.2.2 (preA q.1.1 q.2) ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((BstLean.Part131.continuous_phiN_all.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk (measurable_sphPt.comp
          (measurable_preA.comp ((measurable_fst.comp measurable_fst).prodMk
            measurable_snd))))).pow_const 2)
    exact hj.lintegral_prod_right'
  have hLint : ∫⁻ t, L t ∂mlpTriple 2 n = ENNReal.ofReal (4 / (n : ℝ)) := by
    rw [e0, lintegral_prod _ mL.aemeasurable]
    have h : ∀ W : MlpParam (2 * n) (mW n) n,
        ∫⁻ q, L (W, q) ∂PAF = ENNReal.ofReal (4 / (n : ℝ)) := by
      intro W
      have := lintegral_Lout (mA := mA n) (mF := mF n) (stdGauss (Fin n)) hn1 hmA hmF
        (measurable_preA_W W)
      exact this
    simp_rw [h]
    simp
  have key : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ∫⁻ γ, ENNReal.ofReal (errSA k n (t, γ)) ∂gamK k n ≤
        ENNReal.ofReal (errGA n t) + ENNReal.ofReal ((k : ℝ)⁻¹) * L t := by
    rintro ⟨W, A, F⟩
    have ho : Measurable (preA W) := measurable_preA_W W
    have hφ : BstLean.Part105.BM (fun γ : Fin n → ℝ => phiS A F (preA W γ)) :=
      (bm_phiS hn1 A F).comp ho
    obtain ⟨hi, he⟩ := iid_mean_sq (stdGauss (Fin n)) hφ hk (Part130.Bn W A F)
    by_cases hW : W ∈ goodWA n
    · have e1 : ∀ γ : Fin k → Fin n → ℝ, errSA k n ((W, A, F), γ) =
          ((k : ℝ)⁻¹ * ∑ i, phiS A F (preA W (γ i)) - Part130.Bn W A F) ^ 2 := by
        intro γ
        simp only [errSA, Set.indicator_of_mem hW, gSampleA]
      simp_rw [e1]
      rw [show gamK k n = Measure.pi (fun _ : Fin k => stdGauss (Fin n)) from rfl,
        ← ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
      have he' : ∫ x : Fin k → Fin n → ℝ, ((k : ℝ)⁻¹ * ∑ i, phiS A F (preA W (x i)) -
          Part130.Bn W A F) ^ 2 ∂Measure.pi (fun _ : Fin k => stdGauss (Fin n)) =
          (∫ x, phiS A F (preA W x) ∂stdGauss (Fin n) - Part130.Bn W A F) ^ 2 +
            (k : ℝ)⁻¹ * Var[fun γ : Fin n → ℝ => phiS A F (preA W γ); stdGauss (Fin n)] := he
      rw [he', ← gA_eq hn1]
      have hv : Var[fun γ : Fin n → ℝ => phiS A F (preA W γ); stdGauss (Fin n)] ≤
          ∫ γ, phiS A F (preA W γ) ^ 2 ∂stdGauss (Fin n) := by
        rw [BstLean.Part134.var_bm (stdGauss (Fin n)) hφ]
        nlinarith [sq_nonneg (∫ γ, phiS A F (preA W γ) ∂stdGauss (Fin n))]
      have hG : errGA n (W, A, F) = (gA W A F - Part130.Bn W A F) ^ 2 := by
        simp only [errGA, Set.indicator_of_mem hW]
      have i0 : 0 ≤ ∫ γ, phiS A F (preA W γ) ^ 2 ∂stdGauss (Fin n) :=
        integral_nonneg fun _ => sq_nonneg _
      rw [hL]
      simp only
      rw [← ofReal_integral_out (stdGauss (Fin n)) hn1 A F ho, hG,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (sq_nonneg _)
          (mul_nonneg (by positivity) i0)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹)
      linarith
    · have e1 : ∀ γ : Fin k → Fin n → ℝ, errSA k n ((W, A, F), γ) = 0 := by
        intro γ
        simp only [errSA, Set.indicator_of_notMem hW]
      simp_rw [e1]
      simp
  calc ∫⁻ t, (∫⁻ γ, ENNReal.ofReal (errSA k n (t, γ)) ∂gamK k n) ∂mlpTriple 2 n
      ≤ ∫⁻ t, (ENNReal.ofReal (errGA n t) + ENNReal.ofReal ((k : ℝ)⁻¹) * L t) ∂mlpTriple 2 n :=
        lintegral_mono key
    _ = ∫⁻ t, ENNReal.ofReal (errGA n t) ∂mlpTriple 2 n +
        ENNReal.ofReal ((k : ℝ)⁻¹) * ENNReal.ofReal (4 / (n : ℝ)) := by
        have m1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
            MlpParam n (mF n) 1 => ENNReal.ofReal (errGA n t)) :=
          ENNReal.measurable_ofReal.comp (measurable_errGA hn1)
        rw [lintegral_add_left m1, lintegral_const_mul _ mL, hLint]
    _ ≤ ENNReal.ofReal (XA n ζ η η' * (4 / (n : ℝ))) +
        ENNReal.ofReal ((k : ℝ)⁻¹) * ENNReal.ofReal (4 / (n : ℝ)) :=
        add_le_add (errVecA_lint hn hζ0 hζ1 hη hη') le_rfl
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        ring

/-- The tail form: for `s > 0`:
`Pr(W good and (g̃_k − B)² ≥ s) ≤ (XA n ζ η η′ + 1/k)·(4/n)/s`. -/
theorem errSampleTailA {s : ℝ} (hs : 0 < s) :
    ((mlpTriple 2 n).prod (gamK k n)).real {p | s ≤ errSA k n p} ≤
      (XA n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hX := XA_nonneg hn ζ hη hη'
  have h := errSampleA_lint hn hζ0 hζ1 hη hη' hk
  have hc : (0 : ℝ) ≤ (XA n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ)) := by positivity
  have h0 : 0 ≤ᵐ[(mlpTriple 2 n).prod (gamK k n)] errSA k n :=
    Filter.Eventually.of_forall (errSA_nonneg k n)
  have hm := (measurable_errSA hn1 k).aestronglyMeasurable
    (μ := (mlpTriple 2 n).prod (gamK k n))
  have hi : Integrable (errSA k n) ((mlpTriple 2 n).prod (gamK k n)) :=
    ⟨hm, (hasFiniteIntegral_iff_ofReal h0).2 (lt_of_le_of_lt h ENNReal.ofReal_lt_top)⟩
  have hb : ∫ p, errSA k n p ∂((mlpTriple 2 n).prod (gamK k n)) ≤
      (XA n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ)) := by
    rw [integral_eq_lintegral_of_nonneg_ae h0 hm]
    exact ENNReal.toReal_le_of_le_ofReal hc h
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := (mlpTriple 2 n).prod (gamK k n))
    (f := errSA k n) h0 hi s
  rw [le_div_iff₀ hs]
  linarith

end joint

/-! ## The headline for the sample estimate -/

/-- The success event of the sample estimate: `|g̃_k − B| ≤ sd/2`. -/
def okSampleA (k n : ℕ) : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
    MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ)) :=
  {p | |gSampleA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
    sdn p.1.1 p.1.2.1 p.1.2.2 / 2}

/-- The arithmetic of the terms at `θ = 1/10`, `ζ = η = 1/20`, `η′ = 1/100`. -/
lemma rateA_arith {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    2 / 1000 + 70 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 +
      ((XA n (1 / 20) (1 / 20) (1 / 100) + (k : ℝ)⁻¹) * (4 / (n : ℝ)) /
        (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4)) +
      vSpread n / ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 ≤
    2 / 1000 + 2031 / (n : ℝ) + 180 / (k : ℝ) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have hy0 : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  have e : (XA n (1 / 20) (1 / 20) (1 / 100) + (k : ℝ)⁻¹) * (4 / (n : ℝ)) /
        (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4) =
      4 * XA n (1 / 20) (1 / 20) (1 / 100) / (1 / 10 * (1 - kappa^[6] 0)) +
        4 * (k : ℝ)⁻¹ / (1 / 10 * (1 - kappa^[6] 0)) := by
    field_simp
  rw [e]
  have t1 := markovA_le hn
  have t2 := chebA_le hn
  have t4 := qTerm_le hn
  have eX : XA n (1 / 20) (1 / 20) (1 / 100) =
      (1 + 1 / 100) * (21 / 20 * (183 / 100 / (n : ℝ)) + 84 * EHH n (1 / 20)) +
        (1 + 1 / (1 / 100)) * pertA n := by
    unfold XA
    norm_num
  rw [eX]
  have t3 : 4 * (k : ℝ)⁻¹ / (1 / 10 * (1 - kappa^[6] 0)) ≤ 180 / (k : ℝ) := by
    rw [div_le_div_iff₀ (by nlinarith) hk0, inv_eq_one_div]
    have h4 : 4 * (1 / (k : ℝ)) * (k : ℝ) = 4 := by
      rw [mul_assoc, one_div_mul_cancel hk0.ne', mul_one]
    nlinarith
  have e70 : 70 / (n : ℝ) = 70 * (1 / (n : ℝ)) := by ring
  have e2031 : 2031 / (n : ℝ) = 2031 * (1 / (n : ℝ)) := by ring
  have ht0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  rw [e2031, e70]
  linarith

/-- **`sampleA141`: the sample estimate with the arithmetic centre and scalar succeeds.** For
every `n ≥ 4096` and every `k ≥ 1`, with `g̃_k` the mean of `F(A(·))` over `k` independent points
`sphPt(M₃ b̃ + τ̃₀γ_i)`: `Pr(|g̃_k − B| ≤ sd/2) ≥ 1 − (0.002 + 2031/n + 180/k)`, the probability
over `(W, A, F)` and the `k` Gaussian vectors. -/
theorem sampleA141 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    1 - (2 / 1000 + 2031 / (n : ℝ) + 180 / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okSampleA k n) := by
  have hx0 : (0 : ℝ) < n := by have := nR_ge hn; linarith
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have hs0 : (0 : ℝ) < 1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 := by
    have : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
    positivity
  have h1 : ((mlpTriple 2 n).prod (gamK k n)).real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n}ᶜ ≤
      2 / 1000 + 70 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 :=
    (prod_fst_real (mlpTriple 2 n) (gamK k n) {t | t.1 ∉ goodWA n}).trans_le (badA_prob hn)
  have h2 : ((mlpTriple 2 n).prod (gamK k n)).real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p ∈ {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n} ∧
        1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 ≤
          (gSampleA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2} ≤
      (XA n (1 / 20) (1 / 20) (1 / 100) + (k : ℝ)⁻¹) * (4 / (n : ℝ)) /
        (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4) := by
    have hT := errSampleTailA hn (ζ := 1 / 20) (by norm_num) (by norm_num) (η := 1 / 20)
      (by norm_num) (η' := 1 / 100) (by norm_num) hk hs0
    refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hT
    rintro p ⟨hg, he⟩
    change _ ≤ errSA k n p
    unfold errSA
    rw [Set.indicator_of_mem (show p.1.1 ∈ goodWA n from hg)]
    exact he
  have h3 : ((mlpTriple 2 n).prod (gamK k n)).real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2 <
          4 * (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4)} ≤
      vSpread n / ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 := by
    have e : (4 : ℝ) * (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4) =
        1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) := by ring
    rw [e]
    exact (prod_fst_real (mlpTriple 2 n) (gamK k n)
      {t | sdn t.1 t.2.1 t.2.2 ^ 2 < 1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0))}).trans_le
      (spreadLow139 hn (by norm_num))
  have h := ok_of_three ((mlpTriple 2 n).prod (gamK k n))
    (d := fun p => gSampleA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2)
    (sd := fun p => sdn p.1.1 p.1.2.1 p.1.2.2) (fun p => sdn_nonneg' _ _ _) h1 h2 h3
  have ha := rateA_arith hn hk
  exact le_trans (by linarith) h

end BstLean.Part141

open BstLean.Part141 in
#print axioms errSampleA_lint
open BstLean.Part141 in
#print axioms sampleA141
