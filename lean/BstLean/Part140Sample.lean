import BstLean.Part140Final

/-!
# Part 140: the mean of `k` independent points of the cheap stand-in with the computed centre

Role: `delegations/statements/p140-spec.md`, items 3 and 4. The estimate is the mean of
`F(A(y_i))` over `k` independent points `y_i = sphPt(M₃ b̂ + τ̂₀γ_i)` (`γ_i` independent standard
Gaussian vectors of `ℝⁿ`, independent of `(W, A, F)`), with the computed centre `b̂` and the
scalar `τ̂₀` of this part.

* `preHat W γ = M₃ b̂ + τ̂₀γ`; `gSampleH k W A F γ`: the sample mean.
* **`errSampleHat_lint`**: `E[1_good(W)·(ĝ_k − B)²] ≤ ((1 + η)·(1.83/n) + 4(1 + 1/η)·EHH n ζ + 1/k)·(4/n)`.
* **`sampleHat140`**: for `n ≥ 4096` and `k ≥ 1`:
  `Pr(|ĝ_k − B| ≤ sd/2) ≥ 1 − (0.002 + 2022/n + 180/k)`, the probability over `(W, A, F)` and
  the `k` Gaussian vectors.
The proofs are those of `Part139Sample` with the computed centre.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part140

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM

/-! ## The sample estimate -/

section defs

variable {N m n mA mF : ℕ}

/-- The point of the cheap stand-in of `W` from the Gaussian vector `γ`:
`sphPt(M₃b̂ + τ̂₀γ)` before the normalization. -/
noncomputable def preHat (W : MlpParam N m n) (γ : Fin n → ℝ) : Fin n → ℝ :=
  W.2.2.mulVec (bhat (W.1, W.2.1)) + tauHat N m (W.1, W.2.1) • γ

/-- **The sample estimate** `ĝ_k`: the mean of `F(A(y_i))` over the `k` points
`y_i = sphPt(M₃b̂ + τ̂₀γ_i)` of the cheap stand-in of `W`. -/
noncomputable def gSampleH (k : ℕ) (W : MlpParam N m n) (A : MlpParam n mA n)
    (F : MlpParam n mF 1) (γ : Fin k → Fin n → ℝ) : ℝ :=
  (k : ℝ)⁻¹ * ∑ i, phiS A F (preHat W (γ i))

lemma measurable_preHat (hN : 1 ≤ N) :
    Measurable (fun q : MlpParam N m n × (Fin n → ℝ) => preHat q.1 q.2) := by
  have hθ : Measurable (fun W : MlpParam N m n => ((W.1, W.2.1) : HidParam N m)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hc : Measurable (fun W : MlpParam N m n => W.2.2.mulVec (bhat (W.1, W.2.1))) :=
    measurable_mulVec_joint.comp
      ((measurable_snd.comp measurable_snd).prodMk ((measurable_bhat hN).comp hθ))
  have hτ : Measurable (fun W : MlpParam N m n => tauHat N m (W.1, W.2.1)) :=
    (measurable_tauHat hN).comp hθ
  unfold preHat
  exact (hc.comp measurable_fst).add ((hτ.comp measurable_fst).smul measurable_snd)

lemma measurable_preHat_W (W : MlpParam N m n) : Measurable (preHat W) := by
  unfold preHat
  exact measurable_const.add (measurable_const_smul _)

lemma gHat_eq (hn : 1 ≤ n) (W : MlpParam N m n) (A : MlpParam n mA n) (F : MlpParam n mF 1) :
    gHat W A F = ∫ γ, phiS A F (preHat W γ) ∂stdGauss (Fin n) := by
  unfold gHat cheapHat
  rw [← integral_phiS_cheapIn hn, integral_cheapIn _ _ (bm_phiS hn A F).meas]
  simp only [phiS, sphPt_idem hn]
  rfl

lemma measurable_gSampleHH (hN : 1 ≤ N) (k : ℕ) :
    Measurable (fun p : (MlpParam N m n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin k → Fin n → ℝ) => gSampleH k p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold gSampleH
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
  have h1 : Measurable (fun p : (MlpParam N m n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin k → Fin n → ℝ) => preHat p.1.1 (p.2 i)) :=
    (measurable_preHat hN).comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  exact BstLean.Part131.continuous_phiN_all.measurable.comp
    ((measurable_snd.comp measurable_fst).prodMk (measurable_sphPt.comp h1))

end defs

/-! ## The error of the sample estimate, joint over `(W, A, F)` and the Gaussian vectors -/

/-- `1_good(W)·(ĝ_k − B)²`, a function of `((W, A, F), γ)`. -/
noncomputable def errSH (k n : ℕ)
    (p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) : ℝ :=
  (goodWH n).indicator (fun W => (gSampleH k W p.1.2.1 p.1.2.2 p.2 -
    Part130.Bn W p.1.2.1 p.1.2.2) ^ 2) p.1.1

lemma errSH_nonneg (k n : ℕ)
    (p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) : 0 ≤ errSH k n p :=
  Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

lemma measurable_errSH {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : Measurable (errSH k n) := by
  have hN : 1 ≤ 2 * n := by omega
  have e : errSH k n = ({p | p.1.1 ∈ goodWH n} : Set ((MlpParam (2 * n) (mW n) n ×
      MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ))).indicator
      (fun p => (gSampleH k p.1.1 p.1.2.1 p.1.2.2 p.2 -
        Part130.Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2) := by
    funext p
    by_cases hp : p.1.1 ∈ goodWH n
    · rw [Set.indicator_of_mem (show p ∈ {p : (MlpParam (2 * n) (mW n) n ×
        MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
        p.1.1 ∈ goodWH n} from hp)]
      unfold errSH
      rw [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem (show p ∉ {p : (MlpParam (2 * n) (mW n) n ×
        MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
        p.1.1 ∈ goodWH n} from hp)]
      unfold errSH
      rw [Set.indicator_of_notMem hp]
  rw [e]
  exact (((measurable_gSampleHH hN k).sub
    ((BstLean.Part131.measurable_Bn hN).comp measurable_fst)).pow_const 2).indicator
    ((measurable_fst.comp measurable_fst) (goodWH_meas hn))

section joint

variable {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η)
  {k : ℕ} (hk : 1 ≤ k)

include hn hζ0 hζ1 hη hk

/-- **The error of the sample estimate.** For `n ≥ 4096`, `0 < ζ < 1`, `k ≥ 1`:
`E[1_good(W)·(ĝ_k − B)²] ≤ ((1 + η)·(1.83/n) + 4(1 + 1/η)·EHH n ζ + 1/k)·(4/n)`, the mean over `(W, A, F)` and
the `k` Gaussian vectors. -/
theorem errSampleHat_lint :
    ∫⁻ p, ENNReal.ofReal (errSH k n p) ∂((mlpTriple 2 n).prod (gamK k n)) ≤
      ENNReal.ofReal (((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ + (k : ℝ)⁻¹) * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have hEH := EHH_nonneg hn ζ
  set PW := mlpGauss (2 * n) (mW n) n with hPW
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  have e0 : mlpTriple 2 n = PW.prod PAF := rfl
  have mf : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => ENNReal.ofReal (errSH k n p)) :=
    ENNReal.measurable_ofReal.comp (measurable_errSH hn1 k)
  rw [lintegral_prod _ mf.aemeasurable]
  -- the second moment term, as a function of `(W, (A, F))`
  set L : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => Lout (stdGauss (Fin n)) (preHat t.1) t.2 with hL
  have mL : Measurable L := by
    have hj : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin n → ℝ) =>
        ENNReal.ofReal (phiS q.1.2.1 q.1.2.2 (preHat q.1.1 q.2) ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((BstLean.Part131.continuous_phiN_all.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk (measurable_sphPt.comp
          ((measurable_preHat hN).comp ((measurable_fst.comp measurable_fst).prodMk
            measurable_snd))))).pow_const 2)
    exact hj.lintegral_prod_right'
  have hLint : ∫⁻ t, L t ∂mlpTriple 2 n = ENNReal.ofReal (4 / (n : ℝ)) := by
    rw [e0, lintegral_prod _ mL.aemeasurable]
    have h : ∀ W : MlpParam (2 * n) (mW n) n,
        ∫⁻ q, L (W, q) ∂PAF = ENNReal.ofReal (4 / (n : ℝ)) := by
      intro W
      have := lintegral_Lout (mA := mA n) (mF := mF n) (stdGauss (Fin n)) hn1 hmA hmF
        (measurable_preHat_W W)
      exact this
    simp_rw [h]
    simp
  have key : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ∫⁻ γ, ENNReal.ofReal (errSH k n (t, γ)) ∂gamK k n ≤
        ENNReal.ofReal (errGH n t) + ENNReal.ofReal ((k : ℝ)⁻¹) * L t := by
    rintro ⟨W, A, F⟩
    have ho : Measurable (preHat W) := measurable_preHat_W W
    have hφ : BstLean.Part105.BM (fun γ : Fin n → ℝ => phiS A F (preHat W γ)) :=
      (bm_phiS hn1 A F).comp ho
    obtain ⟨hi, he⟩ := iid_mean_sq (stdGauss (Fin n)) hφ hk (Part130.Bn W A F)
    by_cases hW : W ∈ goodWH n
    · have e1 : ∀ γ : Fin k → Fin n → ℝ, errSH k n ((W, A, F), γ) =
          ((k : ℝ)⁻¹ * ∑ i, phiS A F (preHat W (γ i)) - Part130.Bn W A F) ^ 2 := by
        intro γ
        simp only [errSH, Set.indicator_of_mem hW, gSampleH]
      simp_rw [e1]
      rw [show gamK k n = Measure.pi (fun _ : Fin k => stdGauss (Fin n)) from rfl,
        ← ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
      have he' : ∫ x : Fin k → Fin n → ℝ, ((k : ℝ)⁻¹ * ∑ i, phiS A F (preHat W (x i)) -
          Part130.Bn W A F) ^ 2 ∂Measure.pi (fun _ : Fin k => stdGauss (Fin n)) =
          (∫ x, phiS A F (preHat W x) ∂stdGauss (Fin n) - Part130.Bn W A F) ^ 2 +
            (k : ℝ)⁻¹ * Var[fun γ : Fin n → ℝ => phiS A F (preHat W γ); stdGauss (Fin n)] := he
      rw [he', ← gHat_eq hn1]
      have hv : Var[fun γ : Fin n → ℝ => phiS A F (preHat W γ); stdGauss (Fin n)] ≤
          ∫ γ, phiS A F (preHat W γ) ^ 2 ∂stdGauss (Fin n) := by
        rw [BstLean.Part134.var_bm (stdGauss (Fin n)) hφ]
        nlinarith [sq_nonneg (∫ γ, phiS A F (preHat W γ) ∂stdGauss (Fin n))]
      have hG : errGH n (W, A, F) = (gHat W A F - Part130.Bn W A F) ^ 2 := by
        simp only [errGH, Set.indicator_of_mem hW]
      have i0 : 0 ≤ ∫ γ, phiS A F (preHat W γ) ^ 2 ∂stdGauss (Fin n) :=
        integral_nonneg fun _ => sq_nonneg _
      rw [hL]
      simp only
      rw [← ofReal_integral_out (stdGauss (Fin n)) hn1 A F ho, hG,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (sq_nonneg _)
          (mul_nonneg (by positivity) i0)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹)
      linarith
    · have e1 : ∀ γ : Fin k → Fin n → ℝ, errSH k n ((W, A, F), γ) = 0 := by
        intro γ
        simp only [errSH, Set.indicator_of_notMem hW]
      simp_rw [e1]
      simp
  calc ∫⁻ t, (∫⁻ γ, ENNReal.ofReal (errSH k n (t, γ)) ∂gamK k n) ∂mlpTriple 2 n
      ≤ ∫⁻ t, (ENNReal.ofReal (errGH n t) + ENNReal.ofReal ((k : ℝ)⁻¹) * L t) ∂mlpTriple 2 n :=
        lintegral_mono key
    _ = ∫⁻ t, ENNReal.ofReal (errGH n t) ∂mlpTriple 2 n +
        ENNReal.ofReal ((k : ℝ)⁻¹) * ENNReal.ofReal (4 / (n : ℝ)) := by
        have m1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
            MlpParam n (mF n) 1 => ENNReal.ofReal (errGH n t)) :=
          ENNReal.measurable_ofReal.comp (measurable_errGH hn1)
        rw [lintegral_add_left m1, lintegral_const_mul _ mL, hLint]
    _ ≤ ENNReal.ofReal (((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ) * (4 / (n : ℝ))) +
        ENNReal.ofReal ((k : ℝ)⁻¹) * ENNReal.ofReal (4 / (n : ℝ)) :=
        add_le_add (errVecHat_lint hn hζ0 hζ1 hη) le_rfl
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        ring

/-- The tail form: for `s > 0`:
`Pr(W good and (ĝ_k − B)² ≥ s) ≤ ((1 + η)·(1.83/n) + 4(1 + 1/η)·EHH n ζ + 1/k)·(4/n)/s`. -/
theorem errSampleTailHat {s : ℝ} (hs : 0 < s) :
    ((mlpTriple 2 n).prod (gamK k n)).real {p | s ≤ errSH k n p} ≤
      ((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hEH := EHH_nonneg hn ζ
  have h := errSampleHat_lint hn hζ0 hζ1 hη hk
  have hc : (0 : ℝ) ≤ ((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ + (k : ℝ)⁻¹) * (4 / (n : ℝ)) := by
    positivity
  have h0 : 0 ≤ᵐ[(mlpTriple 2 n).prod (gamK k n)] errSH k n :=
    Filter.Eventually.of_forall (errSH_nonneg k n)
  have hm := (measurable_errSH hn1 k).aestronglyMeasurable
    (μ := (mlpTriple 2 n).prod (gamK k n))
  have hi : Integrable (errSH k n) ((mlpTriple 2 n).prod (gamK k n)) :=
    ⟨hm, (hasFiniteIntegral_iff_ofReal h0).2 (lt_of_le_of_lt h ENNReal.ofReal_lt_top)⟩
  have hb : ∫ p, errSH k n p ∂((mlpTriple 2 n).prod (gamK k n)) ≤
      ((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ + (k : ℝ)⁻¹) * (4 / (n : ℝ)) := by
    rw [integral_eq_lintegral_of_nonneg_ae h0 hm]
    exact ENNReal.toReal_le_of_le_ofReal hc h
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := (mlpTriple 2 n).prod (gamK k n))
    (f := errSH k n) h0 hi s
  rw [le_div_iff₀ hs]
  linarith

end joint

/-! ## The headline for the sample estimate -/

/-- The success event of the sample estimate: `|ĝ_k − B| ≤ sd/2`. -/
def okSampleH (k n : ℕ) : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
    MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ)) :=
  {p | |gSampleH k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
    sdn p.1.1 p.1.2.1 p.1.2.2 / 2}

/-- The arithmetic of the terms at `θ = 1/10`, `ζ = η = 1/20`. -/
lemma rateHat_arith {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    2 / 1000 + 70 / (n : ℝ) +
      ((21 / 20 * (183 / 100 / (n : ℝ)) + 84 * EHH n (1 / 20) + (k : ℝ)⁻¹) * (4 / (n : ℝ)) /
        (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4)) +
      vSpread n / ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 ≤
    2 / 1000 + 2022 / (n : ℝ) + 180 / (k : ℝ) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have hy0 : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  have e : (21 / 20 * (183 / 100 / (n : ℝ)) + 84 * EHH n (1 / 20) + (k : ℝ)⁻¹) * (4 / (n : ℝ)) /
        (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4) =
      4 * (21 / 20 * (183 / 100 / (n : ℝ)) + 84 * EHH n (1 / 20)) / (1 / 10 * (1 - kappa^[6] 0)) +
        4 * (k : ℝ)⁻¹ / (1 / 10 * (1 - kappa^[6] 0)) := by
    field_simp
  rw [e]
  have hv := vSpread_scale hn
  have hv0 : 0 ≤ vSpread n := by unfold vSpread; positivity
  have hEH' := EHH_scale hn
  have hEH0 := EHH_nonneg hn (1 / 20)
  set t : ℝ := 1 / (n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have e183 : 183 / 100 / (n : ℝ) = 183 / 100 * t := by rw [ht]; ring
  have e64 : 64 / (n : ℝ) = 64 * t := by rw [ht]; ring
  have e70 : 70 / (n : ℝ) = 70 * t := by rw [ht]; ring
  have e2022 : 2022 / (n : ℝ) = 2022 * t := by rw [ht]; ring
  rw [e64] at hv
  have t1 : 4 * (21 / 20 * (183 / 100 / (n : ℝ)) + 84 * EHH n (1 / 20)) /
      (1 / 10 * (1 - kappa^[6] 0)) ≤ 3595 / 10 * t := by
    rw [e183, div_le_iff₀ (by nlinarith)]
    nlinarith
  have t2 : vSpread n / ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 ≤ 15924 / 10 * t := by
    have hden : ((1 - 1 / 10) * (222757 / 1000000 : ℝ)) ^ 2 ≤
        ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by nlinarith) 2
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  have t3 : 4 * (k : ℝ)⁻¹ / (1 / 10 * (1 - kappa^[6] 0)) ≤ 180 / (k : ℝ) := by
    rw [div_le_div_iff₀ (by nlinarith) hk0, inv_eq_one_div]
    have h4 : 4 * (1 / (k : ℝ)) * (k : ℝ) = 4 := by
      rw [mul_assoc, one_div_mul_cancel hk0.ne', mul_one]
    nlinarith
  rw [e2022, e70]
  linarith

/-- **`sampleHat140`: the sample estimate with the computed centre succeeds.** For every
`n ≥ 4096` and every `k ≥ 1`, with `ĝ_k` the mean of `F(A(·))` over `k` independent points
`sphPt(M₃ b̂ + τ̂₀γ_i)`: `Pr(|ĝ_k − B| ≤ sd/2) ≥ 1 − (0.002 + 2022/n + 180/k)`, the probability
over `(W, A, F)` and the `k` Gaussian vectors. -/
theorem sampleHat140 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    1 - (2 / 1000 + 2022 / (n : ℝ) + 180 / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okSampleH k n) := by
  have hx0 : (0 : ℝ) < n := by have := nR_ge hn; linarith
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have hs0 : (0 : ℝ) < 1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 := by
    have : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
    positivity
  have h1 : ((mlpTriple 2 n).prod (gamK k n)).real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWH n}ᶜ ≤ 2 / 1000 + 70 / (n : ℝ) :=
    (prod_fst_real (mlpTriple 2 n) (gamK k n) {t | t.1 ∉ goodWH n}).trans_le (badHat_prob hn)
  have h2 : ((mlpTriple 2 n).prod (gamK k n)).real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p ∈ {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWH n} ∧
        1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 ≤
          (gSampleH k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2} ≤
      (21 / 20 * (183 / 100 / (n : ℝ)) + 84 * EHH n (1 / 20) + (k : ℝ)⁻¹) * (4 / (n : ℝ)) /
        (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4) := by
    have hT := errSampleTailHat hn (ζ := 1 / 20) (by norm_num) (by norm_num) (η := 1 / 20)
      (by norm_num) hk hs0
    have e84 : (4 : ℝ) * (1 + 1 / (1 / 20)) = 84 := by norm_num
    have e105 : (1 : ℝ) + 1 / 20 = 21 / 20 := by norm_num
    rw [e84, e105] at hT
    refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
      hT
    rintro p ⟨hg, he⟩
    change _ ≤ errSH k n p
    unfold errSH
    rw [Set.indicator_of_mem (show p.1.1 ∈ goodWH n from hg)]
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
    (d := fun p => gSampleH k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2)
    (sd := fun p => sdn p.1.1 p.1.2.1 p.1.2.2) (fun p => sdn_nonneg' _ _ _) h1 h2 h3
  have ha := rateHat_arith hn hk
  exact le_trans (by linarith) h

end BstLean.Part140

open BstLean.Part140 in
#print axioms errSampleHat_lint
open BstLean.Part140 in
#print axioms sampleHat140
