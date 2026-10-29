import BstLean.Part139Scale

/-!
# Part 139, item 4 (optional): the mean of `k` independent points of the cheap stand-in

Role: `delegations/statements/p139-spec.md`, item 4. The estimate is the mean of `F(A(y_i))`
over `k` independent points `y_i = sphPt(M₃h̄ + τ₀γ_i)` of the cheap stand-in `ν′_W` (`γ_i`
independent standard Gaussian vectors of `ℝⁿ`, independent of `(W, A, F)`). The centre is the
exact `h̄` and the scalar is the exact `τ₀` of Part 138 (no cheap program has them).

* `gSample k W A F γ`: the sample mean.
* `iid_mean_sq`: `E(k⁻¹·Σ f(x_i) − b)² = (E f − b)² + Var(f)/k` for independent `x_i`.
* **`errSample139_lint`**: `E[1_good(W)·(ĝ_k − B)²] ≤ (2·(0.99/n) + 8·EH n ζ + 1/k)·(4/n)`.
* **`sampleSucceeds139`**: for `n ≥ 4096` and `k ≥ 1`:
  `Pr(|ĝ_k − B| ≤ sd/2) ≥ 1 − (0.002 + 1951/n + 180/k)`, the probability over `(W, A, F)` and
  the `k` Gaussian vectors.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part139

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part138

/-! ## The mean of `k` independent values -/

/-- **The second moment of a sample mean around a constant.** For a probability measure `ν`, a
bounded measurable `f`, `k ≥ 1` independent points and every real `b`:
`E(k⁻¹·Σ_i f(x_i) − b)² = (E f − b)² + Var(f)/k`. -/
lemma iid_mean_sq {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    {f : X → ℝ} (hf : BstLean.Part105.BM f) {k : ℕ} (hk : 1 ≤ k) (b : ℝ) :
    Integrable (fun x : Fin k → X => ((k : ℝ)⁻¹ * ∑ i, f (x i) - b) ^ 2)
      (Measure.pi fun _ : Fin k => ν) ∧
    ∫ x : Fin k → X, ((k : ℝ)⁻¹ * ∑ i, f (x i) - b) ^ 2 ∂Measure.pi (fun _ : Fin k => ν) =
      (∫ x, f x ∂ν - b) ^ 2 + (k : ℝ)⁻¹ * Var[f; ν] := by
  set π := Measure.pi fun _ : Fin k => ν with hπ
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨M, hM⟩ := hf.bdd
  set Sf : (Fin k → X) → ℝ := fun x => ∑ i, f (x i) with hSf
  have mS : Measurable Sf :=
    Finset.measurable_sum _ fun i _ => hf.meas.comp (measurable_pi_apply i)
  have bS : BstLean.Part105.BM Sf := by
    refine ⟨mS, k * M, fun x => ?_⟩
    calc |∑ i, f (x i)| ≤ ∑ i, |f (x i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin k, M := Finset.sum_le_sum fun i _ => hM _
      _ = k * M := by simp
  have bY : BstLean.Part105.BM (fun x : Fin k → X => (k : ℝ)⁻¹ * Sf x) :=
    (BstLean.Part105.BM.const _).mul bS
  have hfL : MemLp f 2 ν := BstLean.Part134.bm_memLp2 ν hf
  have hYL : MemLp (fun x : Fin k → X => (k : ℝ)⁻¹ * Sf x) 2 π :=
    BstLean.Part134.bm_memLp2 π bY
  -- the mean
  have hmean1 : ∀ i : Fin k, ∫ x : Fin k → X, f (x i) ∂π = ∫ x, f x ∂ν := by
    intro i
    have h := integral_map (μ := π) (φ := Function.eval i)
      (measurable_pi_apply i).aemeasurable (f := f)
      (by rw [(measurePreserving_eval (fun _ : Fin k => ν) i).map_eq]
          exact hf.meas.aestronglyMeasurable)
    rw [(measurePreserving_eval (fun _ : Fin k => ν) i).map_eq] at h
    exact h.symm
  have hmean : ∫ x, (k : ℝ)⁻¹ * Sf x ∂π = ∫ x, f x ∂ν := by
    rw [integral_const_mul, hSf,
      integral_finsetSum _ fun i _ => (hf.comp (measurable_pi_apply i)).integrable π]
    simp_rw [hmean1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- the variance
  have hvar : Var[fun x : Fin k → X => (k : ℝ)⁻¹ * Sf x; π] = (k : ℝ)⁻¹ * Var[f; ν] := by
    rw [variance_const_mul]
    have h := variance_sum_pi (μ := fun _ : Fin k => ν) (X := fun _ : Fin k => f)
      (fun _ => hfL)
    have e : (∑ i : Fin k, fun ω : Fin k → X => f (ω i)) = Sf := by
      funext ω
      simp [hSf, Finset.sum_apply]
    rw [e] at h
    rw [h]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hsub := BstLean.Part134.var_bm π bY
  have i2 : Integrable (fun x : Fin k → X => ((k : ℝ)⁻¹ * Sf x) ^ 2) π := bY.sq.integrable π
  have i1 : Integrable (fun x : Fin k → X => (k : ℝ)⁻¹ * Sf x) π := bY.integrable π
  refine ⟨((bY.sub (BstLean.Part105.BM.const b)).sq).integrable π, ?_⟩
  have hexp : ∀ x : Fin k → X, ((k : ℝ)⁻¹ * Sf x - b) ^ 2 =
      ((k : ℝ)⁻¹ * Sf x) ^ 2 - 2 * b * ((k : ℝ)⁻¹ * Sf x) + b ^ 2 := fun x => by ring
  change ∫ x : Fin k → X, ((k : ℝ)⁻¹ * Sf x - b) ^ 2 ∂π = _
  simp_rw [hexp]
  have h2 : ∫ x, ((k : ℝ)⁻¹ * Sf x) ^ 2 ∂π =
      (k : ℝ)⁻¹ * Var[f; ν] + (∫ x, f x ∂ν) ^ 2 := by
    rw [← hvar, hsub, hmean]
    ring
  have hI : ∫ x : Fin k → X, (((k : ℝ)⁻¹ * Sf x) ^ 2 - 2 * b * ((k : ℝ)⁻¹ * Sf x) + b ^ 2) ∂π =
      ∫ x, ((k : ℝ)⁻¹ * Sf x) ^ 2 ∂π - 2 * b * ∫ x, (k : ℝ)⁻¹ * Sf x ∂π + b ^ 2 := by
    rw [integral_add (f := fun x : Fin k → X => ((k : ℝ)⁻¹ * Sf x) ^ 2 -
        2 * b * ((k : ℝ)⁻¹ * Sf x)) (g := fun _ => b ^ 2) (i2.sub (i1.const_mul _))
        (integrable_const _),
      integral_sub (f := fun x : Fin k → X => ((k : ℝ)⁻¹ * Sf x) ^ 2)
        (g := fun x : Fin k → X => 2 * b * ((k : ℝ)⁻¹ * Sf x)) i2 (i1.const_mul _),
      integral_const_mul]
    simp
  rw [hI, h2, hmean]
  ring

/-! ## The sample estimate -/

section defs

variable {N m n mA mF : ℕ}

/-- The point of the cheap stand-in of `W` from the Gaussian vector `γ`:
`sphPt(M₃h̄ + τ₀γ)` before the normalization. -/
noncomputable def cheapPre (W : MlpParam N m n) (γ : Fin n → ℝ) : Fin n → ℝ :=
  W.2.2.mulVec (hbarW (W.1, W.2.1)) + tau0 N m (W.1, W.2.1) • γ

/-- **The sample estimate** `ĝ_k`: the mean of `F(A(y_i))` over the `k` points
`y_i = sphPt(M₃h̄ + τ₀γ_i)` of the cheap stand-in of `W`. -/
noncomputable def gSample (k : ℕ) (W : MlpParam N m n) (A : MlpParam n mA n)
    (F : MlpParam n mF 1) (γ : Fin k → Fin n → ℝ) : ℝ :=
  (k : ℝ)⁻¹ * ∑ i, phiS A F (cheapPre W (γ i))

lemma measurable_cheapPre (hN : 1 ≤ N) :
    Measurable (fun q : MlpParam N m n × (Fin n → ℝ) => cheapPre q.1 q.2) := by
  have hθ : Measurable (fun W : MlpParam N m n => ((W.1, W.2.1) : HidParam N m)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hc : Measurable (fun W : MlpParam N m n => W.2.2.mulVec (hbarW (W.1, W.2.1))) :=
    measurable_mulVec_joint.comp
      ((measurable_snd.comp measurable_snd).prodMk ((measurable_hbarW hN).comp hθ))
  have hτ : Measurable (fun W : MlpParam N m n => tau0 N m (W.1, W.2.1)) :=
    (measurable_tau0 hN).comp hθ
  unfold cheapPre
  exact (hc.comp measurable_fst).add ((hτ.comp measurable_fst).smul measurable_snd)

lemma measurable_cheapPre_W (W : MlpParam N m n) : Measurable (cheapPre W) := by
  unfold cheapPre
  exact measurable_const.add (measurable_const_smul _)

lemma gCheap_eq (hn : 1 ≤ n) (W : MlpParam N m n) (A : MlpParam n mA n) (F : MlpParam n mF 1) :
    gCheap W A F = ∫ γ, phiS A F (cheapPre W γ) ∂stdGauss (Fin n) := by
  unfold gCheap cheapW
  rw [← integral_phiS_cheapIn hn, integral_cheapIn _ _ (bm_phiS hn A F).meas]
  simp only [phiS, sphPt_idem hn]
  rfl

lemma measurable_gSample (hN : 1 ≤ N) (k : ℕ) :
    Measurable (fun p : (MlpParam N m n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin k → Fin n → ℝ) => gSample k p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold gSample
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
  have h1 : Measurable (fun p : (MlpParam N m n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin k → Fin n → ℝ) => cheapPre p.1.1 (p.2 i)) :=
    (measurable_cheapPre hN).comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  exact BstLean.Part131.continuous_phiN_all.measurable.comp
    ((measurable_snd.comp measurable_fst).prodMk (measurable_sphPt.comp h1))

end defs

/-! ## The error of the sample estimate, joint over `(W, A, F)` and the Gaussian vectors -/

/-- The distribution of the `k` Gaussian vectors. -/
noncomputable def gamK (k n : ℕ) : Measure (Fin k → Fin n → ℝ) :=
  Measure.pi fun _ : Fin k => stdGauss (Fin n)

instance (k n : ℕ) : IsProbabilityMeasure (gamK k n) := by unfold gamK; infer_instance

/-- `1_good(W)·(ĝ_k − B)²`, a function of `((W, A, F), γ)`. -/
noncomputable def errS (k n : ℕ)
    (p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) : ℝ :=
  (goodW n).indicator (fun W => (gSample k W p.1.2.1 p.1.2.2 p.2 -
    Part130.Bn W p.1.2.1 p.1.2.2) ^ 2) p.1.1

lemma errS_nonneg (k n : ℕ)
    (p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) : 0 ≤ errS k n p :=
  Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

lemma measurable_errS {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : Measurable (errS k n) := by
  have hN : 1 ≤ 2 * n := by omega
  have e : errS k n = ({p | p.1.1 ∈ goodW n} : Set ((MlpParam (2 * n) (mW n) n ×
      MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ))).indicator
      (fun p => (gSample k p.1.1 p.1.2.1 p.1.2.2 p.2 -
        Part130.Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2) := by
    funext p
    by_cases hp : p.1.1 ∈ goodW n
    · rw [Set.indicator_of_mem (show p ∈ {p : (MlpParam (2 * n) (mW n) n ×
        MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
        p.1.1 ∈ goodW n} from hp)]
      unfold errS
      rw [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem (show p ∉ {p : (MlpParam (2 * n) (mW n) n ×
        MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
        p.1.1 ∈ goodW n} from hp)]
      unfold errS
      rw [Set.indicator_of_notMem hp]
  rw [e]
  exact (((measurable_gSample hN k).sub
    ((BstLean.Part131.measurable_Bn hN).comp measurable_fst)).pow_const 2).indicator
    ((measurable_fst.comp measurable_fst) (goodW_meas hn))

section joint

variable {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {k : ℕ} (hk : 1 ≤ k)

include hn hζ0 hζ1 hk

/-- **The error of the sample estimate.** For `n ≥ 4096`, `0 < ζ < 1`, `k ≥ 1`:
`E[1_good(W)·(ĝ_k − B)²] ≤ (2·(0.99/n) + 8·EH n ζ + 1/k)·(4/n)`, the mean over `(W, A, F)` and
the `k` Gaussian vectors. -/
theorem errSample139_lint :
    ∫⁻ p, ENNReal.ofReal (errS k n p) ∂((mlpTriple 2 n).prod (gamK k n)) ≤
      ENNReal.ofReal ((2 * (99 / 100 / (n : ℝ)) + 8 * EH n ζ + (k : ℝ)⁻¹) * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have hEH := (EH_pos hn hζ0).le
  set PW := mlpGauss (2 * n) (mW n) n with hPW
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  have e0 : mlpTriple 2 n = PW.prod PAF := rfl
  have mf : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => ENNReal.ofReal (errS k n p)) :=
    ENNReal.measurable_ofReal.comp (measurable_errS hn1 k)
  rw [lintegral_prod _ mf.aemeasurable]
  -- the second moment term, as a function of `(W, (A, F))`
  set L : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => Lout (stdGauss (Fin n)) (cheapPre t.1) t.2 with hL
  have mL : Measurable L := by
    have hj : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin n → ℝ) =>
        ENNReal.ofReal (phiS q.1.2.1 q.1.2.2 (cheapPre q.1.1 q.2) ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((BstLean.Part131.continuous_phiN_all.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk (measurable_sphPt.comp
          ((measurable_cheapPre hN).comp ((measurable_fst.comp measurable_fst).prodMk
            measurable_snd))))).pow_const 2)
    exact hj.lintegral_prod_right'
  have hLint : ∫⁻ t, L t ∂mlpTriple 2 n = ENNReal.ofReal (4 / (n : ℝ)) := by
    rw [e0, lintegral_prod _ mL.aemeasurable]
    have h : ∀ W : MlpParam (2 * n) (mW n) n,
        ∫⁻ q, L (W, q) ∂PAF = ENNReal.ofReal (4 / (n : ℝ)) := by
      intro W
      have := lintegral_Lout (mA := mA n) (mF := mF n) (stdGauss (Fin n)) hn1 hmA hmF
        (measurable_cheapPre_W W)
      exact this
    simp_rw [h]
    simp
  have key : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ∫⁻ γ, ENNReal.ofReal (errS k n (t, γ)) ∂gamK k n ≤
        ENNReal.ofReal (errG n t) + ENNReal.ofReal ((k : ℝ)⁻¹) * L t := by
    rintro ⟨W, A, F⟩
    have ho : Measurable (cheapPre W) := measurable_cheapPre_W W
    have hφ : BstLean.Part105.BM (fun γ : Fin n → ℝ => phiS A F (cheapPre W γ)) :=
      (bm_phiS hn1 A F).comp ho
    obtain ⟨hi, he⟩ := iid_mean_sq (stdGauss (Fin n)) hφ hk (Part130.Bn W A F)
    by_cases hW : W ∈ goodW n
    · have e1 : ∀ γ : Fin k → Fin n → ℝ, errS k n ((W, A, F), γ) =
          ((k : ℝ)⁻¹ * ∑ i, phiS A F (cheapPre W (γ i)) - Part130.Bn W A F) ^ 2 := by
        intro γ
        simp only [errS, Set.indicator_of_mem hW, gSample]
      simp_rw [e1]
      rw [show gamK k n = Measure.pi (fun _ : Fin k => stdGauss (Fin n)) from rfl,
        ← ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
      have he' : ∫ x : Fin k → Fin n → ℝ, ((k : ℝ)⁻¹ * ∑ i, phiS A F (cheapPre W (x i)) -
          Part130.Bn W A F) ^ 2 ∂Measure.pi (fun _ : Fin k => stdGauss (Fin n)) =
          (∫ x, phiS A F (cheapPre W x) ∂stdGauss (Fin n) - Part130.Bn W A F) ^ 2 +
            (k : ℝ)⁻¹ * Var[fun γ : Fin n → ℝ => phiS A F (cheapPre W γ); stdGauss (Fin n)] := he
      rw [he', ← gCheap_eq hn1]
      have hv : Var[fun γ : Fin n → ℝ => phiS A F (cheapPre W γ); stdGauss (Fin n)] ≤
          ∫ γ, phiS A F (cheapPre W γ) ^ 2 ∂stdGauss (Fin n) := by
        rw [BstLean.Part134.var_bm (stdGauss (Fin n)) hφ]
        nlinarith [sq_nonneg (∫ γ, phiS A F (cheapPre W γ) ∂stdGauss (Fin n))]
      have hG : errG n (W, A, F) = (gCheap W A F - Part130.Bn W A F) ^ 2 := by
        simp only [errG, Set.indicator_of_mem hW]
      have i0 : 0 ≤ ∫ γ, phiS A F (cheapPre W γ) ^ 2 ∂stdGauss (Fin n) :=
        integral_nonneg fun _ => sq_nonneg _
      rw [hL]
      simp only
      rw [← ofReal_integral_out (stdGauss (Fin n)) hn1 A F ho, hG,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (sq_nonneg _)
          (mul_nonneg (by positivity) i0)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹)
      linarith
    · have e1 : ∀ γ : Fin k → Fin n → ℝ, errS k n ((W, A, F), γ) = 0 := by
        intro γ
        simp only [errS, Set.indicator_of_notMem hW]
      simp_rw [e1]
      simp
  calc ∫⁻ t, (∫⁻ γ, ENNReal.ofReal (errS k n (t, γ)) ∂gamK k n) ∂mlpTriple 2 n
      ≤ ∫⁻ t, (ENNReal.ofReal (errG n t) + ENNReal.ofReal ((k : ℝ)⁻¹) * L t) ∂mlpTriple 2 n :=
        lintegral_mono key
    _ = ∫⁻ t, ENNReal.ofReal (errG n t) ∂mlpTriple 2 n +
        ENNReal.ofReal ((k : ℝ)⁻¹) * ENNReal.ofReal (4 / (n : ℝ)) := by
        have m1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
            MlpParam n (mF n) 1 => ENNReal.ofReal (errG n t)) :=
          ENNReal.measurable_ofReal.comp (measurable_errG hn1)
        rw [lintegral_add_left m1, lintegral_const_mul _ mL, hLint]
    _ ≤ ENNReal.ofReal ((2 * (99 / 100 / (n : ℝ)) + 8 * EH n ζ) * (4 / (n : ℝ))) +
        ENNReal.ofReal ((k : ℝ)⁻¹) * ENNReal.ofReal (4 / (n : ℝ)) :=
        add_le_add (errVec139_lint hn hζ0 hζ1) le_rfl
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        ring

/-- The tail form: for `s > 0`:
`Pr(W good and (ĝ_k − B)² ≥ s) ≤ (2·(0.99/n) + 8·EH n ζ + 1/k)·(4/n)/s`. -/
theorem errSampleTail139 {s : ℝ} (hs : 0 < s) :
    ((mlpTriple 2 n).prod (gamK k n)).real {p | s ≤ errS k n p} ≤
      (2 * (99 / 100 / (n : ℝ)) + 8 * EH n ζ + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hEH := (EH_pos hn hζ0).le
  have h := errSample139_lint hn hζ0 hζ1 hk
  have hc : (0 : ℝ) ≤ (2 * (99 / 100 / (n : ℝ)) + 8 * EH n ζ + (k : ℝ)⁻¹) * (4 / (n : ℝ)) := by
    positivity
  have h0 : 0 ≤ᵐ[(mlpTriple 2 n).prod (gamK k n)] errS k n :=
    Filter.Eventually.of_forall (errS_nonneg k n)
  have hm := (measurable_errS hn1 k).aestronglyMeasurable
    (μ := (mlpTriple 2 n).prod (gamK k n))
  have hi : Integrable (errS k n) ((mlpTriple 2 n).prod (gamK k n)) :=
    ⟨hm, (hasFiniteIntegral_iff_ofReal h0).2 (lt_of_le_of_lt h ENNReal.ofReal_lt_top)⟩
  have hb : ∫ p, errS k n p ∂((mlpTriple 2 n).prod (gamK k n)) ≤
      (2 * (99 / 100 / (n : ℝ)) + 8 * EH n ζ + (k : ℝ)⁻¹) * (4 / (n : ℝ)) := by
    rw [integral_eq_lintegral_of_nonneg_ae h0 hm]
    exact ENNReal.toReal_le_of_le_ofReal hc h
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := (mlpTriple 2 n).prod (gamK k n))
    (f := errS k n) h0 hi s
  rw [le_div_iff₀ hs]
  linarith

end joint

/-! ## The headline for the sample estimate -/

/-- The success event of the sample estimate: `|ĝ_k − B| ≤ sd/2`. -/
def okSample (k n : ℕ) : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
    MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ)) :=
  {p | |gSample k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
    sdn p.1.1 p.1.2.1 p.1.2.2 / 2}

/-- An event of `(W, A, F)` has the same probability as an event of `((W, A, F), γ)`. -/
lemma prod_fst_real {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [SFinite μ] [IsProbabilityMeasure ν] (E : Set α) :
    (μ.prod ν).real {p | p.1 ∈ E} = μ.real E := by
  have e : {p : α × β | p.1 ∈ E} = E ×ˢ (Set.univ : Set β) := by ext p; simp
  rw [e, measureReal_def, Measure.prod_prod, measure_univ, mul_one, measureReal_def]

/-- The assembly of the three events: if the good event fails with probability at most `p₁`,
the squared error is at least `s` on the good event with probability at most `p₂`, and the
squared spread is below `4s` with probability at most `p₃`, then `|d| ≤ sd/2` with probability
at least `1 − (p₁ + p₂ + p₃)`. -/
lemma ok_of_three {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {G : Set Ω} {d sd : Ω → ℝ} (hsd : ∀ ω, 0 ≤ sd ω) {s p₁ p₂ p₃ : ℝ}
    (h1 : μ.real Gᶜ ≤ p₁) (h2 : μ.real {ω | ω ∈ G ∧ s ≤ d ω ^ 2} ≤ p₂)
    (h3 : μ.real {ω | sd ω ^ 2 < 4 * s} ≤ p₃) :
    1 - (p₁ + p₂ + p₃) ≤ μ.real {ω | |d ω| ≤ sd ω / 2} := by
  set OK : Set Ω := {ω | |d ω| ≤ sd ω / 2} with hOK
  have hcov : OKᶜ ⊆ Gᶜ ∪ ({ω | ω ∈ G ∧ s ≤ d ω ^ 2} ∪ {ω | sd ω ^ 2 < 4 * s}) := by
    intro ω hω
    by_cases hg : ω ∈ G
    swap
    · exact Or.inl hg
    by_cases he' : s ≤ d ω ^ 2
    · exact Or.inr (Or.inl ⟨hg, he'⟩)
    by_cases hsd' : sd ω ^ 2 < 4 * s
    · exact Or.inr (Or.inr hsd')
    have he := not_le.mp he'
    have hs4 := not_lt.mp hsd'
    exfalso
    apply hω
    change |d ω| ≤ sd ω / 2
    have h0 := hsd ω
    have hsq : d ω ^ 2 ≤ (sd ω / 2) ^ 2 := by nlinarith
    exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (by positivity))
  have hle : μ.real OKᶜ ≤ p₁ + (p₂ + p₃) := by
    calc μ.real OKᶜ ≤ μ.real (Gᶜ ∪ ({ω | ω ∈ G ∧ s ≤ d ω ^ 2} ∪ {ω | sd ω ^ 2 < 4 * s})) :=
          measureReal_mono hcov (measure_ne_top _ _)
      _ ≤ μ.real Gᶜ + μ.real ({ω | ω ∈ G ∧ s ≤ d ω ^ 2} ∪ {ω | sd ω ^ 2 < 4 * s}) :=
          measureReal_union_le _ _
      _ ≤ μ.real Gᶜ + (μ.real {ω | ω ∈ G ∧ s ≤ d ω ^ 2} + μ.real {ω | sd ω ^ 2 < 4 * s}) :=
          add_le_add le_rfl (measureReal_union_le _ _)
      _ ≤ _ := add_le_add h1 (add_le_add h2 h3)
  have hcompl : μ.real OK + μ.real OKᶜ ≥ 1 := by
    have a1 := measureReal_union_le (μ := μ) OK OKᶜ
    rw [Set.union_compl_self, probReal_univ] at a1
    exact a1
  linarith

/-- The arithmetic of the three terms at `θ = 1/10`, `ζ = 1/20`. -/
lemma rate_arith {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    2 / 1000 + ((2 * (99 / 100 / (n : ℝ)) + 8 * EH n (1 / 20) + (k : ℝ)⁻¹) * (4 / (n : ℝ)) /
        (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4)) +
      vSpread n / ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 ≤
    2 / 1000 + 1951 / (n : ℝ) + 180 / (k : ℝ) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have hy0 : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  have e : (2 * (99 / 100 / (n : ℝ)) + 8 * EH n (1 / 20) + (k : ℝ)⁻¹) * (4 / (n : ℝ)) /
        (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4) =
      4 * (2 * (99 / 100 / (n : ℝ)) + 8 * EH n (1 / 20)) / (1 / 10 * (1 - kappa^[6] 0)) +
        4 * (k : ℝ)⁻¹ / (1 / 10 * (1 - kappa^[6] 0)) := by
    field_simp
  rw [e]
  have hv := vSpread_scale hn
  have hv0 : 0 ≤ vSpread n := by unfold vSpread; positivity
  have hEH := EH_le hn
  have hEH0 := (EH_pos hn (by norm_num : (0 : ℝ) < 1 / 20)).le
  have hnm := n_div_mW_scale hn
  set t : ℝ := 1 / (n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have hEH' : EH n (1 / 20) ≤ 470 / 262144 * t := by
    have e : 470 * (n : ℝ) / (mW n : ℝ) = 470 * ((n : ℝ) / (mW n : ℝ)) := by ring
    rw [e] at hEH
    have e2 : (1 : ℝ) / 262144 / (n : ℝ) = 1 / 262144 * t := by rw [ht]; ring
    rw [e2] at hnm
    linarith
  have e99 : 99 / 100 / (n : ℝ) = 99 / 100 * t := by rw [ht]; ring
  have e64 : 64 / (n : ℝ) = 64 * t := by rw [ht]; ring
  have e1951 : 1951 / (n : ℝ) = 1951 * t := by rw [ht]; ring
  rw [e64] at hv
  have t1 : 4 * (2 * (99 / 100 / (n : ℝ)) + 8 * EH n (1 / 20)) /
      (1 / 10 * (1 - kappa^[6] 0)) ≤ 3582 / 10 * t := by
    rw [e99, div_le_iff₀ (by nlinarith)]
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
  rw [e1951]
  linarith

/-- **The sample estimate succeeds (item 4).** For every `n ≥ 4096` and every `k ≥ 1`, with
`ĝ_k` the mean of `F(A(·))` over `k` independent points of the cheap stand-in of `W`:
`Pr(|ĝ_k − B| ≤ sd/2) ≥ 1 − (0.002 + 1951/n + 180/k)`, the probability over `(W, A, F)` and the
`k` Gaussian vectors. -/
theorem sampleSucceeds139 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    1 - (2 / 1000 + 1951 / (n : ℝ) + 180 / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okSample k n) := by
  have hx0 : (0 : ℝ) < n := by have := nR_ge hn; linarith
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have hs0 : (0 : ℝ) < 1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 := by
    have : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
    positivity
  have h1 : ((mlpTriple 2 n).prod (gamK k n)).real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodW n}ᶜ ≤ 2 / 1000 :=
    (prod_fst_real (mlpTriple 2 n) (gamK k n) {t | t.1 ∉ goodW n}).trans_le (bad_prob hn)
  have h2 : ((mlpTriple 2 n).prod (gamK k n)).real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p ∈ {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodW n} ∧
        1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 ≤
          (gSample k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2} ≤
      (2 * (99 / 100 / (n : ℝ)) + 8 * EH n (1 / 20) + (k : ℝ)⁻¹) * (4 / (n : ℝ)) /
        (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4) := by
    refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
      (errSampleTail139 hn (ζ := 1 / 20) (by norm_num) (by norm_num) hk hs0)
    rintro p ⟨hg, he⟩
    change _ ≤ errS k n p
    unfold errS
    rw [Set.indicator_of_mem (show p.1.1 ∈ goodW n from hg)]
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
    (d := fun p => gSample k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2)
    (sd := fun p => sdn p.1.1 p.1.2.1 p.1.2.2) (fun p => sdn_nonneg' _ _ _) h1 h2 h3
  have ha := rate_arith hn hk
  exact le_trans (by linarith) h

end BstLean.Part139

open BstLean.Part139 in
#print axioms iid_mean_sq
open BstLean.Part139 in
#print axioms errSample139_lint
open BstLean.Part139 in
#print axioms sampleSucceeds139
