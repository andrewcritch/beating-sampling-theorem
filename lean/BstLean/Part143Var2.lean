import BstLean.Part143Var

/-!
# Part 143 (helper `lam16`), step 2b: the error bound of Part 142 with a general frame constant

`VbL L n`, `XAL L n ζ η η′`: `Vb`, `XA142` of Part 142 with `L` in the place of `183/100`.
**`errSampleTailAL`**: `errSampleTailA142` with `XAL L`, for every `n ≥ 4096`, `L ≥ 0` and the
frame bound `L/n` on `goodHat n` as a hypothesis. **`errSampleTailA143`**: `n ≥ 16384`,
`L = L143 = 137/100`. `VbL143_le`, `XAL143_le_gen`, `XAL143_le`, `XAL143_le'`: numbers for
`n ≥ 16384`. The proofs are those of `Part142Var2` with the constant replaced.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142

/-- `Vb` of Part 142 with the frame constant `L`. -/
noncomputable def VbL (L : ℝ) (n : ℕ) : ℝ :=
  1 - kappa^[6] 0 + sig4 * (eWr (2 * n) n (mW n) + sU (2 * n)) + eAFr n (mA n) (mF n) +
    L / (n : ℝ)

/-- `XA142` of Part 142 with the frame constant `L`. -/
noncomputable def XAL (L : ℝ) (n : ℕ) (ζ η η' : ℝ) : ℝ :=
  (1 + η') * ((1 + η) * (L / (n : ℝ)) * VbL L n + 4 * (1 + 1 / η) * EHH n ζ) +
    (1 + 1 / η') * pertA n

lemma VbL_183 (n : ℕ) : VbL (183 / 100) n = Vb n := rfl

lemma XAL_183 (n : ℕ) (ζ η η' : ℝ) : XAL (183 / 100) n ζ η η' = XA142 n ζ η η' := rfl

lemma VbL_nonneg {n : ℕ} (hn : 4096 ≤ n) {Lc : ℝ} (hLc0 : 0 ≤ Lc) : 0 ≤ VbL Lc n := by
  obtain ⟨l, rfl⟩ : ∃ l : ℝ, Lc = l ^ 2 := ⟨√Lc, (Real.sq_sqrt hLc0).symm⟩
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have h1 : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have h2 := sig4_nonneg
  have h3 := eWr_nonneg142 hn1 (2 * n) (mW n)
  have h4 := sU_nonneg (2 * n)
  have h5 := eAFr_nonneg142 hn1 hmA hmF
  have h6 : (0 : ℝ) ≤ 1 - kappa^[6] 0 := by linarith
  unfold VbL
  positivity

lemma XAL_nonneg {n : ℕ} (hn : 4096 ≤ n) {Lc : ℝ} (hLc0 : 0 ≤ Lc) (ζ : ℝ) {η : ℝ} (hη : 0 < η) {η' : ℝ}
    (hη' : 0 < η') : 0 ≤ XAL Lc n ζ η η' := by
  obtain ⟨l, rfl⟩ : ∃ l : ℝ, Lc = l ^ 2 := ⟨√Lc, (Real.sq_sqrt hLc0).symm⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hEH := EHH_nonneg hn ζ
  have hp := pertA_nonneg n
  have hV := VbL_nonneg hn hLc0
  unfold XAL
  positivity

/-- **`errVecHat_lint` of Part 140 with the variance of the stand-in.** -/
theorem errVecHatL_lint {n : ℕ} (hn : 4096 ≤ n) {Lc : ℝ} (hLc0 : 0 ≤ Lc) (hLc : FrameL Lc n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ}
    (hη : 0 < η) :
    ∫⁻ t, ENNReal.ofReal (errGH n t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (((1 + η) * (Lc / (n : ℝ)) * VbL Lc n +
        4 * (1 + 1 / η) * EHH n ζ) * (4 / (n : ℝ))) := by
  obtain ⟨l, rfl⟩ : ∃ l : ℝ, Lc = l ^ 2 := ⟨√Lc, (Real.sq_sqrt hLc0).symm⟩
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have mE := goodHat_meas (n := n) hn1
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  set gM := gaussMat n (mW n) (2 / (mW n : ℝ)) with hgM
  set f : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => ENNReal.ofReal (errGH n t) with hf
  have mf : Measurable f := ENNReal.measurable_ofReal.comp (measurable_errGH hn1)
  set G : MlpParam (2 * n) (mW n) n → ℝ≥0∞ := fun W => ∫⁻ p, f (W, p) ∂PAF with hG
  have mG : Measurable G := mf.lintegral_prod_right'
  have e : mlpGauss (2 * n) (mW n) n =
      ((hidGauss (2 * n) (mW n)).prod gM).map MeasurableEquiv.prodAssoc := by
    unfold mlpGauss hidGauss
    rw [Measure.prodAssoc_prod]
  have step1 : ∫⁻ t, f t ∂mlpTriple 2 n =
      ∫⁻ θ, (∫⁻ M₃, G (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n) := by
    have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod PAF := rfl
    rw [e0, lintegral_prod _ mf.aemeasurable]
    change ∫⁻ W, G W ∂mlpGauss (2 * n) (mW n) n = _
    rw [e, lintegral_map mG MeasurableEquiv.prodAssoc.measurable]
    exact lintegral_prod (fun a => G (MeasurableEquiv.prodAssoc a))
      (mG.comp MeasurableEquiv.prodAssoc.measurable).aemeasurable
  -- the bound for fixed θ
  set a : ℝ := (1 + η) * ((l ^ 2) / (n : ℝ)) with ha
  set S : ℝ := 4 / (n : ℝ) with hS
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have he0 : 0 ≤ eAFr n (mA n) (mF n) := by
    have hcF := BstLean.Part133.cF2o_pos hmF
    have hcA := cAr_pos (kGood_kappa.comp_kappa) hmA hn1
    unfold eAFr; positivity
  set δ : ℝ := (l ^ 2) / (n : ℝ) with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  set dd : HidParam (2 * n) (mW n) → ℝ := fun θ => DTh n θ + eAFr n (mA n) (mF n) + δ with hdd
  have hdd0 : ∀ θ, 0 ≤ dd θ := fun θ => by
    have := DTh_nonneg hn1 θ
    rw [hdd]; positivity
  set k : HidParam (2 * n) (mW n) → ℝ := fun θ =>
    a * S * (goodHat n).indicator dd θ +
      4 * (1 + 1 / η) * S * (goodHat n).indicator (HbarH n ζ) θ with hk
  have hk0 : ∀ θ, 0 ≤ k θ := by
    intro θ
    have h1 : 0 ≤ (goodHat n).indicator dd θ :=
      Set.indicator_nonneg (fun θ _ => hdd0 θ) _
    have h2 : 0 ≤ (goodHat n).indicator (HbarH n ζ) θ :=
      Set.indicator_nonneg (fun θ _ => HbarH_nonneg n ζ θ) _
    rw [hk]
    positivity
  have step2 : ∀ θ : HidParam (2 * n) (mW n),
      ∫⁻ M₃, G (θ.1, θ.2, M₃) ∂gM ≤ ENNReal.ofReal (k θ) := by
    intro θ
    have msec : Measurable (fun q : Matrix (Fin n) (Fin (mW n)) ℝ ×
        (MlpParam n (mA n) n × MlpParam n (mF n) 1) =>
        (((θ.1, θ.2, q.1) : MlpParam (2 * n) (mW n) n), q.2)) :=
      ((measurable_const.prodMk (measurable_const.prodMk measurable_fst))).prodMk measurable_snd
    have hswap : ∫⁻ M₃, G (θ.1, θ.2, M₃) ∂gM =
        ∫⁻ p, (∫⁻ M₃, f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) ∂gM) ∂PAF :=
      lintegral_lintegral_swap
        (f := fun (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ)
          (p : MlpParam n (mA n) n × MlpParam n (mF n) 1) =>
          f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p)) (mf.comp msec).aemeasurable
    rw [hswap]
    by_cases hθ : θ ∈ goodHat n
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∈ goodWH n := fun M₃ => hθ
      have hin : ∀ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
          ∫⁻ M₃, f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) ∂gM =
          ENNReal.ofReal (∫ M₃, (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)
            p.1 p.2 - gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2 ∂gM) := by
        rintro ⟨A, F⟩
        have hφ : BM (phiS A F) := bm_phiS hn1 A F
        have hb : BM (fun W : MlpParam (2 * n) (mW n) n =>
            ((∫ x, phiS A F x ∂muWn W) - ∫ x, phiS A F x ∂cheapHat W) ^ 2) :=
          ((bm_muW hN hφ).sub (bm_cheapHat hN hφ)).sq
        have hb' : BM (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
            (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F -
              gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F) ^ 2) := by
          have h1 := hb.comp (g := fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
            ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n))
            (measurable_const.prodMk (measurable_const.prodMk measurable_id))
          refine ⟨?_, h1.bdd.imp fun M hM M₃ => ?_⟩
          · convert h1.meas using 2 with M₃
            rw [integral_phiS_muWn hn1]
            unfold cheapHat gHat
            rw [integral_phiS_cheapIn hn1]
            rfl
          · have := hM M₃
            rw [integral_phiS_muWn hn1] at this
            unfold cheapHat at this
            rw [integral_phiS_cheapIn hn1] at this
            exact this
        rw [ofReal_integral_eq_lintegral_ofReal (hb'.integrable gM)
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
        refine lintegral_congr fun M₃ => ?_
        simp only [hf, errGH, Set.indicator_of_mem (hW M₃)]
        congr 1
        ring
      simp_rw [hin]
      refine (errFixedHatL hn hLc0 hLc hθ hζ0.le hζ1 hη).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hk]
      simp only [Set.indicator_of_mem hθ]
      rw [ha, hS, hdd, hδ]
      apply le_of_eq
      ring
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∉ goodWH n := fun M₃ => hθ
      have hz : ∀ (p : MlpParam n (mA n) n × MlpParam n (mF n) 1)
          (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ),
          f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) = 0 := by
        intro p M₃
        simp only [hf, errGH, Set.indicator_of_notMem (hW M₃), ENNReal.ofReal_zero]
      simp_rw [hz]
      simp
  obtain ⟨iH, hH⟩ := HbarH_mean hn hζ0 hζ1
  obtain ⟨iD, hDb⟩ := DTh_mean hn
  have idd : Integrable dd (hidGauss (2 * n) (mW n)) :=
    (iD.add (integrable_const _)).add (integrable_const _)
  have i1 : Integrable (fun θ : HidParam (2 * n) (mW n) =>
      a * S * (goodHat n).indicator dd θ) (hidGauss (2 * n) (mW n)) :=
    (idd.indicator mE).const_mul _
  have i2 : Integrable (fun θ : HidParam (2 * n) (mW n) =>
      4 * (1 + 1 / η) * S * (goodHat n).indicator (HbarH n ζ) θ) (hidGauss (2 * n) (mW n)) := iH.const_mul _
  have ik : Integrable k (hidGauss (2 * n) (mW n)) := i1.add i2
  rw [step1]
  calc ∫⁻ θ, (∫⁻ M₃, G (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n)
      ≤ ∫⁻ θ, ENNReal.ofReal (k θ) ∂hidGauss (2 * n) (mW n) := lintegral_mono step2
    _ = ENNReal.ofReal (∫ θ, k θ ∂hidGauss (2 * n) (mW n)) :=
        (ofReal_integral_eq_lintegral_ofReal ik (Filter.Eventually.of_forall hk0)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hk, integral_add i1 i2, integral_const_mul, integral_const_mul]
        have e1 : ∫ θ, (goodHat n).indicator dd θ ∂hidGauss (2 * n) (mW n) ≤ VbL (l ^ 2) n := by
          have h0 : ∫ θ, (goodHat n).indicator dd θ ∂hidGauss (2 * n) (mW n) ≤
              ∫ θ, dd θ ∂hidGauss (2 * n) (mW n) :=
            integral_mono (idd.indicator mE) idd
              (fun θ => Set.indicator_le_self' (fun θ _ => hdd0 θ) θ)
          have h1 : ∫ θ, dd θ ∂hidGauss (2 * n) (mW n) =
              (∫ θ, DTh n θ ∂hidGauss (2 * n) (mW n)) + eAFr n (mA n) (mF n) + δ := by
            have e' : dd = fun θ => (DTh n θ + (fun _ => eAFr n (mA n) (mF n)) θ) +
                (fun _ => δ) θ := by rw [hdd]
            rw [e', integral_add (f := fun θ => DTh n θ + (fun _ => eAFr n (mA n) (mF n)) θ)
                (iD.add (integrable_const _)) (integrable_const _),
              integral_add (f := fun θ => DTh n θ) iD (integrable_const _)]
            simp
          unfold VbL
          rw [h1] at h0
          linarith
        have h1 := mul_le_mul_of_nonneg_left e1 (mul_nonneg ha0 hS0)
        have h2 := mul_le_mul_of_nonneg_left hH (by positivity : (0 : ℝ) ≤ 4 * (1 + 1 / η) * S)
        rw [ha, hS] at h1
        rw [hS] at h2
        rw [ha, hS]
        linarith


/-- **`errVecA_lint` of Part 141 with the variance of the stand-in.** -/
theorem errVecAL_lint {n : ℕ} (hn : 4096 ≤ n) {Lc : ℝ} (hLc0 : 0 ≤ Lc) (hLc : FrameL Lc n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ}
    (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') :
    ∫⁻ t, ENNReal.ofReal (errGA n t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (XAL Lc n ζ η η' * (4 / (n : ℝ))) := by
  obtain ⟨l, rfl⟩ : ∃ l : ℝ, Lc = l ^ 2 := ⟨√Lc, (Real.sq_sqrt hLc0).symm⟩
  have hVb := VbL_nonneg hn hLc0
  unfold XAL
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hEH := EHH_nonneg hn ζ
  have hp := pertA_nonneg n
  have m1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ENNReal.ofReal (errGH n t)) :=
    ENNReal.measurable_ofReal.comp (measurable_errGH hn1)
  have m2 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ENNReal.ofReal (dGA n t)) :=
    ENNReal.measurable_ofReal.comp (measurable_dGA hn1)
  have key : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal (errGA n t) ≤
        ENNReal.ofReal (1 + η') * ENNReal.ofReal (errGH n t) +
          ENNReal.ofReal (1 + 1 / η') * ENNReal.ofReal (dGA n t) := by
    intro t
    have h0 := errGH_nonneg n t
    have h0' := dGA_nonneg n t
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases ht : t.1 ∈ goodWA n
    · have ht' : t.1 ∈ goodWH n := goodWA_sub n ht
      simp only [errGA, errGH, dGA, Set.indicator_of_mem ht, Set.indicator_of_mem ht']
      have hs := sq_split (η := 1 / η') (by positivity) (gA t.1 t.2.1 t.2.2)
        (gHat t.1 t.2.1 t.2.2) (Part130.Bn t.1 t.2.1 t.2.2)
      rw [one_div_one_div] at hs
      linarith
    · simp only [errGA, Set.indicator_of_notMem ht]
      positivity
  calc ∫⁻ t, ENNReal.ofReal (errGA n t) ∂mlpTriple 2 n
      ≤ ∫⁻ t, (ENNReal.ofReal (1 + η') * ENNReal.ofReal (errGH n t) +
          ENNReal.ofReal (1 + 1 / η') * ENNReal.ofReal (dGA n t)) ∂mlpTriple 2 n :=
        lintegral_mono key
    _ = ENNReal.ofReal (1 + η') * ∫⁻ t, ENNReal.ofReal (errGH n t) ∂mlpTriple 2 n +
          ENNReal.ofReal (1 + 1 / η') * ∫⁻ t, ENNReal.ofReal (dGA n t) ∂mlpTriple 2 n := by
        rw [lintegral_add_left (m1.const_mul _), lintegral_const_mul _ m1,
          lintegral_const_mul _ m2]
    _ ≤ ENNReal.ofReal (1 + η') * ENNReal.ofReal (((1 + η) * ((l ^ 2) / (n : ℝ)) * VbL (l ^ 2) n +
            4 * (1 + 1 / η) * EHH n ζ) * (4 / (n : ℝ))) +
          ENNReal.ofReal (1 + 1 / η') * ENNReal.ofReal (pertA n * (4 / (n : ℝ))) :=
        add_le_add (mul_le_mul' le_rfl (errVecHatL_lint hn hLc0 hLc hζ0 hζ1 hη))
          (mul_le_mul' le_rfl (diffVecA_lint hn))
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring


/-- **`errSampleA_lint` of Part 141 with the variance of the stand-in.** For `n ≥ 4096`,
`0 < ζ < 1`, `k ≥ 1`: `E[1_good(W)·(g̃_k − B)²] ≤ (XAL (l ^ 2) n ζ η η′ + 1/k)·(4/n)`. -/
theorem errSampleAL_lint {n : ℕ} (hn : 4096 ≤ n) {Lc : ℝ} (hLc0 : 0 ≤ Lc) (hLc : FrameL Lc n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ p, ENNReal.ofReal (errSA k n p) ∂((mlpTriple 2 n).prod (gamK k n)) ≤
      ENNReal.ofReal ((XAL Lc n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ))) := by
  obtain ⟨l, rfl⟩ : ∃ l : ℝ, Lc = l ^ 2 := ⟨√Lc, (Real.sq_sqrt hLc0).symm⟩
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have hX := XAL_nonneg hn hLc0 ζ hη hη'
  set PW := mlpGauss (2 * n) (mW n) n with hPW
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  have e0 : mlpTriple 2 n = PW.prod PAF := rfl
  have mf : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => ENNReal.ofReal (errSA k n p)) :=
    ENNReal.measurable_ofReal.comp (measurable_errSA hn1 k)
  rw [lintegral_prod _ mf.aemeasurable]
  -- the second moment term, as a function of `(W, (A, F))`
  set Lo : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => Lout (stdGauss (Fin n)) (preA t.1) t.2 with hLo
  have mL : Measurable Lo := by
    have hj : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin n → ℝ) =>
        ENNReal.ofReal (phiS q.1.2.1 q.1.2.2 (preA q.1.1 q.2) ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((BstLean.Part131.continuous_phiN_all.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk (measurable_sphPt.comp
          (measurable_preA.comp ((measurable_fst.comp measurable_fst).prodMk
            measurable_snd))))).pow_const 2)
    exact hj.lintegral_prod_right'
  have hLint : ∫⁻ t, Lo t ∂mlpTriple 2 n = ENNReal.ofReal (4 / (n : ℝ)) := by
    rw [e0, lintegral_prod _ mL.aemeasurable]
    have h : ∀ W : MlpParam (2 * n) (mW n) n,
        ∫⁻ q, Lo (W, q) ∂PAF = ENNReal.ofReal (4 / (n : ℝ)) := by
      intro W
      have := lintegral_Lout (mA := mA n) (mF := mF n) (stdGauss (Fin n)) hn1 hmA hmF
        (measurable_preA_W W)
      exact this
    simp_rw [h]
    simp
  have key : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ∫⁻ γ, ENNReal.ofReal (errSA k n (t, γ)) ∂gamK k n ≤
        ENNReal.ofReal (errGA n t) + ENNReal.ofReal ((k : ℝ)⁻¹) * Lo t := by
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
      rw [hLo]
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
      ≤ ∫⁻ t, (ENNReal.ofReal (errGA n t) + ENNReal.ofReal ((k : ℝ)⁻¹) * Lo t) ∂mlpTriple 2 n :=
        lintegral_mono key
    _ = ∫⁻ t, ENNReal.ofReal (errGA n t) ∂mlpTriple 2 n +
        ENNReal.ofReal ((k : ℝ)⁻¹) * ENNReal.ofReal (4 / (n : ℝ)) := by
        have m1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
            MlpParam n (mF n) 1 => ENNReal.ofReal (errGA n t)) :=
          ENNReal.measurable_ofReal.comp (measurable_errGA hn1)
        rw [lintegral_add_left m1, lintegral_const_mul _ mL, hLint]
    _ ≤ ENNReal.ofReal (XAL (l ^ 2) n ζ η η' * (4 / (n : ℝ))) +
        ENNReal.ofReal ((k : ℝ)⁻¹) * ENNReal.ofReal (4 / (n : ℝ)) :=
        add_le_add (errVecAL_lint hn hLc0 hLc hζ0 hζ1 hη hη') le_rfl
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        ring

/-- The tail form: for `s > 0`:
`Pr(W good and (g̃_k − B)² ≥ s) ≤ (XA n ζ η η′ + 1/k)·(4/n)/s`. -/
theorem errSampleTailAL' {n : ℕ} (hn : 4096 ≤ n) {Lc : ℝ} (hLc0 : 0 ≤ Lc) (hLc : FrameL Lc n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') {k : ℕ} (hk : 1 ≤ k) {s : ℝ} (hs : 0 < s) :
    ((mlpTriple 2 n).prod (gamK k n)).real {p | s ≤ errSA k n p} ≤
      (XAL Lc n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s := by
  obtain ⟨l, rfl⟩ : ∃ l : ℝ, Lc = l ^ 2 := ⟨√Lc, (Real.sq_sqrt hLc0).symm⟩
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hX := XAL_nonneg hn hLc0 ζ hη hη'
  have h := errSampleAL_lint hn hLc0 hLc hζ0 hζ1 hη hη' hk
  have hc : (0 : ℝ) ≤ (XAL (l ^ 2) n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ)) := by positivity
  have h0 : 0 ≤ᵐ[(mlpTriple 2 n).prod (gamK k n)] errSA k n :=
    Filter.Eventually.of_forall (errSA_nonneg k n)
  have hm := (measurable_errSA hn1 k).aestronglyMeasurable
    (μ := (mlpTriple 2 n).prod (gamK k n))
  have hi : Integrable (errSA k n) ((mlpTriple 2 n).prod (gamK k n)) :=
    ⟨hm, (hasFiniteIntegral_iff_ofReal h0).2 (lt_of_le_of_lt h ENNReal.ofReal_lt_top)⟩
  have hb : ∫ p, errSA k n p ∂((mlpTriple 2 n).prod (gamK k n)) ≤
      (XAL (l ^ 2) n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ)) := by
    rw [integral_eq_lintegral_of_nonneg_ae h0 hm]
    exact ENNReal.toReal_le_of_le_ofReal hc h
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := (mlpTriple 2 n).prod (gamK k n))
    (f := errSA k n) h0 hi s
  rw [le_div_iff₀ hs]
  linarith


/-! ## The headline statements -/

/-- **`errSampleTailA142` with a general frame constant `L`.** For `n ≥ 4096`, `L ≥ 0` and the
frame bound `L/n` of the computed centre on `goodHat n`:
`Pr(W good and (g̃_k − B)² ≥ s) ≤ (XAL L n ζ η η′ + 1/k)·(4/n)/s`. -/
theorem errSampleTailAL {n : ℕ} (hn : 4096 ≤ n) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ θ ∈ goodHat n, ∀ w : Fin (mW n) → ℝ,
      ∫ u, (∑ j, eDir (bhat θ) (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n) ≤
        L / (n : ℝ) * ∑ j, w j ^ 2)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η')
    {k : ℕ} (hk : 1 ≤ k) {s : ℝ} (hs : 0 < s) :
    ((mlpTriple 2 n).prod (gamK k n)).real {p | s ≤ errSA k n p} ≤
      (XAL L n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s :=
  errSampleTailAL' hn hL0 hL hζ0 hζ1 hη hη' hk hs

/-- **The error bound of Part 142 for `n ≥ 16384`, with the stand-in factor `L143 = 137/100`.** -/
theorem errSampleTailA143 {n : ℕ} (hn : 16384 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') {k : ℕ} (hk : 1 ≤ k) {s : ℝ} (hs : 0 < s) :
    ((mlpTriple 2 n).prod (gamK k n)).real {p | s ≤ errSA k n p} ≤
      (XAL L143 n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s :=
  errSampleTailAL (by omega) L143_nonneg (fun _ hθ w => frameHat143 hn hθ w)
    hζ0 hζ1 hη hη' hk hs

/-- The lintegral form for `n ≥ 16384`. -/
theorem errSampleA143_lint {n : ℕ} (hn : 16384 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ p, ENNReal.ofReal (errSA k n p) ∂((mlpTriple 2 n).prod (gamK k n)) ≤
      ENNReal.ofReal ((XAL L143 n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ))) :=
  errSampleAL_lint (by omega) L143_nonneg (frameL_143 hn) hζ0 hζ1 hη hη' hk

/-! ## Numbers for `n ≥ 16384` -/

/-- `VbL L143 n ≤ 0.2481` for `n ≥ 16384` (Part 142: `Vb n ≤ 0.2736` for `n ≥ 4096`). -/
lemma VbL143_le {n : ℕ} (hn16 : 16384 ≤ n) : VbL L143 n ≤ 2481 / 10000 := by
  have hn : 4096 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn16
  have hx0 : (0 : ℝ) < n := by linarith
  have hs : (128 : ℝ) ≤ √(n : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h1 := eAFr_scale hn
  have h2 := eWr_scale hn
  have h3 := sU_scale hn
  have h4 := sig4_le
  have h40 := sig4_nonneg
  have hsU := sU_nonneg (2 * n)
  have hW0 := eWr_nonneg142 hn1 (2 * n) (mW n)
  have hQ : 7771 / 10000 ≤ kappa^[6] 0 := kappa6_zero_ge'
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 / 128 := by
    rw [ht]
    exact one_div_le_one_div_of_le (by norm_num) hs
  have e1 : (25365 : ℝ) / 10000 / √(n : ℝ) = 25365 / 10000 * t := by rw [ht]; ring
  have e2 : (11746 : ℝ) / 10000 / √(n : ℝ) = 11746 / 10000 * t := by rw [ht]; ring
  have e3 : (3629 : ℝ) / 10000 / √(n : ℝ) = 3629 / 10000 * t := by rw [ht]; ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  have h5 : sig4 * (eWr (2 * n) n (mW n) + sU (2 * n)) ≤
      4404 / 10000 * (15375 / 10000 * t) := by
    apply mul_le_mul h4 (by linarith) (by positivity) (by norm_num)
  have h6 : 137 / 100 / (n : ℝ) ≤ 137 / 100 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  unfold VbL L143
  nlinarith

/-- The general form: for `n ≥ 16384`, `η, η′ > 0`:
`XAL L143 n (1/20) η η′ ≤ ((1 + η′)((1 + η)·1.37·0.2481 + 4(1 + 1/η)·250/262144)
  + (1 + 1/η′)·27501/10⁸)/n`. -/
lemma XAL143_le_gen {n : ℕ} (hn16 : 16384 ≤ n) {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') :
    XAL L143 n (1 / 20) η η' ≤
      ((1 + η') * ((1 + η) * (137 / 100 * (2481 / 10000)) + 4 * (1 + 1 / η) * (250 / 262144)) +
        (1 + 1 / η') * (27501 / 100000000)) * (1 / (n : ℝ)) := by
  have hn : 4096 ≤ n := by omega
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn16
  have hx0 : (0 : ℝ) < n := by linarith
  have hEH' := EHH_scale hn
  have hp := pertA_eq (n := n) (by omega)
  have ht0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hV := VbL143_le hn16
  unfold XAL
  have eL : L143 / (n : ℝ) = 137 / 100 * (1 / (n : ℝ)) := by unfold L143; ring
  rw [eL, hp]
  have h1 : (1 + η) * (137 / 100 * (1 / (n : ℝ))) * VbL L143 n ≤
      (1 + η) * (137 / 100 * (1 / (n : ℝ))) * (2481 / 10000) :=
    mul_le_mul_of_nonneg_left hV (by positivity)
  have h2 : 4 * (1 + 1 / η) * EHH n (1 / 20) ≤
      4 * (1 + 1 / η) * (250 / 262144 * (1 / (n : ℝ))) :=
    mul_le_mul_of_nonneg_left hEH' (by positivity)
  have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity : (0 : ℝ) ≤ 1 + η')
  refine (add_le_add h3 le_rfl).trans (le_of_eq ?_)
  ring

/-- `XAL L143 n (1/20) (1/20) (1/100) ≤ 0.47/n` for `n ≥ 16384` (Part 142: `0.64/n`). -/
lemma XAL143_le {n : ℕ} (hn16 : 16384 ≤ n) :
    XAL L143 n (1 / 20) (1 / 20) (1 / 100) ≤ 47 / 100 * (1 / (n : ℝ)) := by
  have hx0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine (XAL143_le_gen hn16 (by norm_num) (by norm_num)).trans ?_
  exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-- `XAL L143 n (1/20) (1/10) (1/40) ≤ 0.438/n` for `n ≥ 16384`: the best of the choices of
`(η, η′)` tried. -/
lemma XAL143_le' {n : ℕ} (hn16 : 16384 ≤ n) :
    XAL L143 n (1 / 20) (1 / 10) (1 / 40) ≤ 438 / 1000 * (1 / (n : ℝ)) := by
  have hx0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine (XAL143_le_gen hn16 (by norm_num) (by norm_num)).trans ?_
  exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

end BstLean.Part143

open BstLean.Part143 in
#print axioms errSampleTailAL
open BstLean.Part143 in
#print axioms errSampleTailA143
open BstLean.Part143 in
#print axioms errSampleA143_lint
open BstLean.Part143 in
#print axioms VbL143_le
open BstLean.Part143 in
#print axioms XAL143_le_gen
open BstLean.Part143 in
#print axioms XAL143_le
open BstLean.Part143 in
#print axioms XAL143_le'
