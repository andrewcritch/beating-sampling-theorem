import BstLean.Part133Cos
import BstLean.Part133Relu

/-!
# Part 133: the World network in `L²`

Role: `delegations/statements/p133-spec.md`. Paper source: `onW4c-cx.md` §4 (links `W_3`,
`W_2`, `W_1`, `u`).

* `sphere_kk_L2`: `‖κ(κ(⟨u, u′⟩)) − κ(κ(0))‖₂ ≤ 1/√N` for two independent uniform unit vectors.
* `world_cos_L2`: for unit `u, u′`: `‖⟨x(u), x(u′)⟩ − κ(κ(⟨u, u′⟩))‖_{L²(W)} ≤ eW2 n m`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part133

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere
  uniformSphere_moments)
open BstLean.Part130 BstLean.Part131 BstLean.Part132

variable {N m n : ℕ}

/-! ## The inputs -/

/-- `E⟨u, u′⟩² = 1/N` for two independent uniform unit vectors of `ℝ^N`. -/
lemma lawU2_dot_sq (hN : 1 ≤ N) :
    Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => dotp uu.1 uu.2 ^ 2) (lawU2 N) ∧
    ∫ uu, dotp uu.1 uu.2 ^ 2 ∂lawU2 N = 1 / (N : ℝ) := by
  have := uniformSphere_isProbability N hN
  have hmom := uniformSphere_moments N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have e : ∀ uu : (Fin N → ℝ) × (Fin N → ℝ), dotp uu.1 uu.2 ^ 2 =
      ∑ i, ∑ j, (uu.1 i * uu.1 j) * (uu.2 i * uu.2 j) := by
    intro uu
    unfold dotp
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hi : ∀ i j, Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      (uu.1 i * uu.1 j) * (uu.2 i * uu.2 j)) (lawU2 N) := fun i j =>
    (hmom.int2 i j).mul_prod (hmom.int2 i j)
  have hv : ∀ i j, ∫ uu : (Fin N → ℝ) × (Fin N → ℝ), (uu.1 i * uu.1 j) * (uu.2 i * uu.2 j)
      ∂lawU2 N = if i = j then 1 / (N : ℝ) ^ 2 else 0 := by
    intro i j
    unfold lawU2
    rw [integral_prod_mul (fun x : Fin N → ℝ => x i * x j) (fun x : Fin N → ℝ => x i * x j),
      hmom.m2]
    split_ifs
    · ring
    · ring
  simp only [e]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
  have : ∀ i : Fin N, ∫ uu : (Fin N → ℝ) × (Fin N → ℝ),
      ∑ j, (uu.1 i * uu.1 j) * (uu.2 i * uu.2 j) ∂lawU2 N = 1 / (N : ℝ) ^ 2 := by
    intro i
    rw [integral_finsetSum _ fun j _ => hi i j]
    simp only [hv, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **The link of the inputs**: `‖κ(κ(⟨u, u′⟩)) − κ(κ(0))‖₂ ≤ 1/√N`. -/
theorem sphere_kk_L2 (hN : 1 ≤ N) :
    L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) (1 / √(N : ℝ)) := by
  have := lawU2_prob hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  obtain ⟨iD, eD⟩ := lawU2_dot_sq hN
  have hmeas : Measurable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) :=
    ((continuous_kappa.comp (continuous_kappa.comp continuous_dotp)).measurable).sub
      measurable_const
  have hpt : ∀ᵐ uu ∂lawU2 N, (kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) ^ 2 ≤
      dotp uu.1 uu.2 ^ 2 := by
    filter_upwards [lawU2_ae_unit hN] with uu huu
    have h := abs_dotp_le_nrm uu.1 uu.2
    rw [nrm_of_normSq_one huu.1, nrm_of_normSq_one huu.2, mul_one] at h
    obtain ⟨hl, hr⟩ := abs_le.mp h
    have habs : |kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)| ≤ |dotp uu.1 uu.2| := by
      rcases le_total 0 (dotp uu.1 uu.2) with h0 | h0
      · have a1 := hG.lip (by norm_num : (-1 : ℝ) ≤ 0) h0 hr
        have a2 := hG.mono ⟨by norm_num, by norm_num⟩ ⟨hl, hr⟩ h0
        simp only [Function.comp] at a1 a2
        rw [abs_of_nonneg (by linarith), abs_of_nonneg h0]
        linarith
      · have a1 := hG.lip hl h0 (by norm_num : (0 : ℝ) ≤ 1)
        have a2 := hG.mono ⟨hl, hr⟩ ⟨by norm_num, by norm_num⟩ h0
        simp only [Function.comp] at a1 a2
        rw [abs_of_nonpos (by linarith), abs_of_nonpos h0]
        linarith
    rw [← sq_abs, ← sq_abs (dotp uu.1 uu.2)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hi : Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      (kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) ^ 2) (lawU2 N) := by
    refine Integrable.mono' iD (hmeas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hpt] with uu h
    rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  refine ⟨hmeas.aestronglyMeasurable, hi, (integral_mono_ae hi iD hpt).trans ?_⟩
  rw [eD, div_pow, Real.sq_sqrt hN'.le]
  simp

/-! ## The World network -/

/-- The `L²` bound of `world_cos_L2`: the last matrix of `W` and the normalization
(`1/√n + (19/2)√(12 + 48/n)/n`), the norms of the hidden layers (`√(5·epsW)`), the inner product
of the hidden layers, and the zero events (`2√epsW`). -/
noncomputable def eW2 (n m : ℕ) : ℝ :=
  1 / √(n : ℝ) + 19 / 2 * √(12 + 48 / (n : ℝ)) / (n : ℝ) + √(5 * epsW m) +
    (√6 * √(1 + 5 / (m : ℝ)) / √(m : ℝ) + (5 * kappa 0 + √6) / √(m : ℝ)) + 2 * √(epsW m)

lemma epsW_pos (hm : 1 ≤ m) : 0 < epsW m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have : 0 < 5 / (m : ℝ) := by positivity
  unfold epsW
  nlinarith

lemma cosv_of_zero {ι : Type*} [Fintype ι] {y y' : ι → ℝ} (h : normSq y = 0 ∨ normSq y' = 0) :
    cosv y y' = 0 := by
  unfold cosv nrm
  rcases h with h | h <;> simp [h]

lemma measurable_lastStep (u u' : Fin N → ℝ) :
    Measurable (fun z : (Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ) ×
        Matrix (Fin n) (Fin m) ℝ =>
      dotp (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u))) (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u')))) :=
  measurable_dotp_comp
    (measurable_sphPt.comp
      (continuous_snd.matrix_mulVec ((continuous_hid2_param u).comp continuous_fst)).measurable)
    (measurable_sphPt.comp
      (continuous_snd.matrix_mulVec ((continuous_hid2_param u').comp continuous_fst)).measurable)

/-- **The World network and the normalization in `L²`**: for unit vectors `u, u′` of `ℝ^N`,
`‖⟨x(u), x(u′)⟩ − κ(κ(⟨u, u′⟩))‖_{L²(W)} ≤ eW2 n m`. -/
theorem world_cos_L2 (hN : 1 ≤ N) (hm : 1 ≤ m) (hn : 1 ≤ n) {u u' : Fin N → ℝ}
    (hu : normSq u = 1) (hu' : normSq u' = 1) :
    L2le (mlpGauss N m n)
      (fun W : MlpParam N m n => dotp (xW W u) (xW W u') - kappa (kappa (dotp u u')))
      (eW2 n m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := sH_pos hN hm
  have heps := epsW_pos hm
  have hk0 : 0 ≤ kappa 0 := by rw [kappa_zero]; positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 1 / √(n : ℝ) + 19 / 2 * √(12 + 48 / (n : ℝ)) / (n : ℝ) := ⟨_, rfl⟩
  have hApos : 0 < A := by rw [hA]; positivity
  obtain ⟨cH, hcH⟩ : ∃ c : ℝ, c = √6 * √(1 + 5 / (m : ℝ)) / √(m : ℝ) +
      (5 * kappa 0 + √6) / √(m : ℝ) := ⟨_, rfl⟩
  have hcHpos : 0 < cH := by
    rw [hcH]
    have h6 : (0 : ℝ) < √6 := by positivity
    have : 0 < (5 * kappa 0 + √6) / √(m : ℝ) := div_pos (by linarith) (by positivity)
    have : 0 ≤ √6 * √(1 + 5 / (m : ℝ)) / √(m : ℝ) := by positivity
    linarith
  -- the zero events
  have hind : ∀ w : Fin N → ℝ, normSq w = 1 →
      L2le ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
        (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
          if normSq (hid2 θ.1 θ.2 w) = 0 then (1 : ℝ) else 0) (√(epsW m)) := by
    intro w hw
    refine L2le.of_sq_le (measurable_zero_ind w).aestronglyMeasurable (integrable_zero_ind w)
      (fun θ => by split_ifs <;> simp) ?_
    rw [Real.sq_sqrt heps.le]
    exact hid2_zero hN hm hw
  have hg : L2le ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
      (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
        A + ((if normSq (hid2 θ.1 θ.2 u) = 0 then (1 : ℝ) else 0) +
          (if normSq (hid2 θ.1 θ.2 u') = 0 then (1 : ℝ) else 0)))
      (A + (√(epsW m) + √(epsW m))) := by
    have hc : L2le ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
        (fun _ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ => A) A :=
      ⟨aestronglyMeasurable_const, integrable_const _, by simp⟩
    exact hc.add ((hind u hu).add (hind u' hu') (by positivity) (by positivity)) hApos
      (by positivity)
  have hmeasC : Measurable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')) := measurable_cosv_hid2 u u'
  have hmeas1 : Measurable (fun z : (Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ) ×
        Matrix (Fin n) (Fin m) ℝ =>
      dotp (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u))) (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u'))) -
        cosv (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u')) :=
    (measurable_lastStep u u').sub (hmeasC.comp measurable_fst)
  -- (i) the last matrix
  have h1 : L2le (((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))).prod
      (gaussMat n m (2 / (m : ℝ))))
      (fun z : (Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ) ×
        Matrix (Fin n) (Fin m) ℝ =>
      dotp (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u))) (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u'))) -
        cosv (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u')) (A + (√(epsW m) + √(epsW m))) := by
    refine L2le.prod' hmeas1.aestronglyMeasurable hg (Filter.Eventually.of_forall fun θ => ?_)
    by_cases hz : normSq (hid2 θ.1 θ.2 u) = 0 ∨ normSq (hid2 θ.1 θ.2 u') = 0
    · have hb : L2le (gaussMat n m (2 / (m : ℝ))) (fun M₃ : Matrix (Fin n) (Fin m) ℝ =>
          dotp (sphPt (M₃.mulVec (hid2 θ.1 θ.2 u))) (sphPt (M₃.mulVec (hid2 θ.1 θ.2 u'))) -
            cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')) 1 := by
        refine L2le.of_bound (hmeas1.comp measurable_prodMk_left).aestronglyMeasurable
          (fun M₃ => ?_)
        simp only [Function.comp]
        rw [cosv_of_zero hz, sub_zero, abs_le]
        exact ⟨dotp_sphPt_ge hn _ _, dotp_sphPt_le hn _ _⟩
      refine hb.mono zero_le_one ?_
      rcases hz with hz | hz
      · simp only [hz, ↓reduceIte]
        have : (0 : ℝ) ≤ if normSq (hid2 θ.1 θ.2 u') = 0 then (1 : ℝ) else 0 := by
          split_ifs <;> norm_num
        linarith
      · simp only [hz, ↓reduceIte]
        have : (0 : ℝ) ≤ if normSq (hid2 θ.1 θ.2 u) = 0 then (1 : ℝ) else 0 := by
          split_ifs <;> norm_num
        linarith
    · have hz : normSq (hid2 θ.1 θ.2 u) ≠ 0 ∧ normSq (hid2 θ.1 θ.2 u') ≠ 0 :=
        ⟨fun h => hz (Or.inl h), fun h => hz (Or.inr h)⟩
      have hb := lin_cos_L2 (n := n) (v := 2 / (m : ℝ)) (by positivity) hn (hid2 θ.1 θ.2 u)
        (hid2 θ.1 θ.2 u') hz.1 hz.2
      have hc := cosv_mem (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')
      have hc2 : cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') ^ 2 ≤ 1 := by
        nlinarith [hc.1, hc.2]
      have hJ : (0 : ℝ) ≤ 19 / 2 * √(12 + 48 / (n : ℝ)) / (n : ℝ) := by positivity
      have h0 : 0 ≤ (1 - cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') ^ 2) / √(n : ℝ) :=
        div_nonneg (by linarith) (Real.sqrt_nonneg _)
      have hle : (1 - cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') ^ 2) / √(n : ℝ) ≤ 1 / √(n : ℝ) :=
        div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (cosv (hid2 θ.1 θ.2 u)
          (hid2 θ.1 θ.2 u'))]) (Real.sqrt_nonneg _)
      refine hb.mono (by linarith) ?_
      simp only [hz.1, hz.2, ↓reduceIte, hA]
      linarith
  -- (ii) the norms of the hidden layers
  have h2 : L2le ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
      (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
        cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') -
          dotp (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') / sH N m) (√(5 * epsW m)) := by
    obtain ⟨iP, uP⟩ := hid2_pair hN hm hu hu'
    have hmd : Measurable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
        dotp (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')) :=
      measurable_dotp_comp (continuous_hid2_param u).measurable
        (continuous_hid2_param u').measurable
    refine L2le.of_sq_le (hmeasC.sub (hmd.div_const _)).aestronglyMeasurable
      (iP.const_mul (1 / sH N m ^ 2)) (fun θ => ?_) ?_
    · have hc := cosv_mem (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')
      have hc2 : cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') ^ 2 ≤ 1 := by nlinarith [hc.1, hc.2]
      rw [dotp_eq_cosv_mul (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')]
      have e : (cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') -
          cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') *
            (nrm (hid2 θ.1 θ.2 u) * nrm (hid2 θ.1 θ.2 u')) / sH N m) ^ 2 =
          cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') ^ 2 * (1 / sH N m ^ 2 *
            (nrm (hid2 θ.1 θ.2 u) * nrm (hid2 θ.1 θ.2 u') - sH N m) ^ 2) := by
        have : sH N m ≠ 0 := hs.ne'
        field_simp
        ring
      rw [e]
      exact mul_le_of_le_one_left (by positivity) hc2
    · rw [integral_const_mul, Real.sq_sqrt (by positivity)]
      have := mul_le_mul_of_nonneg_left uP (by positivity : (0 : ℝ) ≤ 1 / sH N m ^ 2)
      refine this.trans (le_of_eq ?_)
      have : sH N m ≠ 0 := hs.ne'
      field_simp
  -- (iii) the inner product of the hidden layers
  have h3 : L2le ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
      (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
        dotp (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') / sH N m - kappa (kappa (dotp u u'))) cH := by
    have h := (hid2_dot_L2 (two_div_nonneg N) (two_div_nonneg m) hm hm u u').const_mul_nonneg
      (c := 1 / sH N m) (by positivity)
    rw [psi_unit _ hu hu', nrm_of_normSq_one hu, nrm_of_normSq_one hu'] at h
    have hne : sH N m ≠ 0 := hs.ne'
    refine (h.congr_fun fun θ => ?_).congr_bound ?_
    · simp only [Function.comp]
      unfold sH at hne ⊢
      field_simp
    · rw [hcH]
      unfold sH at hne ⊢
      field_simp
  have h23 := (h2.add h3 (by positivity) hcHpos).comp_fst
    (ν := gaussMat n m (2 / (m : ℝ)))
  have hall := h1.add h23 (by positivity) (by positivity)
  have hmap : (mlpGauss N m n).map (MeasurableEquiv.prodAssoc (α := Matrix (Fin m) (Fin N) ℝ)
      (β := Matrix (Fin m) (Fin m) ℝ) (γ := Matrix (Fin n) (Fin m) ℝ)).symm =
      ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))).prod
        (gaussMat n m (2 / (m : ℝ))) := by
    unfold mlpGauss
    rw [← Measure.prodAssoc_prod, MeasurableEquiv.map_symm_map]
  have hfin := hall.comp_map (MeasurableEquiv.prodAssoc (α := Matrix (Fin m) (Fin N) ℝ)
      (β := Matrix (Fin m) (Fin m) ℝ) (γ := Matrix (Fin n) (Fin m) ℝ)).symm.measurable hmap
  refine (hfin.congr_fun fun W => ?_).congr_bound ?_
  · show dotp (sphPt (W.2.2.mulVec (hid2 W.1 W.2.1 u))) (sphPt (W.2.2.mulVec (hid2 W.1 W.2.1 u'))) -
        cosv (hid2 W.1 W.2.1 u) (hid2 W.1 W.2.1 u') +
        (cosv (hid2 W.1 W.2.1 u) (hid2 W.1 W.2.1 u') -
          dotp (hid2 W.1 W.2.1 u) (hid2 W.1 W.2.1 u') / sH N m +
          (dotp (hid2 W.1 W.2.1 u) (hid2 W.1 W.2.1 u') / sH N m - kappa (kappa (dotp u u')))) =
      dotp (xW W u) (xW W u') - kappa (kappa (dotp u u'))
    have : dotp (xW W u) (xW W u') = dotp (sphPt (W.2.2.mulVec (hid2 W.1 W.2.1 u)))
        (sphPt (W.2.2.mulVec (hid2 W.1 W.2.1 u'))) := rfl
    rw [this]
    ring
  · unfold eW2
    rw [hA, hcH]
    ring

end BstLean.Part133

open BstLean.Part133 in
#print axioms sphere_kk_L2
open BstLean.Part133 in
#print axioms world_cos_L2
