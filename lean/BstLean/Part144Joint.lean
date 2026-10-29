import BstLean.Part144Struct

/-!
# Part 144, item 2, the joint step: the mean of `k` exact samples fails, all widths

Role: `delegations/statements/p144-spec.md`, item 2. Paper source: round onW15c, §7 (the event
method). The probability is joint over `(W, A, F)` and the `k` inputs `u_1, …, u_k`.

* `lawT N mW n mA mF`: the distribution of `(W, A, F)` (three independent random ReLU MLPs).
* `yJ t0 k`: `Y = t0²(4X − k·f) − k·τ` as a function of `((W, A, F), (u_j)_j)`; it does not read
  the last matrix of `F`.
* `measurableSet_failSet`, `measurable_yJ`.
* `fail_ge`: `Φ̄(t0)·Pr(Y > 0) ≤ Pr(|ĝ_k − B| > sd/2)` (the block bound of `Part144Block` over the
  last row of `F`, then Tonelli).
* `yJ_cheb`: `Pr(Y ≤ 0) ≤ K·e²/((4t0² − k)·c)²` if `‖kD − c‖₂ ≤ e` (Chebyshev).
* **`sampleFails_of`**: `Pr(|ĝ_k − B| > sd/2) ≥ Φ̄(t0)·(1 − K·e²/((4t0² − k)·c)²)`,
  `K = 32t0⁴ + (4t0² − k)² + t0⁴k²`, for every `k ≥ 1`, `t0 > 0` with `k < 4t0²`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part144

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139
  BstLean.Part142

variable {N mW n mA mF : ℕ}

/-- The three networks `(W, (A, F))`. -/
abbrev Trip (N mW n mA mF : ℕ) : Type :=
  MlpParam N mW n × MlpParam n mA n × MlpParam n mF 1

/-- The distribution of `(W, (A, F))`: three independent random ReLU MLPs. For `N = 2n` and the
widths of the Focus it is `mlpTriple 2 n`. -/
noncomputable def lawT (N mW n mA mF : ℕ) : Measure (Trip N mW n mA mF) :=
  (mlpGauss N mW n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))

instance : IsProbabilityMeasure (lawT N mW n mA mF) := by unfold lawT; infer_instance

/-- `Y = t0²(4X − k·f) − k·τ` as a function of `((W, A, F), (u_j)_j)`. -/
noncomputable def yJ (t0 : ℝ) (k : ℕ)
    (p : Trip N mW n mA mF × (Fin k → Fin N → ℝ)) : ℝ :=
  yR t0 k p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.2

/-! ## Measurability -/

/-- An entry of `Σ_A` is jointly measurable in `(W, A, F₁, F₂)`. -/
lemma measurable_covEntry (hN : 1 ≤ N) (i j : Fin mF) :
    Measurable (fun t : MlpParam N mW n × (MlpParam n mA n × Matrix (Fin mF) (Fin n) ℝ ×
      Matrix (Fin mF) (Fin mF) ℝ) => covMat t.1 t.2.1 t.2.2.1 t.2.2.2 i j) := by
  have hg : Measurable (Function.uncurry
      (fun (θ : (MlpParam n mA n × Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ) ×
          ℝ × ℝ)
        (x : Fin n → ℝ) => (hidF θ.1.2.1 θ.1.2.2 θ.1.1 x i - θ.2.1) *
          (hidF θ.1.2.1 θ.1.2.2 θ.1.1 x j - θ.2.2))) := by
    have h1 : ∀ l : Fin mF, Measurable (fun p : ((MlpParam n mA n × Matrix (Fin mF) (Fin n) ℝ ×
        Matrix (Fin mF) (Fin mF) ℝ) × ℝ × ℝ) × (Fin n → ℝ) =>
        hidF p.1.1.2.1 p.1.1.2.2 p.1.1.1 p.2 l) := fun l =>
      (continuous_hidF_all l).measurable.comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    exact ((h1 i).sub (measurable_fst.comp (measurable_snd.comp measurable_fst))).mul
      ((h1 j).sub (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  have h := measurable_muWn_integral (mW := mW) hN _ hg
  have h2 : Measurable (fun t : MlpParam N mW n × (MlpParam n mA n × Matrix (Fin mF) (Fin n) ℝ ×
      Matrix (Fin mF) (Fin mF) ℝ) =>
      (t.1, (t.2, aVec t.1 t.2.1 t.2.2.1 t.2.2.2 i, aVec t.1 t.2.1 t.2.2.1 t.2.2.2 j))) :=
    measurable_fst.prodMk (measurable_snd.prodMk
      ((measurable_aVec hN i).prodMk (measurable_aVec hN j)))
  have h3 := h.comp h2
  simp only [Function.comp_def] at h3
  exact h3

/-- The projection `((W, A, F), us) ↦ (W, (A, F₁, F₂))`. -/
lemma measurable_projH (k : ℕ) :
    Measurable (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) =>
      ((p.1.1, (p.1.2.1, p.1.2.2.1, p.1.2.2.2.1)) : MlpParam N mW n × (MlpParam n mA n ×
        Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ))) :=
  (measurable_fst.comp measurable_fst).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
        (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
          (measurable_snd.comp measurable_fst))))))

lemma measurable_covJ (hN : 1 ≤ N) (k : ℕ) (i j : Fin mF) :
    Measurable (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) =>
      covMat p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 i j) := by
  have h3 := (measurable_covEntry (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) hN i j).comp
    (measurable_projH k)
  simp only [Function.comp_def] at h3
  exact h3

lemma measurable_aJ (hN : 1 ≤ N) (k : ℕ) (i : Fin mF) :
    Measurable (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) =>
      aVec p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 i) := by
  have h3 := (measurable_aVec (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) hN i).comp
    (measurable_projH k)
  simp only [Function.comp_def] at h3
  exact h3

lemma measurable_xWJ (k : ℕ) (j : Fin k) :
    Measurable (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) => xW p.1.1 (p.2 j)) := by
  have h1 : Measurable (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) => (p.1.1, p.2 j)) :=
    (measurable_fst.comp measurable_fst).prodMk ((measurable_pi_apply j).comp measurable_snd)
  have h3 := (measurable_xW (N := N) (mW := mW) (n := n)).comp h1
  simp only [Function.comp_def] at h3
  exact h3

lemma measurable_tauJ (hN : 1 ≤ N) (k : ℕ) :
    Measurable (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) =>
      tauR p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1) := by
  have e : (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) =>
      tauR p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1) = fun p =>
      2 / (mF : ℝ) * ∑ i, covMat p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 i i := by
    funext p
    rw [tauR, ← trace_covMat]
    rfl
  rw [e]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => measurable_covJ hN k i i)

lemma measurable_fJ (hN : 1 ≤ N) (k : ℕ) :
    Measurable (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) =>
      fR p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1) := by
  have e : (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) =>
      fR p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1) = fun p =>
      2 / (mF : ℝ) * √(∑ i, ∑ j, covMat p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 i j ^ 2) := by
    funext p
    rw [fR, ← frob_covMat]
  rw [e]
  exact measurable_const.mul (Real.continuous_sqrt.measurable.comp
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      (measurable_covJ hN k i j).pow_const 2))

lemma measurable_zJ (k : ℕ) (j : Fin k) (i : Fin mF) :
    Measurable (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) =>
      zU p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 (p.2 j) i) := by
  have hp : Measurable (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) =>
      (((p.1.2.1, p.1.2.2.1, p.1.2.2.2.1), xW p.1.1 (p.2 j)) :
        (MlpParam n mA n × Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ) ×
          (Fin n → ℝ))) :=
    (measurable_snd.comp (measurable_projH k)).prodMk (measurable_xWJ k j)
  have h3 := (continuous_hidF_all (n := n) (mA := mA) (mF := mF) i).measurable.comp hp
  simp only [Function.comp_def] at h3
  exact h3

lemma measurable_xJ (hN : 1 ≤ N) (k : ℕ) :
    Measurable (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) =>
      xR k p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.2) := by
  have e : (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) =>
      xR k p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.2) = fun p =>
      2 / (mF : ℝ) / (k : ℝ) * ∑ i, (∑ j, (zU p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 (p.2 j) i -
        aVec p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 i)) ^ 2 := by
    funext p
    simp only [xR, sqS, sumC, aVec_eq]
  rw [e]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    (Finset.measurable_sum _ fun j _ =>
      (measurable_zJ k j i).sub (measurable_aJ hN k i)).pow_const 2)

/-- `Y` is jointly measurable. -/
theorem measurable_yJ (hN : 1 ≤ N) (t0 : ℝ) (k : ℕ) :
    Measurable (yJ (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) t0 k) := by
  unfold yJ yR
  exact (measurable_const.mul (((measurable_xJ hN k).const_mul 4).sub
    ((measurable_fJ hN k).const_mul _))).sub ((measurable_tauJ hN k).const_mul _)

lemma measurable_gMean (k : ℕ) :
    Measurable (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) =>
      gMean k p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold gMean
  refine Measurable.div_const (Finset.measurable_sum _ fun j _ => ?_) _
  have hp : Measurable (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) =>
      (((p.1.2.1, p.1.2.2), xW p.1.1 (p.2 j)) :
        (MlpParam n mA n × MlpParam n mF 1) × (Fin n → ℝ))) :=
    ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk (measurable_xWJ k j)
  have h3 := (continuous_phiN_all (n := n) (mA := mA) (mF := mF)).measurable.comp hp
  simp only [Function.comp_def] at h3
  exact h3

lemma measurable_sdnJ (hN : 1 ≤ N) (k : ℕ) :
    Measurable (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) =>
      sdn p.1.1 p.1.2.1 p.1.2.2) := by
  have hfst : Measurable (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) => p.1) :=
    measurable_fst
  have h3 := (measurable_sdn (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) hN).comp hfst
  simp only [Function.comp_def] at h3
  exact h3

lemma measurable_BnJ (hN : 1 ≤ N) (k : ℕ) :
    Measurable (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) =>
      Bn p.1.1 p.1.2.1 p.1.2.2) := by
  have hfst : Measurable (fun p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) => p.1) :=
    measurable_fst
  have h3 := (BstLean.Part131.measurable_Bn (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF)
    hN).comp hfst
  simp only [Function.comp_def] at h3
  exact h3

/-- The event "the sample mean fails" is measurable. -/
theorem measurableSet_failSet (hN : 1 ≤ N) (k : ℕ) :
    MeasurableSet (failSet (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) k) := by
  unfold failSet
  exact measurableSet_lt ((measurable_sdnJ hN k).div_const 2)
    (((measurable_gMean k).sub (measurable_BnJ hN k)).abs)

/-! ## Step 1: the block bound, then Tonelli -/

lemma lintegral_prod_mono_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {f g : α × β → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (h : ∀ y, ∫⁻ x, f (x, y) ∂μ ≤ ∫⁻ x, g (x, y) ∂μ) :
    ∫⁻ z, f z ∂(μ.prod ν) ≤ ∫⁻ z, g z ∂(μ.prod ν) := by
  rw [lintegral_prod_symm _ hf.aemeasurable, lintegral_prod_symm _ hg.aemeasurable]
  exact lintegral_mono h

/-- **`Φ̄(t0)·Pr(Y > 0) ≤ Pr(the sample mean fails)`**, joint over `(W, A, F)` and the inputs. -/
theorem fail_ge (hn : 1 ≤ n) (hN : 1 ≤ N) (hmF : 1 ≤ mF) {k : ℕ} (hk : 1 ≤ k) {t0 : ℝ}
    (ht0 : 0 < t0) :
    ENNReal.ofReal ((gaussianReal 0 1).real (Ioi t0)) *
        ((lawT N mW n mA mF).prod (uniK k N)) {p | 0 < yJ t0 k p} ≤
      ((lawT N mW n mA mF).prod (uniK k N)) (failSet k) := by
  have := uniK_prob hN k
  set Tl : ℝ≥0∞ := ENNReal.ofReal ((gaussianReal 0 1).real (Ioi t0)) with hTl
  have mG : MeasurableSet {p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) | 0 < yJ t0 k p} :=
    measurableSet_lt measurable_const (measurable_yJ hN t0 k)
  have mS := measurableSet_failSet (mW := mW) (n := n) (mA := mA) (mF := mF) hN k
  set g : Trip N mW n mA mF × (Fin k → Fin N → ℝ) → ℝ≥0∞ :=
    fun p => Tl * {p | 0 < yJ t0 k p}.indicator 1 p with hg
  set f : Trip N mW n mA mF × (Fin k → Fin N → ℝ) → ℝ≥0∞ :=
    (failSet k).indicator 1 with hf
  have mg : Measurable g := measurable_const.mul (measurable_one.indicator mG)
  have mf : Measurable f := measurable_one.indicator mS
  have eL : Tl * ((lawT N mW n mA mF).prod (uniK k N)) {p | 0 < yJ t0 k p} =
      ∫⁻ p, g p ∂((lawT N mW n mA mF).prod (uniK k N)) := by
    rw [hg, lintegral_const_mul _ (measurable_one.indicator mG), lintegral_indicator_one mG]
  have eR : ((lawT N mW n mA mF).prod (uniK k N)) (failSet k) =
      ∫⁻ p, f p ∂((lawT N mW n mA mF).prod (uniK k N)) := by
    rw [hf, lintegral_indicator_one mS]
  rw [eL, eR]
  refine lintegral_prod_mono_left mg mf fun us => ?_
  -- the innermost integral, over the last matrix of `F`
  have h5 : ∀ (W : MlpParam N mW n) (A : MlpParam n mA n) (F₁ : Matrix (Fin mF) (Fin n) ℝ)
      (F₂ : Matrix (Fin mF) (Fin mF) ℝ),
      ∫⁻ F₃, g ((W, A, F₁, F₂, F₃), us) ∂gaussMat 1 mF (2 / (mF : ℝ)) ≤
        ∫⁻ F₃, f ((W, A, F₁, F₂, F₃), us) ∂gaussMat 1 mF (2 / (mF : ℝ)) := by
    intro W A F₁ F₂
    have hconst : ∀ F₃ : Matrix (Fin 1) (Fin mF) ℝ,
        g ((W, A, F₁, F₂, F₃), us) = g ((W, A, F₁, F₂, 0), us) := fun _ => rfl
    simp_rw [hconst]
    rw [lintegral_const, measure_univ, mul_one]
    have hsl : MeasurableSet {F₃ : Matrix (Fin 1) (Fin mF) ℝ |
        ((W, A, F₁, F₂, F₃), us) ∈ failSet k} :=
      mS.preimage (f := fun F₃ : Matrix (Fin 1) (Fin mF) ℝ =>
        (((W, A, F₁, F₂, F₃), us) : Trip N mW n mA mF × (Fin k → Fin N → ℝ))) (by fun_prop)
    have e : (fun F₃ : Matrix (Fin 1) (Fin mF) ℝ => f ((W, A, F₁, F₂, F₃), us)) =
        {F₃ : Matrix (Fin 1) (Fin mF) ℝ | ((W, A, F₁, F₂, F₃), us) ∈ failSet k}.indicator 1 := by
      funext F₃
      by_cases h : (((W, A, F₁, F₂, F₃), us) : Trip N mW n mA mF × (Fin k → Fin N → ℝ)) ∈
          failSet k
      · rw [hf, Set.indicator_of_mem h, Set.indicator_of_mem
          (show F₃ ∈ {F₃ : Matrix (Fin 1) (Fin mF) ℝ | ((W, A, F₁, F₂, F₃), us) ∈ failSet k}
            from h)]
        rfl
      · rw [hf, Set.indicator_of_notMem h, Set.indicator_of_notMem
          (show F₃ ∉ {F₃ : Matrix (Fin 1) (Fin mF) ℝ | ((W, A, F₁, F₂, F₃), us) ∈ failSet k}
            from h)]
    rw [e, lintegral_indicator_one hsl]
    by_cases hG : 0 < yR t0 k W A F₁ F₂ us
    · have hc := fail_cond hn hN W A F₁ F₂ hmF hk us ht0 hG
      have hgv : g ((W, A, F₁, F₂, 0), us) = Tl := by
        have hmem : (((W, A, F₁, F₂, 0), us) : Trip N mW n mA mF × (Fin k → Fin N → ℝ)) ∈
            {p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) | 0 < yJ t0 k p} := hG
        simp only [hg, Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
      rw [hgv, hTl]
      rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
      exact hc.le
    · have hgv : g ((W, A, F₁, F₂, 0), us) = 0 := by
        have hmem : (((W, A, F₁, F₂, 0), us) : Trip N mW n mA mF × (Fin k → Fin N → ℝ)) ∉
            {p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) | 0 < yJ t0 k p} := hG
        simp only [hg, Set.indicator_of_notMem hmem, mul_zero]
      rw [hgv]
      exact bot_le
  have mgu : Measurable (fun t : Trip N mW n mA mF => g (t, us)) :=
    mg.comp (measurable_id.prodMk measurable_const)
  have mfu : Measurable (fun t : Trip N mW n mA mF => f (t, us)) :=
    mf.comp (measurable_id.prodMk measurable_const)
  have h4 : ∀ (W : MlpParam N mW n) (A : MlpParam n mA n) (F₁ : Matrix (Fin mF) (Fin n) ℝ),
      ∫⁻ y, g ((W, A, F₁, y), us)
          ∂((gaussMat mF mF (2 / (mF : ℝ))).prod (gaussMat 1 mF (2 / (mF : ℝ)))) ≤
        ∫⁻ y, f ((W, A, F₁, y), us)
          ∂((gaussMat mF mF (2 / (mF : ℝ))).prod (gaussMat 1 mF (2 / (mF : ℝ)))) :=
    fun W A F₁ => lintegral_prod_mono'
      (f := fun y => g ((W, A, F₁, y), us)) (g := fun y => f ((W, A, F₁, y), us))
      (mgu.comp (by fun_prop)) (mfu.comp (by fun_prop)) (fun F₂ => h5 W A F₁ F₂)
  have h3 : ∀ (W : MlpParam N mW n) (A : MlpParam n mA n),
      ∫⁻ y, g ((W, A, y), us) ∂mlpGauss n mF 1 ≤ ∫⁻ y, f ((W, A, y), us) ∂mlpGauss n mF 1 :=
    fun W A => lintegral_prod_mono'
      (f := fun y => g ((W, A, y), us)) (g := fun y => f ((W, A, y), us))
      (mgu.comp (by fun_prop)) (mfu.comp (by fun_prop)) (fun F₁ => h4 W A F₁)
  have h2 : ∀ W : MlpParam N mW n,
      ∫⁻ y, g ((W, y), us) ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) ≤
        ∫⁻ y, f ((W, y), us) ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) :=
    fun W => lintegral_prod_mono'
      (f := fun y => g ((W, y), us)) (g := fun y => f ((W, y), us))
      (mgu.comp (by fun_prop)) (mfu.comp (by fun_prop)) (fun A => h3 W A)
  exact lintegral_prod_mono' (f := fun t => g (t, us)) (g := fun t => f (t, us)) mgu mfu h2

/-! ## Step 2: Chebyshev for `Y` -/

/-- `QD` does not read the second Agent network. -/
lemma QD_indep (c : ℝ) (r : Rest N mW n mA mF) :
    QD c ((r.1, r.2.1, r.2.1, r.2.2.2) : Rest N mW n mA mF) = QD c r := by
  unfold QD
  refine integral_congr_ae (Filter.Eventually.of_forall fun uu => ?_)
  simp only
  rw [kD_zU, kD_zU]

/-- **The second moment of `Y`, joint.** If `‖kD − c‖₂ ≤ e`, then
`E(Y − (4t0² − k)·c)² ≤ K·e²`, `K = 32t0⁴ + (4t0² − k)² + t0⁴k²`. -/
theorem yJ_second (hn : 1 ≤ n) (hN : 1 ≤ N) (hmF : 1 ≤ mF) {k : ℕ} (hk : 1 ≤ k) {c e : ℝ}
    (hD : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF => kD ω - c) e) (t0 : ℝ) :
    ∫⁻ p, ENNReal.ofReal ((yJ t0 k p - (4 * t0 ^ 2 - k) * c) ^ 2)
        ∂((lawT N mW n mA mF).prod (uniK k N)) ≤
      ENNReal.ofReal ((32 * t0 ^ 4 + (4 * t0 ^ 2 - k) ^ 2 + t0 ^ 4 * (k : ℝ) ^ 2) * e ^ 2) := by
  have := uniK_prob hN k
  have := lawU2_prob hN
  set K : ℝ := 32 * t0 ^ 4 + (4 * t0 ^ 2 - k) ^ 2 + t0 ^ 4 * (k : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set Fn : Trip N mW n mA mF × (Fin k → Fin N → ℝ) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((yJ t0 k p - (4 * t0 ^ 2 - k) * c) ^ 2) with hFn
  have mFn : Measurable Fn :=
    ENNReal.measurable_ofReal.comp (((measurable_yJ hN t0 k).sub measurable_const).pow_const 2)
  have mQ : Measurable (QD (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) c) :=
    ((measurable_kD.sub measurable_const).pow_const
      2).stronglyMeasurable.integral_prod_left'.measurable
  have memb : Measurable (fun t : Trip N mW n mA mF =>
      ((t.1, t.2.1, t.2.1, t.2.2) : Rest N mW n mA mF)) := by fun_prop
  rw [lintegral_prod _ mFn.aemeasurable]
  have hin : ∀ t : Trip N mW n mA mF, ∫⁻ us, Fn (t, us) ∂uniK k N ≤
      ENNReal.ofReal (K * QD c ((t.1, t.2.1, t.2.1, t.2.2) : Rest N mW n mA mF)) := by
    intro t
    obtain ⟨hB, hle⟩ := yR_second hn hN t.1 t.2.1 t.2.2.1 t.2.2.2.1 hmF hk t.2.1 t.2.2.2.2 c t0
    have hB2 : BM (fun us : Fin k → Fin N → ℝ =>
        (yR t0 k t.1 t.2.1 t.2.2.1 t.2.2.2.1 us - (4 * t0 ^ 2 - k) * c) ^ 2) :=
      (hB.sub (BM.const _)).sq
    have e : ∫⁻ us, Fn (t, us) ∂uniK k N = ENNReal.ofReal
        (∫ us, (yR t0 k t.1 t.2.1 t.2.2.1 t.2.2.2.1 us - (4 * t0 ^ 2 - k) * c) ^ 2 ∂uniK k N) :=
      (ofReal_integral_eq_lintegral_ofReal (hB2.integrable _)
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
    rw [e]
    exact ENNReal.ofReal_le_ofReal hle
  refine (lintegral_mono hin).trans ?_
  -- from `(W, A, F)` to `(W, A, A′, F)`
  have e1 : ∫⁻ t : Trip N mW n mA mF,
      ENNReal.ofReal (K * QD c ((t.1, t.2.1, t.2.1, t.2.2) : Rest N mW n mA mF))
        ∂lawT N mW n mA mF =
      ∫⁻ r, ENNReal.ofReal (K * QD c r) ∂lawR N mW n mA mF := by
    have mπ : Measurable (fun r : Rest N mW n mA mF => (r.1, r.2.1, r.2.2.2)) := by fun_prop
    have mH : Measurable (fun t : Trip N mW n mA mF =>
        ENNReal.ofReal (K * QD c ((t.1, t.2.1, t.2.1, t.2.2) : Rest N mW n mA mF))) :=
      ENNReal.measurable_ofReal.comp ((mQ.comp memb).const_mul K)
    unfold lawT
    rw [← lawR_drop, lintegral_map mH mπ]
    refine lintegral_congr fun r => ?_
    simp only
    rw [QD_indep]
  rw [e1]
  have iQ : Integrable (QD (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) c)
      (lawR N mW n mA mF) := hD.int_sq.integral_prod_right
  have eQ : ∫ r, QD c r ∂lawR N mW n mA mF ≤ e ^ 2 := by
    have := integral_prod_symm (μ := lawU2 N) (ν := lawR N mW n mA mF) _ hD.int_sq
    unfold QD
    rw [← this]
    exact hD.le
  rw [← ofReal_integral_eq_lintegral_ofReal (iQ.const_mul K)
    (Filter.Eventually.of_forall fun r => mul_nonneg hK0 (QD_nonneg c r))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left eQ hK0

/-- **Chebyshev's inequality for `Y`.** If `‖kD − c‖₂ ≤ e`, `c > 0` and `k < 4t0²`, then
`Pr(Y ≤ 0) ≤ K·e²/((4t0² − k)·c)²`. -/
theorem yJ_cheb (hn : 1 ≤ n) (hN : 1 ≤ N) (hmF : 1 ≤ mF) {k : ℕ} (hk : 1 ≤ k) {c e : ℝ}
    (hc : 0 < c)
    (hD : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF => kD ω - c) e) {t0 : ℝ}
    (hgap : (k : ℝ) < 4 * t0 ^ 2) :
    ((lawT N mW n mA mF).prod (uniK k N)).real {p | yJ t0 k p ≤ 0} ≤
      (32 * t0 ^ 4 + (4 * t0 ^ 2 - k) ^ 2 + t0 ^ 4 * (k : ℝ) ^ 2) * e ^ 2 /
        ((4 * t0 ^ 2 - k) * c) ^ 2 := by
  have := uniK_prob hN k
  set ν := (lawT N mW n mA mF).prod (uniK k N) with hν
  set K : ℝ := 32 * t0 ^ 4 + (4 * t0 ^ 2 - k) ^ 2 + t0 ^ 4 * (k : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hg : 0 < (4 * t0 ^ 2 - k) * c := mul_pos (by linarith) hc
  have hg2 : 0 < ((4 * t0 ^ 2 - k) * c) ^ 2 := by positivity
  set Fn : Trip N mW n mA mF × (Fin k → Fin N → ℝ) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((yJ t0 k p - (4 * t0 ^ 2 - k) * c) ^ 2) with hFn
  have mFn : Measurable Fn :=
    ENNReal.measurable_ofReal.comp (((measurable_yJ hN t0 k).sub measurable_const).pow_const 2)
  have hL : ∫⁻ p, Fn p ∂ν ≤ ENNReal.ofReal (K * e ^ 2) := yJ_second hn hN hmF hk hD t0
  have hsub : {p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) | yJ t0 k p ≤ 0} ⊆
      {p | ENNReal.ofReal (((4 * t0 ^ 2 - k) * c) ^ 2) ≤ Fn p} := by
    intro p hp
    have hp' : yJ t0 k p ≤ 0 := hp
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith
  have hmark := mul_meas_ge_le_lintegral (μ := ν) mFn
    (ENNReal.ofReal (((4 * t0 ^ 2 - k) * c) ^ 2))
  have h1 : ENNReal.ofReal (((4 * t0 ^ 2 - k) * c) ^ 2) * ν {p | yJ t0 k p ≤ 0} ≤
      ENNReal.ofReal (K * e ^ 2) :=
    (mul_le_mul' le_rfl (measure_mono hsub)).trans (hmark.trans hL)
  have hv : (0 : ℝ) ≤ K * e ^ 2 := by positivity
  rw [le_div_iff₀ hg2, mul_comm]
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hg2.le, ENNReal.toReal_ofReal hv] at h2
  exact h2

/-! ## The joint statement, all widths -/

/-- **The mean of `k` exact samples fails with joint probability at least
`Φ̄(t0)·(1 − K·e²/((4t0² − k)·c)²)`**, `K = 32t0⁴ + (4t0² − k)² + t0⁴k²`, for every `k ≥ 1`
and every level `t0 > 0` with `k < 4t0²`, if `‖kD − c‖₂ ≤ e` and `c > 0`. The probability is
over `(W, A, F)` and the `k` independent inputs. -/
theorem sampleFails_of (hn : 1 ≤ n) (hN : 1 ≤ N) (hmF : 1 ≤ mF) {k : ℕ} (hk : 1 ≤ k) {c e : ℝ}
    (hc : 0 < c)
    (hD : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF => kD ω - c) e) {t0 : ℝ}
    (ht0 : 0 < t0) (hgap : (k : ℝ) < 4 * t0 ^ 2) :
    (gaussianReal 0 1).real (Ioi t0) *
        (1 - (32 * t0 ^ 4 + (4 * t0 ^ 2 - k) ^ 2 + t0 ^ 4 * (k : ℝ) ^ 2) * e ^ 2 /
          ((4 * t0 ^ 2 - k) * c) ^ 2) ≤
      ((lawT N mW n mA mF).prod (uniK k N)).real (failSet k) := by
  have := uniK_prob hN k
  set ν := (lawT N mW n mA mF).prod (uniK k N) with hν
  set Tl : ℝ := (gaussianReal 0 1).real (Ioi t0) with hTl
  have hTl0 : 0 ≤ Tl := measureReal_nonneg
  have h1 := fail_ge (mW := mW) (mA := mA) hn hN hmF hk ht0
  have h2 := yJ_cheb hn hN hmF hk hc hD hgap
  have mG : MeasurableSet {p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) | 0 < yJ t0 k p} :=
    measurableSet_lt measurable_const (measurable_yJ hN t0 k)
  have hcompl : {p : Trip N mW n mA mF × (Fin k → Fin N → ℝ) | yJ t0 k p ≤ 0} =
      {p | 0 < yJ t0 k p}ᶜ := by
    ext p; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
  rw [← hν, hcompl, measureReal_compl mG, probReal_univ] at h2
  have h3 := ENNReal.toReal_mono (measure_ne_top _ _) h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal measureReal_nonneg] at h3
  have h4 : Tl * ν.real {p | 0 < yJ t0 k p} ≤ ν.real (failSet k) := h3
  refine le_trans ?_ h4
  exact mul_le_mul_of_nonneg_left (by linarith) hTl0

end BstLean.Part144

open BstLean.Part144 in
#print axioms fail_ge
open BstLean.Part144 in
#print axioms yJ_cheb
open BstLean.Part144 in
#print axioms sampleFails_of
