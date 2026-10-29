import BstLean.Part140Err

/-!
# Part 140, item 2 (more): the stand-in theorem with the computed centre over the whole `W`

Role: `delegations/statements/p140-spec.md`, item 2. The joint and the tail form of
`standInHat140`, as `standIn136_joint` and `standIn136_tail` of Part 136 for the exact centre.

* `nuHat W`: the exact stand-in of `W = (M₁, M₂, M₃)` built on the computed centre `b̂`:
  `standIn` of Part 134 with `b = b̂(M₁, M₂)` and `c = M₃ b̂`.
* **`standInHat140_joint`**: `E_W[1_good·(E_{μ_W} φ − E_{ν̂_W} φ)²] ≤ (1.83/n)·E_W[1_good·Var_{ν̂_W} φ]`
  (`good` is `goodWH n`).
* **`standInHat140_tail`**: for `t > 0`:
  `Pr_W(|E_{μ_W} φ − E_{ν̂_W} φ| ≥ t) ≤ 0.002 + 70/n + (1.83/n)·E_W Var_{ν̂_W} φ / t²`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part140

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn

variable {N m n : ℕ}

/-- **The stand-in distribution of the World network `W = (M₁, M₂, M₃)`**: `standIn` of Part 134
with `μ` uniform on the sphere, `h = hid2 M₁ M₂`, `v = 2/m`, `b = h̄(M₁, M₂)`, `c = M₃ h̄`. -/
noncomputable def nuHat (W : MlpParam N m n) : Measure (Fin n → ℝ) :=
  standIn (uniformSphere N) (hid2 W.1 W.2.1) (2 / (m : ℝ)) (bhat (W.1, W.2.1))
    (W.2.2.mulVec (bhat (W.1, W.2.1)))

lemma nuHat_prob (hN : 1 ≤ N) (W : MlpParam N m n) : IsProbabilityMeasure (nuHat W) := by
  have := uniformSphere_isProbability N hN
  exact standIn_prob _ (continuous_hid2 _ _).measurable _ _ _

/-- `W ↦ E_{ν_W} φ` is bounded and measurable. -/
lemma bm_nuHat (hN : 1 ≤ N) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    BM (fun W : MlpParam N m n => ∫ x, φ x ∂nuHat W) := by
  have := uniformSphere_isProbability N hN
  have hθ : Measurable (fun q : MlpParam N m n × ((Fin N → ℝ) × (Fin n → ℝ)) =>
      ((q.1.1, q.1.2.1) : HidParam N m)) :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_fst))
  have hb : Measurable (fun q : MlpParam N m n × ((Fin N → ℝ) × (Fin n → ℝ)) =>
      bhat (q.1.1, q.1.2.1)) := (measurable_bhat hN).comp hθ
  have hh : Measurable (fun q : MlpParam N m n × ((Fin N → ℝ) × (Fin n → ℝ)) =>
      hid2 q.1.1 q.1.2.1 q.2.1) :=
    continuous_hid2_joint.measurable.comp (hθ.prodMk (measurable_fst.comp measurable_snd))
  have hc : Measurable (fun q : MlpParam N m n × ((Fin N → ℝ) × (Fin n → ℝ)) =>
      q.1.2.2.mulVec (bhat (q.1.1, q.1.2.1))) :=
    measurable_mulVec_joint.comp
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk hb)
  have hJ : Measurable (fun q : MlpParam N m n × ((Fin N → ℝ) × (Fin n → ℝ)) =>
      lam (bhat (q.1.1, q.1.2.1)) (hid2 q.1.1 q.1.2.1 q.2.1) •
          q.1.2.2.mulVec (bhat (q.1.1, q.1.2.1)) +
        sig (2 / (m : ℝ)) (bhat (q.1.1, q.1.2.1)) (hid2 q.1.1 q.1.2.1 q.2.1) • q.2.2) :=
    ((measurable_lam2.comp (hb.prodMk hh)).smul hc).add
      (((measurable_sig2 (2 / (m : ℝ))).comp (hb.prodMk hh)).smul
        (measurable_snd.comp measurable_snd))
  have h1 : BM (fun q : MlpParam N m n × ((Fin N → ℝ) × (Fin n → ℝ)) =>
      φ (sphPt (lam (bhat (q.1.1, q.1.2.1)) (hid2 q.1.1 q.1.2.1 q.2.1) •
          q.1.2.2.mulVec (bhat (q.1.1, q.1.2.1)) +
        sig (2 / (m : ℝ)) (bhat (q.1.1, q.1.2.1)) (hid2 q.1.1 q.1.2.1 q.2.1) • q.2.2))) :=
    hφ.comp (measurable_sphPt.comp hJ)
  have h2 := h1.integral_right ((uniformSphere N).prod (stdGauss (Fin n)))
  have e : (fun W : MlpParam N m n => ∫ x, φ x ∂nuHat W) =
      fun W => ∫ p : (Fin N → ℝ) × (Fin n → ℝ),
        φ (sphPt (lam (bhat (W.1, W.2.1)) (hid2 W.1 W.2.1 p.1) •
          W.2.2.mulVec (bhat (W.1, W.2.1)) +
        sig (2 / (m : ℝ)) (bhat (W.1, W.2.1)) (hid2 W.1 W.2.1 p.1) • p.2))
        ∂((uniformSphere N).prod (stdGauss (Fin n))) := by
    funext W
    unfold nuHat standIn
    exact integral_map (measurable_sphPt.comp (measurable_standOut
      (continuous_hid2 W.1 W.2.1).measurable (2 / (m : ℝ)) (bhat (W.1, W.2.1))
      (W.2.2.mulVec (bhat (W.1, W.2.1))))).aemeasurable hφ.meas.aestronglyMeasurable
  rw [e]
  exact h2

lemma var_nuHat (hN : 1 ≤ N) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) (W : MlpParam N m n) :
    Var[φ; nuHat W] = ∫ x, φ x ^ 2 ∂nuHat W - (∫ x, φ x ∂nuHat W) ^ 2 := by
  have := nuHat_prob hN W
  exact var_bm (nuHat W) hφ

/-- `W ↦ Var_{ν_W} φ` is bounded and measurable. -/
lemma bm_varHat (hN : 1 ≤ N) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    BM (fun W : MlpParam N m n => Var[φ; nuHat W]) := by
  simp_rw [var_nuHat hN hφ]
  exact (bm_nuHat hN hφ.sq).sub (bm_nuHat hN hφ).sq

/-- **The stand-in theorem over the whole World network, on the good event (item 4).** For every
`n ≥ 4096` and every bounded measurable `φ`:
`E_W[1_good·(E_{μ_W} φ − E_{ν_W} φ)²] ≤ ((183/100)/n)·E_W[1_good·Var_{ν_W} φ]`. -/
theorem standInHat140_joint {n : ℕ} (hn : 4096 ≤ n) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ W, (goodWH n).indicator
        (fun W => ((∫ x, φ x ∂muWn W) - ∫ x, φ x ∂nuHat W) ^ 2) W
        ∂mlpGauss (2 * n) (mW n) n ≤
      183 / 100 / (n : ℝ) *
        ∫ W, (goodWH n).indicator (fun W => Var[φ; nuHat W]) W ∂mlpGauss (2 * n) (mW n) n := by
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  have mG := goodWH_meas (n := n) (by omega)
  have b1 : BM ((goodWH n).indicator
      (fun W => ((∫ x, φ x ∂muWn W) - ∫ x, φ x ∂nuHat W) ^ 2)) :=
    bm_indicator mG ((bm_muW hN hφ).sub (bm_nuHat hN hφ)).sq
  have b2 : BM ((goodWH n).indicator (fun W => Var[φ; nuHat W])) :=
    bm_indicator mG (bm_varHat hN hφ)
  rw [integral_mlp_split b1, integral_mlp_split b2, ← integral_const_mul]
  have i1 := ((b1.comp MeasurableEquiv.prodAssoc.measurable).integral_right
    (gaussMat n (mW n) (2 / (mW n : ℝ)))).integrable (hidGauss (2 * n) (mW n))
  have i2 := (((b2.comp MeasurableEquiv.prodAssoc.measurable).integral_right
    (gaussMat n (mW n) (2 / (mW n : ℝ)))).integrable (hidGauss (2 * n) (mW n))).const_mul
    (183 / 100 / (n : ℝ))
  refine integral_mono i1 i2 fun θ => ?_
  by_cases hθ : θ ∈ goodHat n
  · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ, (θ.1, θ.2, M₃) ∈ goodWH n := fun M₃ => hθ
    simp only [Set.indicator_of_mem (hW _)]
    have h := standInHat140 hn hθ hφ
    rw [← cDist_eq, integral_map (measurable_mulVec_right _).aemeasurable
      (bm_var_standIn (uniformSphere (2 * n)) _ _ (continuous_hid2 θ.1 θ.2).measurable
        hφ).meas.aestronglyMeasurable] at h
    exact h
  · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ, (θ.1, θ.2, M₃) ∉ goodWH n := fun M₃ => hθ
    simp only [Set.indicator_of_notMem (hW _)]
    simp

/-- **The tail form.** For every `n ≥ 4096`, bounded measurable `φ` and `t > 0`:
`Pr_W(|E_{μ_W} φ − E_{ν̂_W} φ| ≥ t) ≤ 0.002 + 70/n + (1.83/n)·E_W Var_{ν̂_W} φ / t²`. -/
theorem standInHat140_tail {n : ℕ} (hn : 4096 ≤ n) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) {t : ℝ}
    (ht : 0 < t) :
    (mlpGauss (2 * n) (mW n) n).real
        {W | t ≤ |(∫ x, φ x ∂muWn W) - ∫ x, φ x ∂nuHat W|} ≤
      2 / 1000 + 70 / (n : ℝ) +
        183 / 100 / (n : ℝ) * (∫ W, Var[φ; nuHat W] ∂mlpGauss (2 * n) (mW n) n) / t ^ 2 := by
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by
    have : (4096 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have mG := goodWH_meas (n := n) (by omega)
  set P := mlpGauss (2 * n) (mW n) n with hP
  set f : MlpParam (2 * n) (mW n) n → ℝ :=
    fun W => ((∫ x, φ x ∂muWn W) - ∫ x, φ x ∂nuHat W) ^ 2 with hf
  have bf : BM f := ((bm_muW hN hφ).sub (bm_nuHat hN hφ)).sq
  have bV : BM (fun W : MlpParam (2 * n) (mW n) n => Var[φ; nuHat W]) := bm_varHat hN hφ
  have bg : BM ((goodWH n).indicator f) := bm_indicator mG bf
  have hg0 : ∀ W, 0 ≤ (goodWH n).indicator f W := fun W =>
    Set.indicator_nonneg (fun W _ => sq_nonneg _) W
  have hsub : {W | t ≤ |(∫ x, φ x ∂muWn W) - ∫ x, φ x ∂nuHat W|} ⊆
      (goodWH n)ᶜ ∪ {W | t ^ 2 ≤ (goodWH n).indicator f W} := by
    intro W hW
    by_cases hWG : W ∈ goodWH n
    · right
      simp only [Set.mem_ofPred_eq] at hW ⊢
      rw [Set.indicator_of_mem hWG]
      have := pow_le_pow_left₀ ht.le hW 2
      simpa only [hf, sq_abs] using this
    · left
      exact hWG
  have h1 : P.real (goodWH n)ᶜ ≤ 2 / 1000 + 70 / (n : ℝ) := by
    rw [measureReal_compl mG, probReal_univ]
    have := goodWH_prob hn
    linarith
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := (goodWH n).indicator f)
    (Filter.Eventually.of_forall hg0) (bg.integrable P) (t ^ 2)
  have e3 : ∫ W, (goodWH n).indicator (fun W => Var[φ; nuHat W]) W ∂P ≤
      ∫ W, Var[φ; nuHat W] ∂P := by
    refine integral_mono ((bm_indicator mG bV).integrable P) (bV.integrable P) fun W => ?_
    by_cases hW : W ∈ goodWH n
    · rw [Set.indicator_of_mem hW]
    · rw [Set.indicator_of_notMem hW]; exact variance_nonneg _ _
  have e4 := standInHat140_joint hn hφ
  have e5 : 183 / 100 / (n : ℝ) * ∫ W, (goodWH n).indicator (fun W => Var[φ; nuHat W]) W ∂P ≤
      183 / 100 / (n : ℝ) * ∫ W, Var[φ; nuHat W] ∂P :=
    mul_le_mul_of_nonneg_left e3 (by positivity)
  have ht2 : 0 < t ^ 2 := by positivity
  have h2 : P.real {W | t ^ 2 ≤ (goodWH n).indicator f W} ≤
      183 / 100 / (n : ℝ) * (∫ W, Var[φ; nuHat W] ∂P) / t ^ 2 := by
    rw [le_div_iff₀ ht2]
    have : (∫ W, (goodWH n).indicator f W ∂P) ≤
        183 / 100 / (n : ℝ) * ∫ W, Var[φ; nuHat W] ∂P := e4.trans e5
    linarith
  calc P.real {W | t ≤ |(∫ x, φ x ∂muWn W) - ∫ x, φ x ∂nuHat W|}
      ≤ P.real ((goodWH n)ᶜ ∪ {W | t ^ 2 ≤ (goodWH n).indicator f W}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ P.real (goodWH n)ᶜ + P.real {W | t ^ 2 ≤ (goodWH n).indicator f W} :=
        measureReal_union_le _ _
    _ ≤ _ := add_le_add h1 h2

/-- **`centreEvent140`** (item 1, the event). For every `n ≥ 4096` the hidden event `goodHat n`
has probability at least `1 − (0.002 + 70/n)`, and on it: `b̂ ≠ 0`,
`t|b̂ − h̄|² ≤ γ·(3/4)/N` and `0.48·γ ≤ t|b̂|² ≤ 0.508·γ` (`γ = 2/N`, `N = 2n`). -/
theorem centreEvent140 {n : ℕ} (hn : 4096 ≤ n) :
    1 - (2 / 1000 + 70 / (n : ℝ)) ≤ (hidGauss (2 * n) (mW n)).real (goodHat n) ∧
    ∀ θ ∈ goodHat n, bhat θ ≠ 0 ∧
      dist2 (2 * n) (mW n) θ ≤ 2 / ((2 * n : ℕ) : ℝ) * (3 / 4 / ((2 * n : ℕ) : ℝ)) ∧
      2 / ((2 * n : ℕ) : ℝ) * (48 / 100) ≤ Bh (2 * n) (mW n) θ ∧
      Bh (2 * n) (mW n) θ ≤ 2 / ((2 * n : ℕ) : ℝ) * (508 / 1000) :=
  ⟨goodHat_prob hn, fun θ hθ => ⟨bhat_ne hn hθ, hθ.1.2, (Bh_hat hn hθ).1, (Bh_hat hn hθ).2⟩⟩

end BstLean.Part140

open BstLean.Part140 in
#print axioms centreEvent140

open BstLean.Part140 in
#print axioms standInHat140_joint
open BstLean.Part140 in
#print axioms standInHat140_tail
