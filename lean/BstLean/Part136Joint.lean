import BstLean.Part136Final

/-!
# Part 136, item 4, joint form: the stand-in theorem over the whole World network

Role: `delegations/statements/p136-spec.md`. `W = (M₁, M₂, M₃)` is the World network with
`N` inputs, hidden width `m` and `n` outputs.

* `hbarW θ`: the mean hidden vector `h̄` as a function of `θ = (M₁, M₂)`; it is measurable.
* `nuW W`: the stand-in distribution `ν` of `W`: `standIn` of Part 134 with `b = h̄(M₁, M₂)` and
  `c = M₃ h̄`.
* `bm_muW`, `bm_nuW`, `bm_varW`: `W ↦ E_{μ_W} φ`, `W ↦ E_{ν_W} φ`, `W ↦ Var_{ν_W} φ` are bounded
  and measurable.
* `goodW n`: the good event of Part 136 as an event of `W`.
* **`standIn136_joint`**:
  `E_W[1_good·(E_{μ_W} φ − E_{ν_W} φ)²] ≤ ((99/100)/n)·E_W[1_good·Var_{ν_W} φ]`.
* **`standIn136_total`**: for `|φ| ≤ B`:
  `E_W (E_{μ_W} φ − E_{ν_W} φ)² ≤ ((99/100)/n)·E_W Var_{ν_W} φ + (8/1000)·B²`.
* **`standIn136_tail`**: for `t > 0`:
  `Pr_W(|E_{μ_W} φ − E_{ν_W} φ| ≥ t) ≤ 0.002 + ((99/100)/n)·E_W Var_{ν_W} φ / t²`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part136

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134

variable {N m n : ℕ}

lemma bm_indicator {α : Type*} [MeasurableSpace α] {F : α → ℝ} {S : Set α}
    (hS : MeasurableSet S) (hF : BM F) : BM (S.indicator F) := by
  obtain ⟨M, hM⟩ := hF.bdd
  refine ⟨hF.meas.indicator hS, M, fun x => ?_⟩
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]; exact hM x
  · rw [Set.indicator_of_notMem hx, abs_zero]; exact (abs_nonneg _).trans (hM x)

/-- The mean hidden vector `h̄ = E_u h(u)` of the World network, as a function of `(M₁, M₂)`. -/
noncomputable def hbarW (θ : HidParam N m) : Fin m → ℝ :=
  hbar (uniformSphere N) (hid2 θ.1 θ.2)

lemma measurable_hbarW (hN : 1 ≤ N) : Measurable (hbarW : HidParam N m → Fin m → ℝ) := by
  have := uniformSphere_isProbability N hN
  refine measurable_pi_iff.mpr fun j => ?_
  have hc : Continuous (fun p : HidParam N m × (Fin N → ℝ) => hid2 p.1.1 p.1.2 p.2 j) :=
    (continuous_apply j).comp continuous_hid2_joint
  exact (hc.measurable.stronglyMeasurable.integral_prod_right').measurable

lemma measurable_lam2 :
    Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => lam p.1 p.2) := by
  unfold lam
  exact (Finset.measurable_sum _ fun j _ => ((measurable_pi_apply j).comp measurable_snd).mul
    ((measurable_pi_apply j).comp measurable_fst)).div (measurable_normSq.comp measurable_fst)

lemma measurable_res2 :
    Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => res p.1 p.2) := by
  unfold res
  exact measurable_snd.sub (measurable_lam2.smul measurable_fst)

lemma measurable_sig2 (v : ℝ) :
    Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => sig v p.1 p.2) := by
  unfold sig
  exact ((measurable_normSq.comp measurable_res2).sqrt).const_mul _

/-- **The stand-in distribution of the World network `W = (M₁, M₂, M₃)`**: `standIn` of Part 134
with `μ` uniform on the sphere, `h = hid2 M₁ M₂`, `v = 2/m`, `b = h̄(M₁, M₂)`, `c = M₃ h̄`. -/
noncomputable def nuW (W : MlpParam N m n) : Measure (Fin n → ℝ) :=
  standIn (uniformSphere N) (hid2 W.1 W.2.1) (2 / (m : ℝ)) (hbarW (W.1, W.2.1))
    (W.2.2.mulVec (hbarW (W.1, W.2.1)))

lemma nuW_prob (hN : 1 ≤ N) (W : MlpParam N m n) : IsProbabilityMeasure (nuW W) := by
  have := uniformSphere_isProbability N hN
  exact standIn_prob _ (continuous_hid2 _ _).measurable _ _ _

/-- `W ↦ E_{μ_W} φ` is bounded and measurable. -/
lemma bm_muW (hN : 1 ≤ N) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    BM (fun W : MlpParam N m n => ∫ x, φ x ∂muWn W) := by
  have := uniformSphere_isProbability N hN
  have h1 : BM (fun q : MlpParam N m n × (Fin N → ℝ) => φ (sphPt (mlpEval q.1 q.2))) :=
    hφ.comp (measurable_sphPt.comp continuous_mlpEval_joint.measurable)
  have h2 := h1.integral_right (uniformSphere N)
  have e : (fun W : MlpParam N m n => ∫ x, φ x ∂muWn W) =
      fun W => ∫ u, φ (sphPt (mlpEval W u)) ∂uniformSphere N := by
    funext W
    unfold muWn
    rw [integral_map (measurable_sphPt_mlpEval W).aemeasurable hφ.meas.aestronglyMeasurable]
  rw [e]
  exact h2

/-- `W ↦ E_{ν_W} φ` is bounded and measurable. -/
lemma bm_nuW (hN : 1 ≤ N) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    BM (fun W : MlpParam N m n => ∫ x, φ x ∂nuW W) := by
  have := uniformSphere_isProbability N hN
  have hθ : Measurable (fun q : MlpParam N m n × ((Fin N → ℝ) × (Fin n → ℝ)) =>
      ((q.1.1, q.1.2.1) : HidParam N m)) :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_fst))
  have hb : Measurable (fun q : MlpParam N m n × ((Fin N → ℝ) × (Fin n → ℝ)) =>
      hbarW (q.1.1, q.1.2.1)) := (measurable_hbarW hN).comp hθ
  have hh : Measurable (fun q : MlpParam N m n × ((Fin N → ℝ) × (Fin n → ℝ)) =>
      hid2 q.1.1 q.1.2.1 q.2.1) :=
    continuous_hid2_joint.measurable.comp (hθ.prodMk (measurable_fst.comp measurable_snd))
  have hc : Measurable (fun q : MlpParam N m n × ((Fin N → ℝ) × (Fin n → ℝ)) =>
      q.1.2.2.mulVec (hbarW (q.1.1, q.1.2.1))) :=
    measurable_mulVec_joint.comp
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk hb)
  have hJ : Measurable (fun q : MlpParam N m n × ((Fin N → ℝ) × (Fin n → ℝ)) =>
      lam (hbarW (q.1.1, q.1.2.1)) (hid2 q.1.1 q.1.2.1 q.2.1) •
          q.1.2.2.mulVec (hbarW (q.1.1, q.1.2.1)) +
        sig (2 / (m : ℝ)) (hbarW (q.1.1, q.1.2.1)) (hid2 q.1.1 q.1.2.1 q.2.1) • q.2.2) :=
    ((measurable_lam2.comp (hb.prodMk hh)).smul hc).add
      (((measurable_sig2 (2 / (m : ℝ))).comp (hb.prodMk hh)).smul
        (measurable_snd.comp measurable_snd))
  have h1 : BM (fun q : MlpParam N m n × ((Fin N → ℝ) × (Fin n → ℝ)) =>
      φ (sphPt (lam (hbarW (q.1.1, q.1.2.1)) (hid2 q.1.1 q.1.2.1 q.2.1) •
          q.1.2.2.mulVec (hbarW (q.1.1, q.1.2.1)) +
        sig (2 / (m : ℝ)) (hbarW (q.1.1, q.1.2.1)) (hid2 q.1.1 q.1.2.1 q.2.1) • q.2.2))) :=
    hφ.comp (measurable_sphPt.comp hJ)
  have h2 := h1.integral_right ((uniformSphere N).prod (stdGauss (Fin n)))
  have e : (fun W : MlpParam N m n => ∫ x, φ x ∂nuW W) =
      fun W => ∫ p : (Fin N → ℝ) × (Fin n → ℝ),
        φ (sphPt (lam (hbarW (W.1, W.2.1)) (hid2 W.1 W.2.1 p.1) •
          W.2.2.mulVec (hbarW (W.1, W.2.1)) +
        sig (2 / (m : ℝ)) (hbarW (W.1, W.2.1)) (hid2 W.1 W.2.1 p.1) • p.2))
        ∂((uniformSphere N).prod (stdGauss (Fin n))) := by
    funext W
    unfold nuW standIn
    exact integral_map (measurable_sphPt.comp (measurable_standOut
      (continuous_hid2 W.1 W.2.1).measurable (2 / (m : ℝ)) (hbarW (W.1, W.2.1))
      (W.2.2.mulVec (hbarW (W.1, W.2.1))))).aemeasurable hφ.meas.aestronglyMeasurable
  rw [e]
  exact h2

lemma var_nuW (hN : 1 ≤ N) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) (W : MlpParam N m n) :
    Var[φ; nuW W] = ∫ x, φ x ^ 2 ∂nuW W - (∫ x, φ x ∂nuW W) ^ 2 := by
  have := nuW_prob hN W
  exact var_bm (nuW W) hφ

/-- `W ↦ Var_{ν_W} φ` is bounded and measurable. -/
lemma bm_varW (hN : 1 ≤ N) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    BM (fun W : MlpParam N m n => Var[φ; nuW W]) := by
  simp_rw [var_nuW hN hφ]
  exact (bm_nuW hN hφ.sq).sub (bm_nuW hN hφ).sq

/-- `c ↦ Var_{ν_c} φ` is bounded and measurable (fixed `b`, `h`). -/
lemma bm_var_standIn {U : Type*} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]
    (v : ℝ) (b : Fin m → ℝ) {h : U → Fin m → ℝ} (hh : Measurable h)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    BM (fun c : Fin n → ℝ => Var[φ; standIn μ h v b c]) := by
  have hvar : ∀ c : Fin n → ℝ, Var[φ; standIn μ h v b c] =
      ∫ x, φ x ^ 2 ∂standIn μ h v b c - (∫ x, φ x ∂standIn μ h v b c) ^ 2 := by
    intro c
    have := standIn_prob (n := n) μ hh v b c
    exact var_bm (standIn μ h v b c) hφ
  simp_rw [hvar]
  exact (bm_standIn (n := n) μ v b hh hφ.sq).sub (bm_standIn (n := n) μ v b hh hφ).sq

/-- Fubini for the World network: first `(M₁, M₂)`, then `M₃`. -/
lemma integral_mlp_split {F : MlpParam N m n → ℝ} (hF : BM F) :
    ∫ W, F W ∂mlpGauss N m n =
      ∫ θ, (∫ M₃, F (θ.1, θ.2, M₃) ∂gaussMat n m (2 / (m : ℝ))) ∂hidGauss N m := by
  have e : mlpGauss N m n =
      ((hidGauss N m).prod (gaussMat n m (2 / (m : ℝ)))).map MeasurableEquiv.prodAssoc := by
    unfold mlpGauss hidGauss
    rw [Measure.prodAssoc_prod]
  rw [e, integral_map MeasurableEquiv.prodAssoc.measurable.aemeasurable
    hF.meas.aestronglyMeasurable,
    integral_prod _ ((hF.comp MeasurableEquiv.prodAssoc.measurable).integrable _)]
  rfl

/-- The good event of `(M₁, M₂)` as an event of the World network. -/
def goodW (n : ℕ) : Set (MlpParam (2 * n) (mW n) n) := {W | (W.1, W.2.1) ∈ good136 n}

lemma goodW_meas {n : ℕ} (hn : 1 ≤ n) : MeasurableSet (goodW n) :=
  (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) (good136_meas hn)

theorem goodW_prob {n : ℕ} (hn : 4096 ≤ n) :
    998 / 1000 ≤ (mlpGauss (2 * n) (mW n) n).real (goodW n) := good136_prob_W hn

/-- **The stand-in theorem over the whole World network, on the good event (item 4).** For every
`n ≥ 4096` and every bounded measurable `φ`:
`E_W[1_good·(E_{μ_W} φ − E_{ν_W} φ)²] ≤ ((99/100)/n)·E_W[1_good·Var_{ν_W} φ]`. -/
theorem standIn136_joint {n : ℕ} (hn : 4096 ≤ n) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ W, (goodW n).indicator
        (fun W => ((∫ x, φ x ∂muWn W) - ∫ x, φ x ∂nuW W) ^ 2) W
        ∂mlpGauss (2 * n) (mW n) n ≤
      99 / 100 / (n : ℝ) *
        ∫ W, (goodW n).indicator (fun W => Var[φ; nuW W]) W ∂mlpGauss (2 * n) (mW n) n := by
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  have mG := goodW_meas (n := n) (by omega)
  have b1 : BM ((goodW n).indicator
      (fun W => ((∫ x, φ x ∂muWn W) - ∫ x, φ x ∂nuW W) ^ 2)) :=
    bm_indicator mG ((bm_muW hN hφ).sub (bm_nuW hN hφ)).sq
  have b2 : BM ((goodW n).indicator (fun W => Var[φ; nuW W])) :=
    bm_indicator mG (bm_varW hN hφ)
  rw [integral_mlp_split b1, integral_mlp_split b2, ← integral_const_mul]
  have i1 := ((b1.comp MeasurableEquiv.prodAssoc.measurable).integral_right
    (gaussMat n (mW n) (2 / (mW n : ℝ)))).integrable (hidGauss (2 * n) (mW n))
  have i2 := (((b2.comp MeasurableEquiv.prodAssoc.measurable).integral_right
    (gaussMat n (mW n) (2 / (mW n : ℝ)))).integrable (hidGauss (2 * n) (mW n))).const_mul
    (99 / 100 / (n : ℝ))
  refine integral_mono i1 i2 fun θ => ?_
  by_cases hθ : θ ∈ good136 n
  · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ, (θ.1, θ.2, M₃) ∈ goodW n := fun M₃ => hθ
    simp only [Set.indicator_of_mem (hW _)]
    have h := standIn136 hn hθ hφ
    rw [← cDist_eq, integral_map (measurable_mulVec_right _).aemeasurable
      (bm_var_standIn (uniformSphere (2 * n)) _ _ (continuous_hid2 θ.1 θ.2).measurable
        hφ).meas.aestronglyMeasurable] at h
    exact h
  · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ, (θ.1, θ.2, M₃) ∉ goodW n := fun M₃ => hθ
    simp only [Set.indicator_of_notMem (hW _)]
    simp

lemma abs_integral_le_bound {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] {f : α → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B) : |∫ x, f x ∂P| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := P) (f := f) (C := B)
    (Filter.Eventually.of_forall fun x => by simpa using hB x)
  simpa using this

/-- **The stand-in theorem over the whole World network (item 4, total form).** For every
`n ≥ 4096` and every measurable `φ` with `|φ| ≤ B`:
`E_W (E_{μ_W} φ − E_{ν_W} φ)² ≤ ((99/100)/n)·E_W Var_{ν_W} φ + (8/1000)·B²`
(`8/1000 = 4·0.002`: the square of the error is at most `4B²` off the good event). -/
theorem standIn136_total {n : ℕ} (hn : 4096 ≤ n) {φ : (Fin n → ℝ) → ℝ} (hφ : Measurable φ)
    {B : ℝ} (hB : ∀ x, |φ x| ≤ B) :
    ∫ W, ((∫ x, φ x ∂muWn W) - ∫ x, φ x ∂nuW W) ^ 2 ∂mlpGauss (2 * n) (mW n) n ≤
      99 / 100 / (n : ℝ) * ∫ W, Var[φ; nuW W] ∂mlpGauss (2 * n) (mW n) n +
        8 / 1000 * B ^ 2 := by
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by
    have : (4096 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hφb : BM φ := ⟨hφ, B, hB⟩
  have mG := goodW_meas (n := n) (by omega)
  set P := mlpGauss (2 * n) (mW n) n with hP
  set f : MlpParam (2 * n) (mW n) n → ℝ :=
    fun W => ((∫ x, φ x ∂muWn W) - ∫ x, φ x ∂nuW W) ^ 2 with hf
  have bf : BM f := ((bm_muW hN hφb).sub (bm_nuW hN hφb)).sq
  have bV : BM (fun W : MlpParam (2 * n) (mW n) n => Var[φ; nuW W]) := bm_varW hN hφb
  have hf4 : ∀ W, f W ≤ 4 * B ^ 2 := by
    intro W
    have := muWn_isProbability hN W
    have := nuW_prob hN W
    have h1 := abs_integral_le_bound (muWn W) hB
    have h2 := abs_integral_le_bound (nuW W) hB
    have h3 : |(∫ x, φ x ∂muWn W) - ∫ x, φ x ∂nuW W| ≤ 2 * B := by
      have := abs_sub (∫ x, φ x ∂muWn W) (∫ x, φ x ∂nuW W)
      linarith
    have h4 : f W = |(∫ x, φ x ∂muWn W) - ∫ x, φ x ∂nuW W| ^ 2 := by
      simp only [hf, sq_abs]
    rw [h4]
    have := pow_le_pow_left₀ (abs_nonneg _) h3 2
    nlinarith
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
  have e3 : ∫ W, (goodW n).indicator (fun W => Var[φ; nuW W]) W ∂P ≤
      ∫ W, Var[φ; nuW W] ∂P := by
    refine integral_mono ((bm_indicator mG bV).integrable P) (bV.integrable P) fun W => ?_
    by_cases hW : W ∈ goodW n
    · rw [Set.indicator_of_mem hW]
    · rw [Set.indicator_of_notMem hW]; exact variance_nonneg _ _
  have e4 := standIn136_joint hn hφb
  have e5 : 99 / 100 / (n : ℝ) * ∫ W, (goodW n).indicator (fun W => Var[φ; nuW W]) W ∂P ≤
      99 / 100 / (n : ℝ) * ∫ W, Var[φ; nuW W] ∂P :=
    mul_le_mul_of_nonneg_left e3 (by positivity)
  rw [e1]
  linarith

/-- **The tail form.** For every `n ≥ 4096`, bounded measurable `φ` and `t > 0`:
`Pr_W(|E_{μ_W} φ − E_{ν_W} φ| ≥ t) ≤ 0.002 + ((99/100)/n)·E_W Var_{ν_W} φ / t²`. -/
theorem standIn136_tail {n : ℕ} (hn : 4096 ≤ n) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) {t : ℝ}
    (ht : 0 < t) :
    (mlpGauss (2 * n) (mW n) n).real
        {W | t ≤ |(∫ x, φ x ∂muWn W) - ∫ x, φ x ∂nuW W|} ≤
      2 / 1000 +
        99 / 100 / (n : ℝ) * (∫ W, Var[φ; nuW W] ∂mlpGauss (2 * n) (mW n) n) / t ^ 2 := by
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by
    have : (4096 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have mG := goodW_meas (n := n) (by omega)
  set P := mlpGauss (2 * n) (mW n) n with hP
  set f : MlpParam (2 * n) (mW n) n → ℝ :=
    fun W => ((∫ x, φ x ∂muWn W) - ∫ x, φ x ∂nuW W) ^ 2 with hf
  have bf : BM f := ((bm_muW hN hφ).sub (bm_nuW hN hφ)).sq
  have bV : BM (fun W : MlpParam (2 * n) (mW n) n => Var[φ; nuW W]) := bm_varW hN hφ
  have bg : BM ((goodW n).indicator f) := bm_indicator mG bf
  have hg0 : ∀ W, 0 ≤ (goodW n).indicator f W := fun W =>
    Set.indicator_nonneg (fun W _ => sq_nonneg _) W
  have hsub : {W | t ≤ |(∫ x, φ x ∂muWn W) - ∫ x, φ x ∂nuW W|} ⊆
      (goodW n)ᶜ ∪ {W | t ^ 2 ≤ (goodW n).indicator f W} := by
    intro W hW
    by_cases hWG : W ∈ goodW n
    · right
      simp only [Set.mem_ofPred_eq] at hW ⊢
      rw [Set.indicator_of_mem hWG]
      have := pow_le_pow_left₀ ht.le hW 2
      simpa only [hf, sq_abs] using this
    · left
      exact hWG
  have h1 : P.real (goodW n)ᶜ ≤ 2 / 1000 := by
    rw [measureReal_compl mG, probReal_univ]
    have := goodW_prob hn
    linarith
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := (goodW n).indicator f)
    (Filter.Eventually.of_forall hg0) (bg.integrable P) (t ^ 2)
  have e3 : ∫ W, (goodW n).indicator (fun W => Var[φ; nuW W]) W ∂P ≤
      ∫ W, Var[φ; nuW W] ∂P := by
    refine integral_mono ((bm_indicator mG bV).integrable P) (bV.integrable P) fun W => ?_
    by_cases hW : W ∈ goodW n
    · rw [Set.indicator_of_mem hW]
    · rw [Set.indicator_of_notMem hW]; exact variance_nonneg _ _
  have e4 := standIn136_joint hn hφ
  have e5 : 99 / 100 / (n : ℝ) * ∫ W, (goodW n).indicator (fun W => Var[φ; nuW W]) W ∂P ≤
      99 / 100 / (n : ℝ) * ∫ W, Var[φ; nuW W] ∂P :=
    mul_le_mul_of_nonneg_left e3 (by positivity)
  have ht2 : 0 < t ^ 2 := by positivity
  have h2 : P.real {W | t ^ 2 ≤ (goodW n).indicator f W} ≤
      99 / 100 / (n : ℝ) * (∫ W, Var[φ; nuW W] ∂P) / t ^ 2 := by
    rw [le_div_iff₀ ht2]
    have : (∫ W, (goodW n).indicator f W ∂P) ≤
        99 / 100 / (n : ℝ) * ∫ W, Var[φ; nuW W] ∂P := e4.trans e5
    linarith
  calc P.real {W | t ≤ |(∫ x, φ x ∂muWn W) - ∫ x, φ x ∂nuW W|}
      ≤ P.real ((goodW n)ᶜ ∪ {W | t ^ 2 ≤ (goodW n).indicator f W}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ P.real (goodW n)ᶜ + P.real {W | t ^ 2 ≤ (goodW n).indicator f W} :=
        measureReal_union_le _ _
    _ ≤ _ := add_le_add h1 h2

end BstLean.Part136
