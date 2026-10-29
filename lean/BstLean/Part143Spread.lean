import BstLean.Part142Spread

/-!
# Part 143, lever 2 (orthogonality over the inputs): the realized spread with the factor 2

Role: `delegations/statements/p143-spec.md`. Part 142 (`cond_sq_dist`) proves, for fixed
`(W, A, F₁, F₂)`: `E_{F₃}(sd² − c)² ≤ 3·E_{u,u′}(kD − c)²`, from
`E_{F₃}(sd² − c)² = (α·tr Σ − c)² + 2α²‖Σ‖_F²` with the two bounds `(α·tr Σ − c)² ≤ QD` (Jensen)
and `α²‖Σ‖_F² ≤ QD` separately. Here the two terms are bounded TOGETHER:
`(α·tr Σ − c)² + α²‖Σ‖_F² ≤ QD` (the mean of `kD − c` over `(u, u′)` and the doubly centred part
of `kD` are orthogonal). So the factor `3` becomes `2`.

* `frob_QD`: `α²‖Σ‖_F² ≤ QD c′ r` for every constant `c′`; `tr_QD`: `α·tr Σ − c = E(kD − c)`.
* `QD_shift`: `QD (c + m) r = QD c r − m²` for `m = E_{u,u′}(kD − c)`.
* `cond_sq_dist2`: `E_{F₃}(sd² − c)² ≤ 2·QD c r`.
* **`spread_L2_dist2`**: from `‖kD − c‖₂ ≤ e`: `E_{W,A,F}(sd² − c)² ≤ 2e²`.
* **`spreadLow_dist2`**: Chebyshev: `Pr(sd² < θ·c) ≤ 2e²/((1 − θ)c)²`, `c > 0`, `θ < 1`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139
open BstLean.Part142

variable {N mW n mA mF : ℕ}

/-- `kD − c` is bounded and measurable in `(u, u′)` for fixed networks. -/
lemma kD_sub_BM (hn : 1 ≤ n) (r : Rest N mW n mA mF) (c : ℝ) :
    BM (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => kD (uu, r) - c) := by
  set α : ℝ := 2 / (mF : ℝ) with hα
  set z := zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 with hz
  have hzm : ∀ i, Measurable fun u => z u i := zU_meas _ _ _ _
  have hzb : ∃ B : ℝ, ∀ u i, |z u i| ≤ B := zU_bdd hn _ _ _ _
  have hzB : ∀ i, BM (fun u => z u i) := fun i => ⟨hzm i, hzb.imp fun _ hB u => hB u i⟩
  have hdB : BM (fun p : (Fin N → ℝ) × (Fin N → ℝ) => (∑ i, (z p.1 i - z p.2 i) ^ 2) / 2) := by
    have h1 : BM (fun p : (Fin N → ℝ) × (Fin N → ℝ) => ∑ i, (z p.1 i - z p.2 i) ^ 2) :=
      BM.sum _ fun i _ => ((hzB i).fst.sub (hzB i).snd).sq
    have := h1.mul (BM.const (α := (Fin N → ℝ) × (Fin N → ℝ)) (1 / 2))
    simpa [div_eq_mul_inv] using this
  have hkD : ∀ uu : (Fin N → ℝ) × (Fin N → ℝ),
      kD (uu, r) = α * ((∑ i, (z uu.1 i - z uu.2 i) ^ 2) / 2) := fun uu => kD_zU uu r
  have := ((BM.const (α := (Fin N → ℝ) × (Fin N → ℝ)) α).mul hdB).sub (BM.const c)
  simpa [hkD] using this

/-- The trace: `α·tr Σ − c = E_{u,u′}(kD − c)`. -/
lemma tr_QD (hn : 1 ≤ n) (hN : 1 ≤ N) (r : Rest N mW n mA mF) (c : ℝ) :
    2 / (mF : ℝ) * (covMat r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1).trace - c =
      ∫ uu, (kD (uu, r) - c) ∂lawU2 N := by
  have := uniformSphere_isProbability N hN
  set α : ℝ := 2 / (mF : ℝ) with hα
  set z := zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 with hz
  have hzm : ∀ i, Measurable fun u => z u i := zU_meas _ _ _ _
  have hzb : ∃ B : ℝ, ∀ u i, |z u i| ≤ B := zU_bdd hn _ _ _ _
  have hkD : ∀ uu : (Fin N → ℝ) × (Fin N → ℝ),
      kD (uu, r) = α * ((∑ i, (z uu.1 i - z uu.2 i) ^ 2) / 2) := fun uu => kD_zU uu r
  have hkB := kD_sub_BM hn r c
  have e1 : (covMat r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1).trace =
      ∑ i, covV (uniformSphere N) z i i := by
    simp only [Matrix.trace, Matrix.diag, covMat_eq, hz]
  rw [e1, covV_trace_dist (uniformSphere N) z hzm hzb]
  have hpr : IsProbabilityMeasure (lawU2 N) := lawU2_prob hN
  have iD : Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => kD (uu, r)) (lawU2 N) := by
    have := (hkB.add (BM.const c)).integrable (lawU2 N)
    simpa using this
  rw [integral_sub iD (integrable_const _), integral_const]
  simp only [probReal_univ, one_smul]
  simp_rw [hkD]
  rw [integral_const_mul]
  rfl

/-- The Frobenius norm: `α²·Σ_{ij} Σ_{ij}² ≤ QD c′ r` for every constant `c′`. -/
lemma frob_QD (hn : 1 ≤ n) (hN : 1 ≤ N) (hmF : 1 ≤ mF) (r : Rest N mW n mA mF) (c : ℝ) :
    (2 / (mF : ℝ)) ^ 2 * ∑ i, ∑ j, covMat r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 i j ^ 2 ≤ QD c r := by
  have := uniformSphere_isProbability N hN
  have hm : (0 : ℝ) < mF := by exact_mod_cast hmF
  set α : ℝ := 2 / (mF : ℝ) with hα
  have hα0 : 0 < α := by positivity
  set z := zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 with hz
  have hzm : ∀ i, Measurable fun u => z u i := zU_meas _ _ _ _
  have hzb : ∃ B : ℝ, ∀ u i, |z u i| ≤ B := zU_bdd hn _ _ _ _
  have hkD : ∀ uu : (Fin N → ℝ) × (Fin N → ℝ),
      kD (uu, r) = α * ((∑ i, (z uu.1 i - z uu.2 i) ^ 2) / 2) := fun uu => kD_zU uu r
  have h := covV_frob_dist (uniformSphere N) z hzm hzb (c / α)
  simp_rw [covMat_eq]
  have h2 := mul_le_mul_of_nonneg_left h (sq_nonneg α)
  refine h2.trans (le_of_eq ?_)
  unfold QD lawU2
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun uu => ?_)
  simp only
  rw [hkD]
  field_simp

/-- `QD (c + m) r = QD c r − m²` for the mean `m = E_{u,u′}(kD − c)`. -/
lemma QD_shift (hn : 1 ≤ n) (hN : 1 ≤ N) (r : Rest N mW n mA mF) (c : ℝ) :
    QD (c + ∫ uu, (kD (uu, r) - c) ∂lawU2 N) r =
      QD c r - (∫ uu, (kD (uu, r) - c) ∂lawU2 N) ^ 2 := by
  have hpr : IsProbabilityMeasure (lawU2 N) := lawU2_prob hN
  have hkB := kD_sub_BM hn r c
  set m : ℝ := ∫ uu, (kD (uu, r) - c) ∂lawU2 N with hm
  have i1 : Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => (kD (uu, r) - c) ^ 2) (lawU2 N) :=
    hkB.sq.integrable _
  have i2 : Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => kD (uu, r) - c) (lawU2 N) :=
    hkB.integrable _
  have e : (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => (kD (uu, r) - (c + m)) ^ 2) =
      fun uu => (kD (uu, r) - c) ^ 2 - (2 * m * (kD (uu, r) - c) - m ^ 2) := by
    funext uu; ring
  have i3 : Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => 2 * m * (kD (uu, r) - c) - m ^ 2)
      (lawU2 N) := (i2.const_mul _).sub (integrable_const _)
  have e3 : ∫ uu, (2 * m * (kD (uu, r) - c) - m ^ 2) ∂lawU2 N = 2 * m * m - m ^ 2 := by
    rw [integral_sub (i2.const_mul _) (integrable_const _), integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul, ← hm]
  unfold QD
  rw [e, integral_sub i1 i3, e3]
  ring

/-- **The second moment of the realized spread over the last matrix of `F`, with the factor 2.**
For fixed `(W, A, F₁, F₂)` and a constant `c`: `E_{F₃}(sd² − c)² ≤ 2·E_{u,u′}(kD − c)²`. -/
lemma cond_sq_dist2 (hn : 1 ≤ n) (hN : 1 ≤ N) (hmF : 1 ≤ mF) (r : Rest N mW n mA mF) (c : ℝ) :
    Integrable (fun F₃ : Matrix (Fin 1) (Fin mF) ℝ =>
      (sdn r.1 r.2.1 (r.2.2.2.1, r.2.2.2.2.1, F₃) ^ 2 - c) ^ 2) (gaussMat 1 mF (2 / (mF : ℝ))) ∧
    ∫ F₃, (sdn r.1 r.2.1 (r.2.2.2.1, r.2.2.2.2.1, F₃) ^ 2 - c) ^ 2 ∂gaussMat 1 mF (2 / (mF : ℝ)) ≤
      2 * QD c r := by
  have hm : (0 : ℝ) < mF := by exact_mod_cast hmF
  have htr := tr_QD hn hN r c
  set m : ℝ := ∫ uu, (kD (uu, r) - c) ∂lawU2 N with hmd
  have hfr := frob_QD hn hN hmF r (c + m)
  rw [hmd, QD_shift hn hN r c, ← hmd] at hfr
  have e : (fun F₃ : Matrix (Fin 1) (Fin mF) ℝ =>
      (sdn r.1 r.2.1 (r.2.2.2.1, r.2.2.2.2.1, F₃) ^ 2 - c) ^ 2) =
      fun F₃ => (rowOf 0 F₃ ⬝ᵥ covMat r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 *ᵥ rowOf 0 F₃ - c) ^ 2 := by
    funext F₃
    rw [sdn_last hn hN, Real.sq_sqrt (covMat_nonneg hn hN _ _ _ _ _)]
  obtain ⟨hi, he⟩ := gaussRow_qform_sq (2 / (mF : ℝ)) (by positivity)
    (covMat r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1) (covMat_symm _ _ _ _) c
  rw [e]
  refine ⟨hi, ?_⟩
  rw [he, htr]
  nlinarith [sq_nonneg m]

/-- **The second moment of the realized spread around `c`, distance form.** If
`‖kD − c‖₂ ≤ e` under `(u, u′) ⊗ (W, A, A′, F)`, then `E(sd² − c)² ≤ 2e²`. -/
theorem spread_L2_dist2 (hn : 1 ≤ n) (hN : 1 ≤ N) (hmF : 1 ≤ mF) {c e : ℝ} (he : 0 ≤ e)
    (hD : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF => kD ω - c) e) :
    ∫⁻ r : Rest N mW n mA mF,
        ENNReal.ofReal ((sdn r.1 r.2.1 r.2.2.2 ^ 2 - c) ^ 2) ∂lawR N mW n mA mF ≤
      ENNReal.ofReal (2 * e ^ 2) := by
  have := lawU2_prob hN
  set f : Rest N mW n mA mF → ℝ≥0∞ :=
    fun r => ENNReal.ofReal ((sdn r.1 r.2.1 r.2.2.2 ^ 2 - c) ^ 2) with hf
  set Rr : Rest N mW n mA mF → ℝ := fun r => 2 * QD c r with hRr
  set g : Rest N mW n mA mF → ℝ≥0∞ := fun r => ENNReal.ofReal (Rr r) with hg
  have mf : Measurable f :=
    ENNReal.measurable_ofReal.comp ((((measurable_sdn_R hN).pow_const 2).sub
      measurable_const).pow_const 2)
  have mQ : Measurable (QD (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) c) :=
    ((measurable_kD.sub measurable_const).pow_const 2).stronglyMeasurable.integral_prod_left'.measurable
  have mRr : Measurable Rr := mQ.const_mul 2
  have mg : Measurable g := ENNReal.measurable_ofReal.comp mRr
  have h5 : ∀ (W : MlpParam N mW n) (A A' : MlpParam n mA n) (F₁ : Matrix (Fin mF) (Fin n) ℝ)
      (F₂ : Matrix (Fin mF) (Fin mF) ℝ),
      ∫⁻ F₃, f (W, A, A', F₁, F₂, F₃) ∂gaussMat 1 mF (2 / (mF : ℝ)) ≤
        ∫⁻ F₃, g (W, A, A', F₁, F₂, F₃) ∂gaussMat 1 mF (2 / (mF : ℝ)) := by
    intro W A A' F₁ F₂
    have hconst : ∀ F₃ : Matrix (Fin 1) (Fin mF) ℝ,
        g (W, A, A', F₁, F₂, F₃) = g (W, A, A', F₁, F₂, 0) := fun _ => rfl
    simp_rw [hconst]
    rw [lintegral_const, measure_univ, mul_one]
    obtain ⟨hi, hle⟩ := cond_sq_dist2 hn hN hmF
      ((W, A, A', F₁, F₂, 0) : Rest N mW n mA mF) c
    have e : ∫⁻ F₃, f (W, A, A', F₁, F₂, F₃) ∂gaussMat 1 mF (2 / (mF : ℝ)) =
        ENNReal.ofReal (∫ F₃, (sdn W A (F₁, F₂, F₃) ^ 2 - c) ^ 2
          ∂gaussMat 1 mF (2 / (mF : ℝ))) :=
      (ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
    rw [e]
    exact ENNReal.ofReal_le_ofReal hle
  have h4 : ∀ (W : MlpParam N mW n) (A A' : MlpParam n mA n) (F₁ : Matrix (Fin mF) (Fin n) ℝ),
      ∫⁻ y, f (W, A, A', F₁, y)
          ∂((gaussMat mF mF (2 / (mF : ℝ))).prod (gaussMat 1 mF (2 / (mF : ℝ)))) ≤
        ∫⁻ y, g (W, A, A', F₁, y)
          ∂((gaussMat mF mF (2 / (mF : ℝ))).prod (gaussMat 1 mF (2 / (mF : ℝ)))) :=
    fun W A A' F₁ => lintegral_prod_mono'
      (f := fun y => f (W, A, A', F₁, y)) (g := fun y => g (W, A, A', F₁, y))
      (mf.comp (by fun_prop)) (mg.comp (by fun_prop)) (fun F₂ => h5 W A A' F₁ F₂)
  have h3 : ∀ (W : MlpParam N mW n) (A A' : MlpParam n mA n),
      ∫⁻ y, f (W, A, A', y) ∂mlpGauss n mF 1 ≤ ∫⁻ y, g (W, A, A', y) ∂mlpGauss n mF 1 :=
    fun W A A' => lintegral_prod_mono'
      (f := fun y => f (W, A, A', y)) (g := fun y => g (W, A, A', y))
      (mf.comp (by fun_prop)) (mg.comp (by fun_prop)) (fun F₁ => h4 W A A' F₁)
  have h2 : ∀ (W : MlpParam N mW n) (A : MlpParam n mA n),
      ∫⁻ y, f (W, A, y) ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) ≤
        ∫⁻ y, g (W, A, y) ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) :=
    fun W A => lintegral_prod_mono'
      (f := fun y => f (W, A, y)) (g := fun y => g (W, A, y))
      (mf.comp (by fun_prop)) (mg.comp (by fun_prop)) (fun A' => h3 W A A')
  have h1 : ∀ W : MlpParam N mW n,
      ∫⁻ y, f (W, y) ∂((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) ≤
        ∫⁻ y, g (W, y) ∂((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) :=
    fun W => lintegral_prod_mono'
      (f := fun y => f (W, y)) (g := fun y => g (W, y))
      (mf.comp (by fun_prop)) (mg.comp (by fun_prop)) (fun A => h2 W A)
  have h0 : ∫⁻ r, f r ∂lawR N mW n mA mF ≤ ∫⁻ r, g r ∂lawR N mW n mA mF :=
    lintegral_prod_mono' mf mg h1
  refine h0.trans ?_
  have iQ : Integrable (QD (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) c)
      (lawR N mW n mA mF) := hD.int_sq.integral_prod_right
  have eQ : ∫ r, QD c r ∂lawR N mW n mA mF ≤ e ^ 2 := by
    have := integral_prod_symm (μ := lawU2 N) (ν := lawR N mW n mA mF) _ hD.int_sq
    unfold QD
    rw [← this]
    exact hD.le
  have iR : Integrable Rr (lawR N mW n mA mF) := iQ.const_mul 2
  have hR0 : ∀ r, 0 ≤ Rr r := fun r => by
    have := QD_nonneg c r
    rw [hRr]
    positivity
  rw [hg, ← ofReal_integral_eq_lintegral_ofReal iR (Filter.Eventually.of_forall hR0)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hRr, integral_const_mul]
  linarith

/-- **Chebyshev's inequality for the realized spread, distance form, all widths.** With
`‖kD − c‖₂ ≤ e`, `c > 0` and `θ < 1`: `Pr_{W,A,F}(sd² < θ·c) ≤ 2e²/((1 − θ)·c)²`. -/
theorem spreadLow_dist2 (hn : 1 ≤ n) (hN : 1 ≤ N) (hmF : 1 ≤ mF) {c e : ℝ} (he : 0 ≤ e)
    (hD : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF => kD ω - c) e)
    (hc : 0 < c) {θ : ℝ} (hθ : θ < 1) :
    ((mlpGauss N mW n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))).real
        {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * c} ≤
      2 * e ^ 2 / ((1 - θ) * c) ^ 2 := by
  set T := (mlpGauss N mW n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)) with hT
  have hgap : 0 < (1 - θ) * c := mul_pos (by linarith) hc
  have hgap2 : 0 < ((1 - θ) * c) ^ 2 := by positivity
  set F : MlpParam N mW n × MlpParam n mA n × MlpParam n mF 1 → ℝ≥0∞ :=
    fun t => ENNReal.ofReal ((sdn t.1 t.2.1 t.2.2 ^ 2 - c) ^ 2) with hF
  have mF' : Measurable F :=
    ENNReal.measurable_ofReal.comp ((((measurable_sdn (mA := mA) (mF := mF) hN).pow_const 2).sub
      measurable_const).pow_const 2)
  have mπ : Measurable (fun r : Rest N mW n mA mF => (r.1, r.2.1, r.2.2.2)) := by fun_prop
  have hL : ∫⁻ t, F t ∂T ≤ ENNReal.ofReal (2 * e ^ 2) := by
    rw [hT, ← lawR_drop, lintegral_map mF' mπ]
    exact spread_L2_dist2 hn hN hmF he hD
  have hsub : {t : MlpParam N mW n × MlpParam n mA n × MlpParam n mF 1 |
      sdn t.1 t.2.1 t.2.2 ^ 2 < θ * c} ⊆ {t | ENNReal.ofReal (((1 - θ) * c) ^ 2) ≤ F t} := by
    intro t ht
    have ht' : sdn t.1 t.2.1 t.2.2 ^ 2 < θ * c := ht
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith
  have hmark := mul_meas_ge_le_lintegral (μ := T) mF' (ENNReal.ofReal (((1 - θ) * c) ^ 2))
  have h1 : ENNReal.ofReal (((1 - θ) * c) ^ 2) * T {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * c} ≤
      ENNReal.ofReal (2 * e ^ 2) :=
    (mul_le_mul' le_rfl (measure_mono hsub)).trans (hmark.trans hL)
  have hv : (0 : ℝ) ≤ 2 * e ^ 2 := by positivity
  rw [le_div_iff₀ hgap2, mul_comm]
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hgap2.le, ENNReal.toReal_ofReal hv] at h2
  exact h2



end BstLean.Part143

open BstLean.Part143 in
#print axioms cond_sq_dist2
open BstLean.Part143 in
#print axioms spread_L2_dist2
open BstLean.Part143 in
#print axioms spreadLow_dist2
