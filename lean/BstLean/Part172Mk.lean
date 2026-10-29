import BstLean.Part172Frm
import BstLean.Part172AMeas
import BstLean.Part172Mom

/-!
# Part 172 (file `Mk`): Markov of order 64 for a first-layer tangential statistic

No proof is left open; no `native_decide` or `axiom` is used.

Fix the World data (through `c₀`), a latitude `s` and a direction field `F(A₁, v)` that is
admissible for every `v` and has `|F|² ≤ t_A`. Put
`T(A₁, v) = (1 − s²)·latSq((D₁A₁)ᵀF, u, w)` (the paper's `(1 − s²)Ψ_F`).
* **`mk_markov`**: `ν{A₁ : K⁶⁴ < E_v |T|⁶⁴} ≤ ((1 − s²)·4.25/n²)⁶⁴ / K⁶⁴`
  (Markov, Tonelli, and the frame moment `frame_mom_num`).
* `mk_bdd`: `|T(A₁, v)| ≤ 3|1 − s²| t_A Σ A₁ᵢⱼ²` (needed for the moment chain).
-/

namespace BstLean.Part172

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part161 (xLat uHat)
open BstLean.Part162 (dirW)
open BstLean.Part167 (latSq D1A1)
open BstLean.Part170 (tA)
open BstLean.Part53 (unitF53)

variable {n : ℕ}

/-- The tangential statistic of a direction field. -/
noncomputable def Tf (c₀ : Ret n) (s : ℝ)
    (F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (v : Fin (n - 1) → ℝ) : ℝ :=
  (1 - s ^ 2) * latSq (vecMul (F A v) (D1A1 A (xLat c₀ s (unitF53 v)))) (uHat c₀)
    (dirW c₀ (unitF53 v))

lemma mk_dot_sq_le {ι : Type*} [Fintype ι] (g u : ι → ℝ) :
    (∑ i, g i * u i) ^ 2 ≤ normSq g * normSq u := by
  have := BstLean.Part170.abs_dot_le g u
  unfold dotProduct at this
  have h2 : (∑ i, g i * u i) ^ 2 ≤ (√(normSq g) * √(normSq u)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  rwa [mul_pow, Real.sq_sqrt (BstLean.Part171.normSq_nonneg' _),
    Real.sq_sqrt (BstLean.Part171.normSq_nonneg' _)] at h2

lemma mk_latSq_abs {ι : Type*} [Fintype ι] (g u w : ι → ℝ) :
    |latSq g u w| ≤ normSq g * (1 + normSq u + normSq w) := by
  unfold latSq
  have h1 := mk_dot_sq_le g u
  have h2 := mk_dot_sq_le g w
  have hg : ∑ i, g i ^ 2 = normSq g := rfl
  have hg0 := BstLean.Part171.normSq_nonneg' g
  have hu0 := BstLean.Part171.normSq_nonneg' u
  have hw0 := BstLean.Part171.normSq_nonneg' w
  rw [hg, abs_le]
  constructor <;> nlinarith [sq_nonneg (∑ i, g i * u i), sq_nonneg (∑ i, g i * w i),
    mul_nonneg hg0 hu0, mul_nonneg hg0 hw0]

lemma mk_vecMul_le {m k : ℕ} (e : Fin m → ℝ) (M : Matrix (Fin m) (Fin k) ℝ) :
    normSq (vecMul e M) ≤ normSq e * ∑ i, ∑ l, M i l ^ 2 := by
  unfold normSq
  have : ∀ l, (vecMul e M l) ^ 2 ≤ (∑ i, e i ^ 2) * ∑ i, M i l ^ 2 := fun l => by
    simp only [vecMul, dotProduct]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ e (fun i => M i l)
  calc ∑ l, vecMul e M l ^ 2 ≤ ∑ l, (∑ i, e i ^ 2) * ∑ i, M i l ^ 2 := Finset.sum_le_sum fun l _ => this l
    _ = (∑ i, e i ^ 2) * ∑ i, ∑ l, M i l ^ 2 := by rw [← Finset.mul_sum, Finset.sum_comm]

lemma mk_D1A1_le {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (x : Fin k → ℝ) :
    ∑ i, ∑ l, D1A1 A x i l ^ 2 ≤ ∑ i, ∑ l, A i l ^ 2 := by
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => ?_
  simp only [D1A1, Matrix.of_apply, mul_pow]
  have h0 := BstLean.Part151.mask_nonneg ((A *ᵥ x) i)
  have h1 := BstLean.Part151.mask_le_one ((A *ᵥ x) i)
  nlinarith [sq_nonneg (A i l), mul_le_one₀ h1 h0 h1]

lemma mk_dirW_le (hn : 1 ≤ n) (c : Ret n) (v : Fin (n - 1) → ℝ) :
    normSq (dirW c (unitF53 v)) ≤ 1 := by
  unfold dirW
  rw [BstLean.Part161.hh_normSq, BstLean.Part161.normSq_consV hn]
  have hu : normSq (unitF53 v) ≤ 1 := by
    have h := BstLean.Part162.radF_unitF_le v
    have h3 : normSq (unitF53 v) = BstLean.Part53.radF53 (unitF53 v) ^ 2 :=
      (BstLean.Part162.radF_sq _).symm
    rw [h3]
    have := BstLean.Part162.radF_nonneg (unitF53 v)
    nlinarith
  linarith

/-- The pointwise bound of the statistic. -/
lemma mk_bdd (hn : 1 ≤ n) {c₀ : Ret n} (hc : c₀.1.2 ≠ 0) (s : ℝ)
    (F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ)
    (hB : ∀ A v, normSq (F A v) ≤ tA n) (A : Matrix (Fin (mA n)) (Fin n) ℝ)
    (v : Fin (n - 1) → ℝ) :
    |Tf c₀ s F A v| ≤ |1 - s ^ 2| * (tA n * (∑ i, ∑ l, A i l ^ 2) * 3) := by
  unfold Tf
  rw [abs_mul]
  gcongr
  refine (mk_latSq_abs _ _ _).trans ?_
  rw [BstLean.Part161.normSq_uHat hc]
  have hw := mk_dirW_le hn c₀ v
  have hg := (mk_vecMul_le (F A v) (D1A1 A (xLat c₀ s (unitF53 v)))).trans
    (mul_le_mul (hB A v) (mk_D1A1_le A _) (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _) (BstLean.Part171.tA_nonneg n))
  have hg0 := BstLean.Part171.normSq_nonneg' (vecMul (F A v) (D1A1 A (xLat c₀ s (unitF53 v))))
  have hA0 : 0 ≤ tA n * ∑ i, ∑ l, A i l ^ 2 := mul_nonneg (BstLean.Part171.tA_nonneg n)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  nlinarith [BstLean.Part171.normSq_nonneg' (dirW c₀ (unitF53 v))]

lemma mk_meas_D1A1 {β : Type*} [MeasurableSpace β] {A : β → Matrix (Fin (mA n)) (Fin n) ℝ}
    {x : β → Fin n → ℝ} (hA : Measurable A) (hx : Measurable x) :
    Measurable (fun b => D1A1 (A b) (x b)) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun l => ?_
  simp only [D1A1, Matrix.of_apply]
  have hc : Continuous (fun q : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin n → ℝ) => (q.1 *ᵥ q.2) i) := by
    simp only [mulVec, dotProduct]; fun_prop
  refine (BstLean.Part151.measurable_mask.comp (hc.measurable.comp (hA.prodMk hx))).mul ?_
  exact (measurable_pi_apply l).comp ((measurable_pi_apply i).comp hA)

lemma mk_cont_latSq (u : Fin n → ℝ) :
    Continuous (fun q : (Fin n → ℝ) × (Fin n → ℝ) => latSq q.1 u q.2) := by
  unfold latSq
  refine ((continuous_finset_sum _ fun i _ => ?_).sub ?_).sub ?_
  · exact ((continuous_apply i).comp continuous_fst).pow 2
  · exact (continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp continuous_fst).mul continuous_const).pow 2
  · exact (continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)).pow 2

lemma mk_cont_vecMul :
    Continuous (fun q : (Fin (mA n) → ℝ) × Matrix (Fin (mA n)) (Fin n) ℝ => vecMul q.1 q.2) := by
  refine continuous_pi fun l => ?_
  simp only [vecMul, dotProduct]
  exact continuous_finset_sum _ fun i _ => ((continuous_apply i).comp continuous_fst).mul
    ((continuous_apply l).comp ((continuous_apply i).comp continuous_snd))

lemma mk_meas_Tf (c₀ : Ret n) (s : ℝ)
    {F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ}
    (hF : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => F p.1 p.2)) :
    Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => Tf c₀ s F p.1 p.2) := by
  simp only [Tf]
  have hx : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      xLat c₀ s (unitF53 p.2)) :=
    BstLean.Part161.measurable_xLat_comp c₀ measurable_const
      (BstLean.Part53.measurable_unitF.comp measurable_snd)
  have hD := mk_meas_D1A1 measurable_fst hx
  have hV : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      vecMul (F p.1 p.2) (D1A1 p.1 (xLat c₀ s (unitF53 p.2)))) := by
    exact (mk_cont_vecMul (n := n)).measurable.comp (hF.prodMk hD)
  have hW : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      dirW c₀ (unitF53 p.2)) := by
    unfold dirW
    have hc : Continuous (fun e : Fin (n - 1) → ℝ =>
        (BstLean.Part161.hhMat (uHat c₀)).mulVec (BstLean.Part161.consV (n := n) 0 e)) := by
      have := BstLean.Part162.continuous_consV (n := n)
      exact Continuous.matrix_mulVec continuous_const
        (this.comp (continuous_const.prodMk continuous_id))
    exact hc.measurable.comp (BstLean.Part53.measurable_unitF.comp measurable_snd)
  have hL := mk_cont_latSq (n := n) (uHat c₀)
  have hLW : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      latSq (vecMul (F p.1 p.2) (D1A1 p.1 (xLat c₀ s (unitF53 p.2)))) (uHat c₀)
        (dirW c₀ (unitF53 p.2))) :=
    hL.measurable.comp (f := fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      (vecMul (F p.1 p.2) (D1A1 p.1 (xLat c₀ s (unitF53 p.2))), dirW c₀ (unitF53 p.2)))
      (hV.prodMk hW)
  exact hLW.const_mul (1 - s ^ 2)

/-- **Markov of order 64 for a tangential statistic.** -/
theorem mk_markov (hn : 80000 ≤ n) {c₀ : Ret n} (hc : c₀.1.2 ≠ 0) {s : ℝ} (hs : s ^ 2 ≤ 1)
    (F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ)
    (hF : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => F p.1 p.2))
    (hadm : ∀ v, BstLean.Part172.fr_Adm (xLat c₀ s (unitF53 v)) (uHat c₀) (fun A => F A v))
    (hB : ∀ A v, normSq (F A v) ≤ tA n) {K : ℝ} (hK : 0 < K) :
    gaussMat (mA n) n (2 / (n : ℝ))
        {A | K ^ 64 < ∫ v, |Tf c₀ s F A v| ^ 64 ∂stdGauss (Fin (n - 1))} ≤
      ENNReal.ofReal (((1 - s ^ 2) * (425 / 100 / (n : ℝ) ^ 2)) ^ 64) / ENNReal.ofReal (K ^ 64) := by
  have hn1 : 1 ≤ n := by omega
  set μA := gaussMat (mA n) n (2 / (n : ℝ))
  have hT := mk_meas_Tf c₀ s hF
  set f : Matrix (Fin (mA n)) (Fin n) ℝ → ℝ≥0∞ :=
    fun A => ∫⁻ v, ENNReal.ofReal (|Tf c₀ s F A v| ^ 64) ∂stdGauss (Fin (n - 1)) with hf
  have hG : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      ENNReal.ofReal (|Tf c₀ s F p.1 p.2| ^ 64)) :=
    ENNReal.measurable_ofReal.comp (hT.abs.pow_const 64)
  have hfm : Measurable f := hG.lintegral_prod_right'
  have hsub : {A | K ^ 64 < ∫ v, |Tf c₀ s F A v| ^ 64 ∂stdGauss (Fin (n - 1))} ⊆
      {A | ENNReal.ofReal (K ^ 64) ≤ f A} := by
    intro A hA
    simp only [mem_setOf_eq] at hA ⊢
    have hi : Integrable (fun v => |Tf c₀ s F A v| ^ 64) (stdGauss (Fin (n - 1))) := by
      refine mo_bdd_pow (μ := stdGauss (Fin (n - 1)))
        ((hT.comp (measurable_const.prodMk measurable_id)).abs) (C := |1 - s ^ 2| *
          (tA n * (∑ i, ∑ l, A i l ^ 2) * 3)) (fun v => ?_) 64
      rw [abs_abs]; exact mk_bdd hn1 hc s F hB A v
    rw [hf]
    simp only
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun v => by positivity)]
    exact ENNReal.ofReal_le_ofReal hA.le
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_lintegral_div hfm.aemeasurable (by simp; positivity) ENNReal.ofReal_ne_top).trans ?_
  gcongr
  -- Tonelli and the frame moment
  rw [hf, lintegral_lintegral_swap hG.aemeasurable]
  have hnz : ∀ᵐ v ∂stdGauss (Fin (n - 1)), v ≠ 0 := by
    have h0 : stdGauss (Fin (n - 1)) {(0 : Fin (n - 1) → ℝ)} = 0 :=
      BstLean.Part168.stdGauss_zero (by omega)
    rw [ae_iff]; simpa using h0
  have h1s : 0 ≤ 1 - s ^ 2 := by linarith
  calc ∫⁻ v, ∫⁻ A, ENNReal.ofReal (|Tf c₀ s F A v| ^ 64) ∂μA ∂stdGauss (Fin (n - 1)) ≤
      ∫⁻ _v, ENNReal.ofReal (((1 - s ^ 2) * (425 / 100 / (n : ℝ) ^ 2)) ^ 64)
        ∂stdGauss (Fin (n - 1)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hnz] with v hv
        have e : ∀ A, ENNReal.ofReal (|Tf c₀ s F A v| ^ 64) = ENNReal.ofReal ((1 - s ^ 2) ^ 64) *
            ENNReal.ofReal (latSq (vecMul (F A v) (D1A1 A (xLat c₀ s (unitF53 v)))) (uHat c₀)
              (dirW c₀ (unitF53 v)) ^ 64) := by
          intro A
          have e1 : |Tf c₀ s F A v| ^ 64 = (1 - s ^ 2) ^ 64 * latSq (vecMul (F A v)
              (D1A1 A (xLat c₀ s (unitF53 v)))) (uHat c₀) (dirW c₀ (unitF53 v)) ^ 64 := by
            rw [Even.pow_abs ⟨32, by norm_num⟩]
            simp only [Tf]
            rw [mul_pow]
          rw [e1, ENNReal.ofReal_mul (pow_nonneg h1s 64)]
        simp_rw [e]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have hM := frame_mom_num hn hc hs hv (fun A => F A v) (hadm v) (fun A => hB A v)
        calc ENNReal.ofReal ((1 - s ^ 2) ^ 64) * ∫⁻ A, ENNReal.ofReal (latSq (vecMul (F A v)
              (D1A1 A (xLat c₀ s (unitF53 v)))) (uHat c₀) (dirW c₀ (unitF53 v)) ^ 64) ∂μA ≤
            ENNReal.ofReal ((1 - s ^ 2) ^ 64) * ENNReal.ofReal ((425 / 100 / (n : ℝ) ^ 2) ^ 64) :=
              by gcongr
          _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), mul_pow]
    _ = _ := by simp

end BstLean.Part172
