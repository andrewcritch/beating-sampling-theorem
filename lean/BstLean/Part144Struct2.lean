import BstLean.Part144Struct
import BstLean.Part144Block3
import BstLean.Part144Lip

/-!
# Part 144, the sharper conditional step: a polynomial lower bound of the conditional failure

Role: `delegations/statements/p144-spec.md`, item 2 with a larger `k_0`. New in this part (not
the paper's route of round onW15c §7): the Rayleigh quotient of the covariance along `D_k` in
the place of its operator norm, a global lower parabola in the place of an event, and a
Lipschitz step for the Rayleigh term.

Notation of `Part144Struct`: `α = 2/m_F`, `τ = α·tr C` (`tauR`), `f = α·‖C‖_F` (`fR`),
`X = k·α·|D_k|²` (`xR`). New: `w = α²·D_kᵀ C D_k` (`wR`).

* `wR_nonneg`, `wR_mean` (`E_us w = f²/k`), `xR_moments` (`E_us X = τ`,
  `E_us (X − c)² ≤ 2·E_{u,u′}(kD − c)²`).
* `fail_cond2`: for `X > 0` and `V = X − k²w/(4X) > 0`: over `F₃`,
  `Pr(|ĝ_k − B| > sd/2) ≥ 2(Φ̄(t0) + κ·t0²) − 2κ·(k/4)·τ/V`, `κ = φ(t0)/(2t0)` (the two-sided
  tangent form of the block bound, `gauss_block_tangent2` of `Part144Block3`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part144

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139
  BstLean.Part142

variable {N mW n mA mF : ℕ}

/-- `w = α²·D_kᵀ C D_k`, `D_k = S/k`. -/
noncomputable def wR (k : ℕ) (W : MlpParam N mW n) (A : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)
    (us : Fin k → Fin N → ℝ) : ℝ :=
  (2 / (mF : ℝ)) ^ 2 / (k : ℝ) ^ 2 *
    ∑ i, ∑ j, covV (uniformSphere N) (zU W A F₁ F₂) i j *
      (sumC (uniformSphere N) (zU W A F₁ F₂) k us i *
        sumC (uniformSphere N) (zU W A F₁ F₂) k us j)

section fixed

variable (hn : 1 ≤ n) (hN : 1 ≤ N) (W : MlpParam N mW n) (A : MlpParam n mA n)
  (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)

/-- The quadratic form of `C` at the centred sum. -/
lemma qform_sumC (k : ℕ) (us : Fin k → Fin N → ℝ) :
    ∑ i, ∑ j, covV (uniformSphere N) (zU W A F₁ F₂) i j *
      (sumC (uniformSphere N) (zU W A F₁ F₂) k us i *
        sumC (uniformSphere N) (zU W A F₁ F₂) k us j) =
      (sumC (uniformSphere N) (zU W A F₁ F₂) k us) ⬝ᵥ covMat W A F₁ F₂ *ᵥ
        (sumC (uniformSphere N) (zU W A F₁ F₂) k us) := by
  rw [qform_expand]
  simp only [covMat_eq]

include hn hN in
lemma wR_nonneg (k : ℕ) (us : Fin k → Fin N → ℝ) : 0 ≤ wR k W A F₁ F₂ us := by
  unfold wR
  rw [qform_sumC]
  have h := covMat_nonneg hn hN W A F₁ F₂ (sumC (uniformSphere N) (zU W A F₁ F₂) k us)
  positivity

lemma fR_nonneg : 0 ≤ fR W A F₁ F₂ := by unfold fR; positivity

lemma xR_nonneg (k : ℕ) (us : Fin k → Fin N → ℝ) : 0 ≤ xR k W A F₁ F₂ us := by
  unfold xR sqS
  have : 0 ≤ ∑ i, sumC (uniformSphere N) (zU W A F₁ F₂) k us i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  positivity

include hN in
lemma tauR_nonneg : 0 ≤ tauR W A F₁ F₂ := by
  have := uniformSphere_isProbability N hN
  unfold tauR trC
  have h : ∀ i, 0 ≤ covV (uniformSphere N) (zU W A F₁ F₂) i i := by
    intro i
    unfold covV
    exact integral_nonneg fun u => mul_self_nonneg _
  have : 0 ≤ ∑ i, covV (uniformSphere N) (zU W A F₁ F₂) i i :=
    Finset.sum_nonneg fun i _ => h i
  positivity

include hn hN in
/-- `E_us w = f²/k`. -/
lemma wR_mean {k : ℕ} (hk : 1 ≤ k) :
    BM (fun us => wR k W A F₁ F₂ us) ∧
    ∫ us, wR k W A F₁ F₂ us ∂uniK k N = fR W A F₁ F₂ ^ 2 / (k : ℝ) := by
  have := uniformSphere_isProbability N hN
  have hk0 : (0 : ℝ) < k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hzm := zU_meas W A F₁ F₂
  have hzb := zU_bdd hn W A F₁ F₂
  have hs := sumC_bm (uniformSphere N) (zU W A F₁ F₂) hzm hzb k
  have hB : BM (fun us : Fin k → Fin N → ℝ =>
      ∑ i, ∑ j, covV (uniformSphere N) (zU W A F₁ F₂) i j *
        (sumC (uniformSphere N) (zU W A F₁ F₂) k us i *
          sumC (uniformSphere N) (zU W A F₁ F₂) k us j)) :=
    BM.sum _ fun i _ => BM.sum _ fun j _ => (BM.const _).mul ((hs i).mul (hs j))
  refine ⟨(BM.const _).mul hB, ?_⟩
  unfold wR
  rw [integral_const_mul, uniK, quadS_mean (uniformSphere N) (zU W A F₁ F₂) hzm hzb k]
  have hfr0 : 0 ≤ frC (uniformSphere N) (zU W A F₁ F₂) := by
    unfold frC
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  unfold fR
  rw [mul_pow, Real.sq_sqrt hfr0]
  field_simp

include hn hN in
/-- `X` is bounded and measurable in the inputs, `E_us X = τ`, and
`E_us (X − c)² ≤ 2·E_{u,u′}(kD − c)²`. -/
lemma xR_moments (hmF : 1 ≤ mF) {k : ℕ} (hk : 1 ≤ k) (A' : MlpParam n mA n)
    (F₃ : Matrix (Fin 1) (Fin mF) ℝ) (c : ℝ) :
    BM (fun us => xR k W A F₁ F₂ us) ∧
    ∫ us, xR k W A F₁ F₂ us ∂uniK k N = tauR W A F₁ F₂ ∧
    ∫ us, (xR k W A F₁ F₂ us - c) ^ 2 ∂uniK k N ≤
      2 * QD c ((W, A, A', F₁, F₂, F₃) : Rest N mW n mA mF) ∧
    (tauR W A F₁ F₂ - c) ^ 2 + fR W A F₁ F₂ ^ 2 ≤
      QD c ((W, A, A', F₁, F₂, F₃) : Rest N mW n mA mF) := by
  have := uniformSphere_isProbability N hN
  have := uniK_prob hN k
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hm : (0 : ℝ) < mF := by exact_mod_cast hmF
  set α : ℝ := 2 / (mF : ℝ) with hα
  have hα0 : 0 < α := by positivity
  set z := zU W A F₁ F₂ with hz
  have hzm := zU_meas W A F₁ F₂
  have hzb := zU_bdd hn W A F₁ F₂
  set τ := tauR W A F₁ F₂ with hτ
  set f := fR W A F₁ F₂ with hf
  set T := trC (uniformSphere N) z with hT
  set Rv := radV (uniformSphere N) z with hRv
  set Φ := frC (uniformSphere N) z with hΦ
  have hΦ0 : 0 ≤ Φ := by
    rw [hΦ]; unfold frC
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hRv0 : 0 ≤ Rv := by rw [hRv]; unfold radV; exact integral_nonneg fun _ => sq_nonneg _
  have hff : f ^ 2 = α ^ 2 * Φ := by
    rw [hf]; simp only [fR, ← hα, ← hz, ← hΦ]
    rw [mul_pow, Real.sq_sqrt hΦ0]
  have hτT : τ = α * T := rfl
  set G : (Fin k → Fin N → ℝ) → ℝ := fun us => sqS (uniformSphere N) z k us - k * T with hG
  have hsB : BM (sqS (uniformSphere N) z k) := sqS_bm (uniformSphere N) z hzm hzb k
  have hGB : BM G := hsB.sub (BM.const _)
  have hG1 : ∫ us, G us ∂uniK k N = 0 := by
    rw [hG, integral_sub (hsB.integrable _) (integrable_const _), uniK,
      sqS_mean (uniformSphere N) z hzm hzb k]
    simp [hT]
  have hG2 : ∫ us, G us ^ 2 ∂uniK k N = k * Rv + 2 * k * (k - 1) * Φ := by
    rw [hG, uniK]; exact sqS_var (uniformSphere N) z hzm hzb k
  set a : ℝ := α / k with ha
  have hX : ∀ us, xR k W A F₁ F₂ us = a * G us + τ := by
    intro us
    simp only [xR, ← hα, ← hz, hG, ha, hτT]
    field_simp
    ring
  have hXB : BM (fun us => xR k W A F₁ F₂ us) := by
    have e : (fun us => xR k W A F₁ F₂ us) = fun us => a * G us + τ := funext hX
    rw [e]; exact ((BM.const a).mul hGB).add (BM.const τ)
  have hQ := QD_ge hn hN W A F₁ F₂ hmF A' F₃ c
  simp only [← hα, ← hz, ← hτ, ← hf, ← hRv] at hQ
  refine ⟨hXB, ?_, ?_, ?_⟩
  · have i1 : Integrable (fun us => a * G us) (uniK k N) := (hGB.integrable _).const_mul _
    have e1 : ∫ us, (a * G us + τ) ∂uniK k N =
        ∫ us, a * G us ∂uniK k N + ∫ _us, τ ∂uniK k N := integral_add i1 (integrable_const _)
    simp_rw [hX]
    rw [e1, integral_const_mul, hG1, integral_const]
    simp
  · have e : (fun us => (xR k W A F₁ F₂ us - c) ^ 2) =
        fun us => a ^ 2 * G us ^ 2 + 2 * a * (τ - c) * G us + (τ - c) ^ 2 := by
      funext us; rw [hX us]; ring
    have i1 : Integrable (fun us => a ^ 2 * G us ^ 2) (uniK k N) :=
      (hGB.sq.integrable _).const_mul _
    have i2 : Integrable (fun us => 2 * a * (τ - c) * G us) (uniK k N) :=
      (hGB.integrable _).const_mul _
    have i12 : Integrable (fun us => a ^ 2 * G us ^ 2 + 2 * a * (τ - c) * G us) (uniK k N) :=
      i1.add i2
    have e1 : ∫ us, (a ^ 2 * G us ^ 2 + 2 * a * (τ - c) * G us + (τ - c) ^ 2) ∂uniK k N =
        ∫ us, (a ^ 2 * G us ^ 2 + 2 * a * (τ - c) * G us) ∂uniK k N +
          ∫ _us, (τ - c) ^ 2 ∂uniK k N :=
      integral_add i12 (integrable_const _)
    have e2 : ∫ us, (a ^ 2 * G us ^ 2 + 2 * a * (τ - c) * G us) ∂uniK k N =
        ∫ us, a ^ 2 * G us ^ 2 ∂uniK k N + ∫ us, 2 * a * (τ - c) * G us ∂uniK k N :=
      integral_add i1 i2
    rw [e, e1, e2, integral_const_mul, integral_const_mul, hG1, hG2, integral_const]
    simp only [mul_zero, add_zero, probReal_univ, smul_eq_mul, one_mul]
    have e3 : a ^ 2 * (k * Rv + 2 * k * (k - 1) * Φ) =
        α ^ 2 * Rv / k + 2 * (α ^ 2 * Φ * ((k - 1) / k)) := by
      rw [ha]; field_simp
    rw [e3]
    have h1 : α ^ 2 * Rv / k ≤ α ^ 2 * Rv := div_le_self (by positivity) hkR
    have h2 : α ^ 2 * Φ * ((k - 1) / k) ≤ α ^ 2 * Φ := by
      refine mul_le_of_le_one_right (by positivity) ?_
      rw [div_le_one hk0]; linarith
    rw [hff] at hQ
    have hx1 : 0 ≤ (τ - c) ^ 2 := sq_nonneg _
    linarith
  · have hx2 : 0 ≤ α ^ 2 * Rv / 2 := by positivity
    linarith

/-! ## The tangent form of the conditional step -/

include hn hN in
/-- **The conditional failure of the sample mean, two-sided tangent form.** Fix `W`, `A`, `F₁`,
`F₂` and the inputs. If `X > 0`, `V = X − k²w/(4X) > 0` and `2(Φ̄(t0) + κ·t0²) ≤ Φ̄(1)`, then
over the last matrix `F₃` of `F`:
`Pr(|ĝ_k − B| > sd/2) ≥ 2(Φ̄(t0) + κ·t0²) − 2κ·(k/4)·τ/V`, `κ = φ(t0)/(2t0)`. -/
theorem fail_cond2 (hmF : 1 ≤ mF) {k : ℕ} (hk : 1 ≤ k) (us : Fin k → Fin N → ℝ) {t0 : ℝ}
    (ht0 : 0 < t0)
    (hA1 : 2 * ((gaussianReal 0 1).real (Ioi t0) + gaussianPDFReal 0 1 t0 / (2 * t0) * t0 ^ 2) ≤
      (gaussianReal 0 1).real (Ioi 1))
    (hX : 0 < xR k W A F₁ F₂ us)
    (hV : 0 < xR k W A F₁ F₂ us -
      (k : ℝ) ^ 2 * wR k W A F₁ F₂ us / (4 * xR k W A F₁ F₂ us)) :
    2 * ((gaussianReal 0 1).real (Ioi t0) + gaussianPDFReal 0 1 t0 / (2 * t0) * t0 ^ 2) -
        2 * (gaussianPDFReal 0 1 t0 / (2 * t0) * ((k : ℝ) / 4)) * tauR W A F₁ F₂ /
          (xR k W A F₁ F₂ us - (k : ℝ) ^ 2 * wR k W A F₁ F₂ us / (4 * xR k W A F₁ F₂ us)) ≤
      (gaussMat 1 mF (2 / (mF : ℝ))).real
        {F₃ | sdn W A (F₁, F₂, F₃) / 2 <
          |gMean k W A (F₁, F₂, F₃) us - Bn W A (F₁, F₂, F₃)|} := by
  have := uniformSphere_isProbability N hN
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hm : (0 : ℝ) < mF := by exact_mod_cast hmF
  set α : ℝ := 2 / (mF : ℝ) with hα
  have hα0 : 0 < α := by positivity
  set r : ℝ := √α with hr
  have hrr : r * r = α := Real.mul_self_sqrt hα0.le
  set C := covMat W A F₁ F₂ with hC
  set d := dVec k W A F₁ F₂ us with hd
  set X := xR k W A F₁ F₂ us with hXd
  set w := wR k W A F₁ F₂ us with hwd
  set τ := tauR W A F₁ F₂ with hτ
  set V := X - (k : ℝ) ^ 2 * w / (4 * X) with hVd
  have hw0 : 0 ≤ w := wR_nonneg hn hN W A F₁ F₂ k us
  have hτ0 : 0 ≤ τ := tauR_nonneg hN W A F₁ F₂
  let v : Fin mF → ℝ := r • d
  let M : Matrix (Fin mF) (Fin mF) ℝ := (α / 4) • C
  have hMq : ∀ y : Fin mF → ℝ, y ⬝ᵥ M *ᵥ y = α / 4 * (y ⬝ᵥ C *ᵥ y) := fun y =>
    BstLean.Part135.qform_smul _ _ _
  have hM : ∀ y : Fin mF → ℝ, 0 ≤ y ⬝ᵥ M *ᵥ y := by
    intro y
    rw [hMq]
    have h1 := covMat_nonneg hn hN W A F₁ F₂ y
    positivity
  have hvv : v ⬝ᵥ v = X / k := by
    have e1 : v ⬝ᵥ v = α * ∑ i, d i ^ 2 := by
      simp only [v, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← hrr]; ring
    rw [e1, hd, dVec_sq, hXd]
    simp only [xR, ← hα]
    field_simp
  have htr : M.trace = τ / 4 := by
    simp only [M, trace_smul, smul_eq_mul, hC, trace_covMat, hτ, tauR, ← hα]
    ring
  have hvMv : v ⬝ᵥ M *ᵥ v = w / 4 := by
    rw [hMq]
    have e1 : v ⬝ᵥ C *ᵥ v = α * (d ⬝ᵥ C *ᵥ d) := by
      simp only [v, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [← mul_assoc, hrr]
    have e2 : d ⬝ᵥ C *ᵥ d =
        (sumC (uniformSphere N) (zU W A F₁ F₂) k us) ⬝ᵥ C *ᵥ
          (sumC (uniformSphere N) (zU W A F₁ F₂) k us) / (k : ℝ) ^ 2 := by
      have hdS : d = (1 / (k : ℝ)) • sumC (uniformSphere N) (zU W A F₁ F₂) k us := by
        funext i
        simp only [hd, dVec, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hdS]
      simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      field_simp
    rw [e1, e2, hwd, wR, qform_sumC, ← hα, ← hC]
    ring
  have hD : 0 < v ⬝ᵥ v := by rw [hvv]; positivity
  have hVk : v ⬝ᵥ v - v ⬝ᵥ M *ᵥ v / (v ⬝ᵥ v) = V / k := by
    rw [hvv, hvMv, hVd]
    field_simp
  have hδ : v ⬝ᵥ M *ᵥ v / (v ⬝ᵥ v) < v ⬝ᵥ v := by
    have : 0 < V / k := by positivity
    rw [← hVk] at this
    linarith
  have hblock := gauss_block_tangent2 v M hM ht0 hD hδ hA1
  rw [hVk, htr] at hblock
  set κ : ℝ := gaussianPDFReal 0 1 t0 / (2 * t0) with hκ
  have hκ0 : 0 ≤ κ := by
    have : 0 ≤ gaussianPDFReal 0 1 t0 := gaussianPDFReal_nonneg _ _ _
    positivity
  have ha0 : 0 ≤ v ⬝ᵥ M *ᵥ v / (v ⬝ᵥ v) := div_nonneg (hM v) hD.le
  -- `z ≤ k τ / (4 V)`
  have hz : (τ / 4 - v ⬝ᵥ M *ᵥ v / (v ⬝ᵥ v)) / (V / k) ≤ (k : ℝ) / 4 * τ / V := by
    have e : (k : ℝ) / 4 * τ / V = (τ / 4) / (V / k) := by field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hlow : 2 * ((gaussianReal 0 1).real (Ioi t0) + κ * t0 ^ 2) -
      2 * (κ * ((k : ℝ) / 4)) * τ / V ≤
      (stdGauss (Fin mF)).real {g | g ⬝ᵥ M *ᵥ g < (g ⬝ᵥ v) ^ 2} := by
    refine le_trans ?_ hblock
    have h1 := mul_le_mul_of_nonneg_left hz hκ0
    have e : 2 * (κ * ((k : ℝ) / 4)) * τ / V = 2 * (κ * ((k : ℝ) / 4 * τ / V)) := by ring
    rw [e]
    linarith
  -- the event in terms of the row
  let S' : Set (Fin mF → ℝ) := {w | √(w ⬝ᵥ C *ᵥ w) / 2 < |w ⬝ᵥ d|}
  have hS' : MeasurableSet S' := by
    have h1 : Continuous fun w : Fin mF → ℝ => √(w ⬝ᵥ C *ᵥ w) / 2 := by fun_prop
    have h2 : Continuous fun w : Fin mF → ℝ => |w ⬝ᵥ d| := by fun_prop
    exact measurableSet_lt h1.measurable h2.measurable
  have hset : {F₃ : Matrix (Fin 1) (Fin mF) ℝ | sdn W A (F₁, F₂, F₃) / 2 <
      |gMean k W A (F₁, F₂, F₃) us - Bn W A (F₁, F₂, F₃)|} = rowOf 0 ⁻¹' S' := by
    ext F₃
    simp only [S', mem_preimage, mem_ofPred_eq, sdn_last hn hN, gMean_sub hn hN W A F₁ F₂ hk,
      ← hC, ← hd]
  rw [hset, ← map_measureReal_apply (measurable_rowOf 0) hS', gaussMat_row,
    map_measureReal_apply (measurable_const_smul _) hS']
  refine hlow.trans (measureReal_mono ?_)
  intro ξ hξ
  have hξ' : ξ ⬝ᵥ M *ᵥ ξ < (ξ ⬝ᵥ v) ^ 2 := hξ
  rw [hMq] at hξ'
  change √((r • ξ) ⬝ᵥ C *ᵥ (r • ξ)) / 2 < |(r • ξ) ⬝ᵥ d|
  have q1 : (r • ξ) ⬝ᵥ C *ᵥ (r • ξ) = α * (ξ ⬝ᵥ C *ᵥ ξ) := by
    simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← mul_assoc, hrr]
  have q3 : (r • ξ) ⬝ᵥ d = ξ ⬝ᵥ v := by
    simp only [v, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [q1, q3]
  have n1 : 0 ≤ α * (ξ ⬝ᵥ C *ᵥ ξ) := mul_nonneg hα0.le (covMat_nonneg hn hN W A F₁ F₂ ξ)
  have h5 : (√(α * (ξ ⬝ᵥ C *ᵥ ξ)) / 2) ^ 2 < (ξ ⬝ᵥ v) ^ 2 := by
    rw [div_pow, Real.sq_sqrt n1]
    linarith
  have h6 := sq_lt_sq.mp h5
  rwa [abs_of_nonneg (by positivity)] at h6

end fixed

end BstLean.Part144

open BstLean.Part144 in
#print axioms fail_cond2
