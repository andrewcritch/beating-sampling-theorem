import BstLean.Part144Block
import BstLean.Part144Moment
import BstLean.Part142Spread

/-!
# Part 144, item 1: the mean of `k` exact samples, given all but the last row of `F`

Role: `delegations/statements/p144-spec.md`, item 1 (`sampleMeanStruct144`) and the conditional
step of item 2. Paper source: round onW15c, §§2 and 7.

Notation: `W : MlpParam N mW n` (the World network), `A : MlpParam n mA n` (the Agent network),
`F = (F₁, F₂, F₃) : MlpParam n mF 1`; `z = zU W A F₁ F₂` is the last hidden vector of `F` at
`A(x(u))`, a function of the input `u`; `m = E_u z`, `C = Cov_u z` (`covMat`), `α = 2/m_F`.

* `uniK k N`: `k` independent uniform unit vectors `u_1, …, u_k` of `ℝ^N`.
* `gMean k W A F us`: the mean of the `k` exact samples `F(A(x(u_j)))`, `x(u) = xW W u`.
* `failSet k`: the event `|ĝ_k − B| > sd/2`, a set of `((W, A, F), (u_j)_j)`.
* `dVec k W A F₁ F₂ us`: `D_k = (1/k)·Σ_j (z(u_j) − m)`.
* **`sampleMeanStruct144`**: `ĝ_k − B = w·D_k`, `sd = √(wᵀCw)` (`w` the row of `F₃`), and
  `E_us |D_k|² = tr C/k`.
* `tauR = α·tr C`, `fR = α·‖C‖_F`, `xR = k·α·|D_k|²`.
* `fail_cond`: if `k·τ < t0²·(4X − k·f)`, then over `F₃` the event `|ĝ_k − B| > sd/2` has
  probability above `Φ̄(t0)`.
* `yR_second`: `E_us (Y − (4t0² − k)·c)² ≤ (32t0⁴ + (4t0² − k)² + t0⁴k²)·E_{u,u′}(kD − c)²` for
  `Y = t0²(4X − k·f) − k·τ`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part144

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139
  BstLean.Part142

variable {N mW n mA mF : ℕ}

/-! ## Definitions -/

/-- `k` independent uniform unit vectors of `ℝ^N`. -/
noncomputable def uniK (k N : ℕ) : Measure (Fin k → Fin N → ℝ) :=
  Measure.pi fun _ : Fin k => uniformSphere N

/-- **The mean of `k` exact samples** `F(A(x(u_j)))`, `x(u) = W(u)/|W(u)|` (`xW`, with the fixed
point `e0 n` at `W(u) = 0`, as in `muWn` and `Bn`). -/
noncomputable def gMean (k : ℕ) (W : MlpParam N mW n) (A : MlpParam n mA n)
    (F : MlpParam n mF 1) (us : Fin k → Fin N → ℝ) : ℝ :=
  (∑ j, phiN A F (xW W (us j))) / (k : ℝ)

/-- **The sample mean fails**: `|ĝ_k − B| > sd/2`, a set of `((W, A, F), (u_j)_j)`. -/
def failSet (k : ℕ) : Set ((MlpParam N mW n × MlpParam n mA n × MlpParam n mF 1) ×
    (Fin k → Fin N → ℝ)) :=
  {p | sdn p.1.1 p.1.2.1 p.1.2.2 / 2 <
    |gMean k p.1.1 p.1.2.1 p.1.2.2 p.2 - Bn p.1.1 p.1.2.1 p.1.2.2|}

/-- `D_k = (1/k)·Σ_j (z(u_j) − E_u z)`, `z` the last hidden vector of `F` at `A(x(u))`. -/
noncomputable def dVec (k : ℕ) (W : MlpParam N mW n) (A : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)
    (us : Fin k → Fin N → ℝ) : Fin mF → ℝ :=
  fun i => sumC (uniformSphere N) (zU W A F₁ F₂) k us i / (k : ℝ)

/-- `τ = α·tr C`: the mean of `sd²` over the last row of `F`. -/
noncomputable def tauR (W : MlpParam N mW n) (A : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ) : ℝ :=
  2 / (mF : ℝ) * trC (uniformSphere N) (zU W A F₁ F₂)

/-- `f = α·‖C‖_F` (Frobenius norm). -/
noncomputable def fR (W : MlpParam N mW n) (A : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ) : ℝ :=
  2 / (mF : ℝ) * √(frC (uniformSphere N) (zU W A F₁ F₂))

/-- `X = k·α·|D_k|² = (α/k)·|Σ_j (z(u_j) − m)|²`. -/
noncomputable def xR (k : ℕ) (W : MlpParam N mW n) (A : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)
    (us : Fin k → Fin N → ℝ) : ℝ :=
  2 / (mF : ℝ) / (k : ℝ) * sqS (uniformSphere N) (zU W A F₁ F₂) k us

/-- `Y = t0²·(4X − k·f) − k·τ`. The block bound applies where `Y > 0`. -/
noncomputable def yR (t0 : ℝ) (k : ℕ) (W : MlpParam N mW n) (A : MlpParam n mA n)
    (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)
    (us : Fin k → Fin N → ℝ) : ℝ :=
  t0 ^ 2 * (4 * xR k W A F₁ F₂ us - k * fR W A F₁ F₂) - k * tauR W A F₁ F₂

lemma uniK_prob (hN : 1 ≤ N) (k : ℕ) : IsProbabilityMeasure (uniK k N) := by
  have := uniformSphere_isProbability N hN
  unfold uniK; infer_instance

/-! ## A quadratic form and the Frobenius norm -/

/-- `yᵀCy ≤ ‖C‖_F·|y|²`. -/
lemma qform_le_frob {ι : Type} [Fintype ι] (C : Matrix ι ι ℝ) (y : ι → ℝ) :
    y ⬝ᵥ C *ᵥ y ≤ √(∑ i, ∑ j, C i j ^ 2) * (y ⬝ᵥ y) := by
  rw [qform_expand]
  have hyy : y ⬝ᵥ y = ∑ i, y i ^ 2 := by
    simp only [dotProduct]; exact Finset.sum_congr rfl fun i _ => (pow_two _).symm
  have hyy0 : 0 ≤ y ⬝ᵥ y := by rw [hyy]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have e1 : ∑ i, ∑ j, C i j * (y i * y j) =
      ∑ p : ι × ι, C p.1 p.2 * (y p.1 * y p.2) := (Fintype.sum_prod_type' _).symm
  have e2 : ∑ i, ∑ j, C i j ^ 2 = ∑ p : ι × ι, C p.1 p.2 ^ 2 :=
    (Fintype.sum_prod_type' (fun i j => C i j ^ 2)).symm
  have e3 : ∑ p : ι × ι, (y p.1 * y p.2) ^ 2 = (y ⬝ᵥ y) ^ 2 := by
    rw [Fintype.sum_prod_type' (fun a b => (y a * y b) ^ 2), hyy, pow_two, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
    (fun p => C p.1 p.2) (fun p => y p.1 * y p.2)
  rw [e3, ← e2] at hcs
  rw [e1]
  have h1 := Real.abs_le_sqrt hcs
  have hA0 : 0 ≤ ∑ i, ∑ j, C i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [Real.sqrt_mul hA0, Real.sqrt_sq hyy0] at h1
  exact (le_abs_self _).trans h1

/-! ## Item 1: the conditional structure -/

section fixed

variable (hn : 1 ≤ n) (hN : 1 ≤ N) (W : MlpParam N mW n) (A : MlpParam n mA n)
  (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)

lemma trace_covMat :
    (covMat W A F₁ F₂).trace = trC (uniformSphere N) (zU W A F₁ F₂) := by
  simp only [Matrix.trace, Matrix.diag, covMat_eq, trC]

lemma frob_covMat :
    ∑ i, ∑ j, covMat W A F₁ F₂ i j ^ 2 = frC (uniformSphere N) (zU W A F₁ F₂) := by
  simp only [covMat_eq, frC]

lemma dVec_sq (k : ℕ) (us : Fin k → Fin N → ℝ) :
    ∑ i, dVec k W A F₁ F₂ us i ^ 2 =
      sqS (uniformSphere N) (zU W A F₁ F₂) k us / (k : ℝ) ^ 2 := by
  simp only [dVec, sqS, div_pow]
  rw [Finset.sum_div]

include hn hN in
/-- **The error of the sample mean is a linear form in the last row of `F`**:
`ĝ_k − B = w·D_k`. -/
theorem gMean_sub {k : ℕ} (hk : 1 ≤ k) (F₃ : Matrix (Fin 1) (Fin mF) ℝ)
    (us : Fin k → Fin N → ℝ) :
    gMean k W A (F₁, F₂, F₃) us - Bn W A (F₁, F₂, F₃) =
      rowOf 0 F₃ ⬝ᵥ dVec k W A F₁ F₂ us := by
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [Bn_last hn hN]
  unfold gMean
  simp_rw [phiN_last]
  simp only [dotProduct, rowOf, dVec, sumC, ← aVec_eq, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_comm, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum]
  have e : ∑ j, hidF F₁ F₂ A (xW W (us j)) i = ∑ j, zU W A F₁ F₂ (us j) i := rfl
  rw [e]
  field_simp

include hn hN in
/-- **Item 1 (`sampleMeanStruct144`): the conditional structure of the mean of `k` exact
samples.** For fixed `W`, `A`, `F₁`, `F₂` and `k ≥ 1`, with `w` the one row of the last matrix
`F₃` of `F` (independent `N(0, 2/m_F)` entries, independent of everything else):
`ĝ_k − B = w·D_k` (a linear form in `w`), `sd = √(wᵀCw)` (a quadratic form in the same `w`), and
`E|D_k|² = tr C/k` over the `k` inputs. -/
theorem sampleMeanStruct144 {k : ℕ} (hk : 1 ≤ k) :
    (∀ (F₃ : Matrix (Fin 1) (Fin mF) ℝ) (us : Fin k → Fin N → ℝ),
      gMean k W A (F₁, F₂, F₃) us - Bn W A (F₁, F₂, F₃) =
        rowOf 0 F₃ ⬝ᵥ dVec k W A F₁ F₂ us) ∧
    (∀ F₃ : Matrix (Fin 1) (Fin mF) ℝ,
      sdn W A (F₁, F₂, F₃) = √(rowOf 0 F₃ ⬝ᵥ covMat W A F₁ F₂ *ᵥ rowOf 0 F₃)) ∧
    ∫ us, ∑ i, dVec k W A F₁ F₂ us i ^ 2 ∂uniK k N = (covMat W A F₁ F₂).trace / (k : ℝ) := by
  have := uniformSphere_isProbability N hN
  have := uniK_prob hN k
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine ⟨fun F₃ us => gMean_sub hn hN W A F₁ F₂ hk F₃ us, fun F₃ => sdn_last hn hN W A F₁ F₂ F₃,
    ?_⟩
  simp_rw [dVec_sq]
  rw [integral_div, uniK,
    sqS_mean (uniformSphere N) (zU W A F₁ F₂) (zU_meas W A F₁ F₂) (zU_bdd hn W A F₁ F₂) k,
    trace_covMat]
  field_simp

/-! ## The conditional step: the block bound for the sample mean -/

include hn hN in
/-- **The conditional failure of the sample mean.** Fix `W`, `A`, `F₁`, `F₂` and the inputs
`u_1, …, u_k`. If `k·τ < t0²·(4X − k·f)`, then over the last matrix `F₃` of `F` the event
`|ĝ_k − B| > sd/2` has probability above `Φ̄(t0) = γ(t0, ∞)`. -/
theorem fail_cond (hmF : 1 ≤ mF) {k : ℕ} (hk : 1 ≤ k) (us : Fin k → Fin N → ℝ) {t0 : ℝ}
    (ht0 : 0 < t0) (hY : 0 < yR t0 k W A F₁ F₂ us) :
    (gaussianReal 0 1).real (Ioi t0) < (gaussMat 1 mF (2 / (mF : ℝ))).real
      {F₃ | sdn W A (F₁, F₂, F₃) / 2 <
        |gMean k W A (F₁, F₂, F₃) us - Bn W A (F₁, F₂, F₃)|} := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hm : (0 : ℝ) < mF := by exact_mod_cast hmF
  set α : ℝ := 2 / (mF : ℝ) with hα
  have hα0 : 0 < α := by positivity
  set r : ℝ := √α with hr
  have hrr : r * r = α := Real.mul_self_sqrt hα0.le
  set C := covMat W A F₁ F₂ with hC
  set d := dVec k W A F₁ F₂ us with hd
  set fr : ℝ := frC (uniformSphere N) (zU W A F₁ F₂) with hfr
  let v : Fin mF → ℝ := r • d
  let M : Matrix (Fin mF) (Fin mF) ℝ := (α / 4) • C
  have hMq : ∀ y : Fin mF → ℝ, y ⬝ᵥ M *ᵥ y = α / 4 * (y ⬝ᵥ C *ᵥ y) := fun y =>
    BstLean.Part135.qform_smul _ _ _
  have hM : ∀ y : Fin mF → ℝ, 0 ≤ y ⬝ᵥ M *ᵥ y := by
    intro y
    rw [hMq]
    have h1 := covMat_nonneg hn hN W A F₁ F₂ y
    positivity
  have hop : ∀ y : Fin mF → ℝ, y ⬝ᵥ M *ᵥ y ≤ fR W A F₁ F₂ / 4 * (y ⬝ᵥ y) := by
    intro y
    rw [hMq]
    have h1 := qform_le_frob C y
    rw [hC, frob_covMat, ← hC, ← hfr] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ α / 4)
    refine h2.trans (le_of_eq ?_)
    simp only [fR, ← hα, ← hfr]
    ring
  have hfR4 : 0 ≤ fR W A F₁ F₂ / 4 := by
    unfold fR; positivity
  have hvv : v ⬝ᵥ v = xR k W A F₁ F₂ us / k := by
    have e1 : v ⬝ᵥ v = α * ∑ i, d i ^ 2 := by
      simp only [v, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← hrr]; ring
    rw [e1, hd, dVec_sq]
    simp only [xR, ← hα]
    field_simp
  have htr : M.trace = tauR W A F₁ F₂ / 4 := by
    simp only [M, trace_smul, smul_eq_mul, hC, trace_covMat, tauR, ← hα]
    ring
  have hv : M.trace < t0 ^ 2 * (v ⬝ᵥ v - fR W A F₁ F₂ / 4) := by
    rw [htr, hvv]
    have hY' : (k : ℝ) * tauR W A F₁ F₂ <
        t0 ^ 2 * (4 * xR k W A F₁ F₂ us - k * fR W A F₁ F₂) := by
      unfold yR at hY; linarith
    have e : t0 ^ 2 * (xR k W A F₁ F₂ us / k - fR W A F₁ F₂ / 4) =
        t0 ^ 2 * (4 * xR k W A F₁ F₂ us - k * fR W A F₁ F₂) / (4 * k) := by
      field_simp
    rw [e, lt_div_iff₀ (by positivity)]
    linarith
  have hblock := gauss_block_op v M hM hfR4 hop ht0 hv
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
  refine lt_of_lt_of_le hblock (measureReal_mono ?_)
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

/-! ## The second moment of `Y` over the inputs -/

include hn hN in
/-- `E_{u,u′}(kD − c)² ≥ (τ − c)² + α²·Var(|z − m|²)/2 + f²`. -/
lemma QD_ge (hmF : 1 ≤ mF) (A' : MlpParam n mA n) (F₃ : Matrix (Fin 1) (Fin mF) ℝ) (c : ℝ) :
    (tauR W A F₁ F₂ - c) ^ 2 +
        (2 / (mF : ℝ)) ^ 2 * radV (uniformSphere N) (zU W A F₁ F₂) / 2 +
        fR W A F₁ F₂ ^ 2 ≤
      QD c ((W, A, A', F₁, F₂, F₃) : Rest N mW n mA mF) := by
  have := uniformSphere_isProbability N hN
  have hm : (0 : ℝ) < mF := by exact_mod_cast hmF
  set α : ℝ := 2 / (mF : ℝ) with hα
  have hα0 : 0 < α := by positivity
  set z := zU W A F₁ F₂ with hz
  have hfr0 : 0 ≤ frC (uniformSphere N) z := by
    unfold frC
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have h := dist_decomp (uniformSphere N) z (zU_meas W A F₁ F₂) (zU_bdd hn W A F₁ F₂) (c / α)
  have h2 := mul_le_mul_of_nonneg_left h (sq_nonneg α)
  have eL : (tauR W A F₁ F₂ - c) ^ 2 + α ^ 2 * radV (uniformSphere N) z / 2 +
      fR W A F₁ F₂ ^ 2 =
      α ^ 2 * ((trC (uniformSphere N) z - c / α) ^ 2 + radV (uniformSphere N) z / 2 +
        frC (uniformSphere N) z) := by
    simp only [tauR, fR, ← hα, ← hz]
    rw [mul_pow, Real.sq_sqrt hfr0]
    field_simp
  rw [eL]
  refine h2.trans (le_of_eq ?_)
  unfold QD lawU2
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun uu => ?_)
  simp only
  rw [kD_zU]
  simp only [← hα, ← hz]
  field_simp

include hn hN in
/-- **The second moment of `Y` over the `k` inputs.** For fixed `(W, A, F₁, F₂)`, `k ≥ 1`
and constants `c`, `t0`: `Y` is bounded and measurable in the inputs and
`E_us (Y − (4t0² − k)·c)² ≤ (32t0⁴ + (4t0² − k)² + t0⁴k²)·E_{u,u′}(kD − c)²`. -/
theorem yR_second (hmF : 1 ≤ mF) {k : ℕ} (hk : 1 ≤ k) (A' : MlpParam n mA n)
    (F₃ : Matrix (Fin 1) (Fin mF) ℝ) (c t0 : ℝ) :
    BM (fun us => yR t0 k W A F₁ F₂ us) ∧
    ∫ us, (yR t0 k W A F₁ F₂ us - (4 * t0 ^ 2 - k) * c) ^ 2 ∂uniK k N ≤
      (32 * t0 ^ 4 + (4 * t0 ^ 2 - k) ^ 2 + t0 ^ 4 * (k : ℝ) ^ 2) *
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
  -- the centred variable
  set G : (Fin k → Fin N → ℝ) → ℝ := fun us => sqS (uniformSphere N) z k us - k * T with hG
  have hsB : BM (sqS (uniformSphere N) z k) := sqS_bm (uniformSphere N) z hzm hzb k
  have hGB : BM G := hsB.sub (BM.const _)
  have hG1 : ∫ us, G us ∂uniK k N = 0 := by
    rw [hG, integral_sub (hsB.integrable _) (integrable_const _), uniK,
      sqS_mean (uniformSphere N) z hzm hzb k]
    simp [hT]
  have hG2 : ∫ us, G us ^ 2 ∂uniK k N = k * Rv + 2 * k * (k - 1) * Φ := by
    rw [hG, uniK]; exact sqS_var (uniformSphere N) z hzm hzb k
  set a : ℝ := 4 * t0 ^ 2 * (α / k) with ha
  set b : ℝ := (4 * t0 ^ 2 - k) * (τ - c) - t0 ^ 2 * k * f with hb
  have hY : ∀ us, yR t0 k W A F₁ F₂ us - (4 * t0 ^ 2 - k) * c = a * G us + b := by
    intro us
    simp only [yR, xR, ← hα, ← hz, ← hτ, ← hf, hG, ha, hb, hτT]
    field_simp
    ring
  have hYB : BM (fun us => yR t0 k W A F₁ F₂ us) := by
    have h1 : BM (fun us => a * G us + b + (4 * t0 ^ 2 - k) * c) :=
      (((BM.const a).mul hGB).add (BM.const b)).add (BM.const _)
    have e : (fun us => yR t0 k W A F₁ F₂ us) =
        fun us => a * G us + b + (4 * t0 ^ 2 - k) * c := by
      funext us
      have := hY us
      linarith
    rw [e]; exact h1
  refine ⟨hYB, ?_⟩
  have hint : ∫ us, (yR t0 k W A F₁ F₂ us - (4 * t0 ^ 2 - k) * c) ^ 2 ∂uniK k N =
      a ^ 2 * (k * Rv + 2 * k * (k - 1) * Φ) + b ^ 2 := by
    have e : (fun us => (yR t0 k W A F₁ F₂ us - (4 * t0 ^ 2 - k) * c) ^ 2) =
        fun us => a ^ 2 * G us ^ 2 + 2 * a * b * G us + b ^ 2 := by
      funext us; rw [hY us]; ring
    have i1 : Integrable (fun us => a ^ 2 * G us ^ 2) (uniK k N) :=
      (hGB.sq.integrable _).const_mul _
    have i2 : Integrable (fun us => 2 * a * b * G us) (uniK k N) :=
      (hGB.integrable _).const_mul _
    have i12 : Integrable (fun us => a ^ 2 * G us ^ 2 + 2 * a * b * G us) (uniK k N) :=
      i1.add i2
    have e1 : ∫ us, (a ^ 2 * G us ^ 2 + 2 * a * b * G us + b ^ 2) ∂uniK k N =
        ∫ us, (a ^ 2 * G us ^ 2 + 2 * a * b * G us) ∂uniK k N + ∫ _us, b ^ 2 ∂uniK k N :=
      integral_add i12 (integrable_const _)
    have e2 : ∫ us, (a ^ 2 * G us ^ 2 + 2 * a * b * G us) ∂uniK k N =
        ∫ us, a ^ 2 * G us ^ 2 ∂uniK k N + ∫ us, 2 * a * b * G us ∂uniK k N :=
      integral_add i1 i2
    rw [e, e1, e2, integral_const_mul, integral_const_mul, hG1, hG2, integral_const]
    simp
  rw [hint]
  have hQ := QD_ge hn hN W A F₁ F₂ hmF A' F₃ c
  simp only [← hα, ← hz, ← hτ, ← hf, ← hRv] at hQ
  rw [hff] at hQ
  -- the two pieces
  have hb2 : b ^ 2 ≤ ((4 * t0 ^ 2 - k) ^ 2 + t0 ^ 4 * (k : ℝ) ^ 2) *
      ((τ - c) ^ 2 + α ^ 2 * Φ) := by
    have e : ((4 * t0 ^ 2 - k) ^ 2 + t0 ^ 4 * (k : ℝ) ^ 2) * ((τ - c) ^ 2 + f ^ 2) - b ^ 2 =
        ((4 * t0 ^ 2 - k) * f + t0 ^ 2 * k * (τ - c)) ^ 2 := by rw [hb]; ring
    have h0 := sq_nonneg ((4 * t0 ^ 2 - k) * f + t0 ^ 2 * k * (τ - c))
    rw [← hff]
    linarith
  have ht4 : 0 ≤ t0 ^ 4 := by positivity
  have ha2 : a ^ 2 * (k * Rv + 2 * k * (k - 1) * Φ) ≤
      32 * t0 ^ 4 * (α ^ 2 * Rv / 2 + α ^ 2 * Φ) := by
    have e : a ^ 2 * (k * Rv + 2 * k * (k - 1) * Φ) =
        16 * t0 ^ 4 * (α ^ 2 * Rv / k) + 32 * t0 ^ 4 * (α ^ 2 * Φ * ((k - 1) / k)) := by
      rw [ha]; field_simp; ring
    rw [e]
    have h1 : α ^ 2 * Rv / k ≤ α ^ 2 * Rv := div_le_self (by positivity) hkR
    have h2 : α ^ 2 * Φ * ((k - 1) / k) ≤ α ^ 2 * Φ := by
      refine mul_le_of_le_one_right (by positivity) ?_
      rw [div_le_one hk0]; linarith
    have h1' := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 16 * t0 ^ 4)
    have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 32 * t0 ^ 4)
    linarith
  have hK1 : 0 ≤ 32 * t0 ^ 4 := by positivity
  have hK2 : 0 ≤ (4 * t0 ^ 2 - k) ^ 2 + t0 ^ 4 * (k : ℝ) ^ 2 := by positivity
  have hx1 : 0 ≤ (τ - c) ^ 2 := sq_nonneg _
  have hx2 : 0 ≤ α ^ 2 * Rv / 2 := by positivity
  have hx3 : 0 ≤ α ^ 2 * Φ := by positivity
  set x1 := (τ - c) ^ 2 with hx1d
  set x2 := α ^ 2 * Rv / 2 with hx2d
  set x3 := α ^ 2 * Φ with hx3d
  set K1 := 32 * t0 ^ 4 with hK1d
  set K2 := (4 * t0 ^ 2 - k) ^ 2 + t0 ^ 4 * (k : ℝ) ^ 2 with hK2d
  set q := QD c ((W, A, A', F₁, F₂, F₃) : Rest N mW n mA mF) with hq
  have s1 : K1 * (x2 + x3) ≤ K1 * (x1 + x2 + x3) :=
    mul_le_mul_of_nonneg_left (by linarith) hK1
  have s2 : K2 * (x1 + x3) ≤ K2 * (x1 + x2 + x3) :=
    mul_le_mul_of_nonneg_left (by linarith) hK2
  have s3 : (K1 + K2) * (x1 + x2 + x3) ≤ (K1 + K2) * q :=
    mul_le_mul_of_nonneg_left hQ (by linarith)
  have e4 : (K1 + K2) * (x1 + x2 + x3) = K1 * (x1 + x2 + x3) + K2 * (x1 + x2 + x3) := by ring
  have e5 : (32 * t0 ^ 4 + (4 * t0 ^ 2 - k) ^ 2 + t0 ^ 4 * (k : ℝ) ^ 2) * q = (K1 + K2) * q := by
    rw [hK1d, hK2d]; ring
  rw [e5]
  linarith

end fixed

end BstLean.Part144

open BstLean.Part144 in
#print axioms sampleMeanStruct144
open BstLean.Part144 in
#print axioms fail_cond
open BstLean.Part144 in
#print axioms yR_second
