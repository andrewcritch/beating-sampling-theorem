import BstLean.Part152Op
import BstLean.Part152GC
import BstLean.Part130Sym
import BstLean.Part112Chaos

/-!
# Part 153, item 3: the operator-norm event of `A₁` and its consequences (Lemma L1 (a))

Role: `delegations/statements/p153-spec.md`, item 3. Paper source:
`proofs/option-n/theorem5-06-centre.tex`, Lemma L1 (a).

Notation. `n` is the dimension, `m_A = mA n = n²`, `t_A = 2/m_A`, `γ_A = 2/n`. `A₁` is an
`m × n` matrix. The stand-in input is `y = c + τ·ξ`, `ξ` a standard Gaussian vector of `ℝⁿ`
(`c = ĉ` and `τ = τ₀` are the two outputs of the pass over `W`; here they are arbitrary).
`h₁(y) = ReLU(A₁y)`. `opN` is the operator norm of Part 152.

* `nrm v = √(normSq v)`: the Euclidean length.
* `wn n = (1 + 2/√n)²`.
* `Eop n = {A₁ | opN A₁ ≤ √(2/n)·(n + 2√n)}`: **the event `E_op`**.
* **`Eop_prob`**: `Pr(A₁ ∉ E_op) ≤ exp(−n/2)` for `A₁ ∼ gaussMat (n²) n (2/n)`, `n ≥ 1`.
* `Eop_sq`: on `E_op`: `t_A·opN(A₁)² ≤ 4w_n/n`.
* **`covH_le`**: for every `A₁` and every vector `w`:
  `Var_ξ ⟨w, h₁(y)⟩ ≤ τ²·opN(A₁)²·|w|²` (so `‖H‖_op ≤ ℓ² = τ²·t_A·opN(A₁)²`).
* **`covH_le_Eop`**: on `E_op`: `t_A·Var_ξ ⟨w, h₁(y)⟩ ≤ (4w_nτ²/n)·|w|²`.
* `GamS A₁ c τ = t·E_ξ|h₁(y)|²` (`t = 2/m`): the energy `Γ` of the document;
  `GamS_le`: `Γ ≤ t·opN(A₁)²·ρ²`, `ρ² = |c|² + nτ²`; `GamS_le_Eop`: `Γ ≤ 4w_nρ²/n` on `E_op`.
* `fro_le`: `‖A₁‖_F² ≤ n·opN(A₁)²`; `fro_le_Eop`: `t_A‖A₁‖_F² ≤ 4w_n` on `E_op`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part148 (EuLip)
open BstLean.Part130
open BstLean.Part152

/-! ## Vectors -/

section vec

variable {ι : Type*} [Fintype ι]

/-- The Euclidean length. -/
noncomputable def nrm (v : ι → ℝ) : ℝ := √(normSq v)

lemma nrm_nonneg (v : ι → ℝ) : 0 ≤ nrm v := Real.sqrt_nonneg _

lemma nrm_sq (v : ι → ℝ) : nrm v ^ 2 = normSq v := Real.sq_sqrt (normSq_nonneg v)

lemma relu_sub_sq (a b : ℝ) : (relu a - relu b) ^ 2 ≤ (a - b) ^ 2 := by
  unfold relu
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb <;>
    simp only [max_eq_right, max_eq_left, ha, hb] <;> nlinarith

lemma normSq_reluV_sub_le (u v : ι → ℝ) : normSq (reluV u - reluV v) ≤ normSq (u - v) := by
  unfold normSq reluV
  exact Finset.sum_le_sum fun i _ => by simpa using relu_sub_sq (u i) (v i)

lemma normSq_reluV_le (u : ι → ℝ) : normSq (reluV u) ≤ normSq u := by
  unfold normSq reluV
  refine Finset.sum_le_sum fun i _ => ?_
  have := relu_sub_sq (u i) 0
  simpa [relu] using this

lemma nrm_reluV_sub_le (u v : ι → ℝ) : nrm (reluV u - reluV v) ≤ nrm (u - v) :=
  Real.sqrt_le_sqrt (normSq_reluV_sub_le u v)

lemma nrm_reluV_le (u : ι → ℝ) : nrm (reluV u) ≤ nrm u := Real.sqrt_le_sqrt (normSq_reluV_le u)

/-- Cauchy–Schwarz. -/
lemma abs_dot_le_nrm (u v : ι → ℝ) : |u ⬝ᵥ v| ≤ nrm u * nrm v := by
  unfold nrm
  rw [← Real.sqrt_mul (normSq_nonneg u), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

/-- The triangle inequality for the Euclidean length. -/
lemma nrm_add_le (u v : ι → ℝ) : nrm (u + v) ≤ nrm u + nrm v := by
  have h0 : 0 ≤ nrm u + nrm v := add_nonneg (nrm_nonneg u) (nrm_nonneg v)
  unfold nrm at *
  rw [← Real.sqrt_sq h0]
  refine Real.sqrt_le_sqrt ?_
  have h1 : normSq (u + v) = normSq u + 2 * (u ⬝ᵥ v) + normSq v := by
    unfold normSq dotProduct
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring
  have h2 := (abs_le.mp (abs_dot_le_nrm u v)).2
  unfold nrm at h2
  rw [h1, add_sq, Real.sq_sqrt (normSq_nonneg u), Real.sq_sqrt (normSq_nonneg v)]
  linarith

/-- The reverse triangle inequality for the Euclidean length. -/
lemma abs_nrm_sub_le (u v : ι → ℝ) : |nrm u - nrm v| ≤ nrm (u - v) := by
  have h1 := nrm_add_le (u - v) v
  have h2 := nrm_add_le (v - u) u
  have e : nrm (v - u) = nrm (u - v) := by
    unfold nrm normSq
    congr 1
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
  rw [sub_add_cancel] at h1 h2
  rw [e] at h2
  rw [abs_le]
  constructor <;> linarith

lemma nrm_smul (a : ℝ) (v : ι → ℝ) : nrm (a • v) = |a| * nrm v := by
  unfold nrm
  rw [normSq_smul, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

end vec

/-! ## The operator norm in the notation `nrm` -/

section op

variable {m n : ℕ}

/-- `|M v| ≤ opN M·|v|`. -/
lemma nrm_mulVec_le (M : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) :
    nrm (M *ᵥ v) ≤ opN M * nrm v := mulVec_le_opN M v

lemma normSq_mulVec_le (M : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) :
    normSq (M *ᵥ v) ≤ opN M ^ 2 * normSq v := by
  have h := nrm_mulVec_le M v
  have h0 := nrm_nonneg (M *ᵥ v)
  calc normSq (M *ᵥ v) = nrm (M *ᵥ v) ^ 2 := (nrm_sq _).symm
    _ ≤ (opN M * nrm v) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = opN M ^ 2 * normSq v := by rw [mul_pow, nrm_sq]

/-- `‖M‖_F² ≤ n·opN(M)²` (the rank is at most the number of columns). -/
theorem fro_le (M : Matrix (Fin m) (Fin n) ℝ) :
    ∑ i, ∑ j, M i j ^ 2 ≤ (n : ℝ) * opN M ^ 2 := by
  classical
  rw [Finset.sum_comm]
  have h : ∀ j : Fin n, ∑ i, M i j ^ 2 ≤ opN M ^ 2 := by
    intro j
    have h1 := normSq_mulVec_le M (Pi.single j 1)
    have e1 : normSq (M *ᵥ (Pi.single j 1 : Fin n → ℝ)) = ∑ i, M i j ^ 2 := by
      unfold normSq
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have e2 : normSq (Pi.single j 1 : Fin n → ℝ) = 1 := by
      unfold normSq
      simp [Pi.single_apply]
    rw [e1, e2, mul_one] at h1
    exact h1
  calc ∑ j, ∑ i, M i j ^ 2 ≤ ∑ _j : Fin n, opN M ^ 2 := Finset.sum_le_sum fun j _ => h j
    _ = (n : ℝ) * opN M ^ 2 := by simp

end op

/-! ## The event `E_op` -/

/-- `w_n = (1 + 2/√n)²`. -/
noncomputable def wn (n : ℕ) : ℝ := (1 + 2 / √(n : ℝ)) ^ 2

/-- **The event `E_op`**: `‖A₁‖_op ≤ √(γ_A)·(n + 2√n)`, `γ_A = 2/n`. -/
def Eop (n : ℕ) : Set (Matrix (Fin (mA n)) (Fin n) ℝ) :=
  {M | opN M ≤ √(2 / (n : ℝ)) * ((n : ℝ) + 2 * √(n : ℝ))}

lemma sqrt_mA (n : ℕ) : √((mA n : ℕ) : ℝ) = (n : ℝ) := by
  unfold mA
  push_cast
  exact Real.sqrt_sq (Nat.cast_nonneg n)

/-- **The charge of `E_op`** (Lemma L1 (a)): `Pr(A₁ ∉ E_op) ≤ exp(−n/2)`, `A₁` a Gaussian
`n² × n` matrix with entry variance `2/n`. -/
theorem Eop_prob {n : ℕ} (hn : 1 ≤ n) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real (Eop n)ᶜ ≤ Real.exp (-(n : ℝ) / 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := opN_tail' (p := mA n) (q := n) (v := 2 / (n : ℝ)) (by positivity)
    (u := √(n : ℝ)) (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt hn0.le, sqrt_mA] at h
  refine le_trans (measureReal_mono (fun M hM => ?_)) h
  simp only [Eop, mem_compl_iff, mem_ofPred_eq, not_le] at hM ⊢
  have e : (n : ℝ) + √(n : ℝ) + √(n : ℝ) = (n : ℝ) + 2 * √(n : ℝ) := by ring
  rw [e]
  exact hM.le

/-- On `E_op`: `t_A·‖A₁‖_op² ≤ 4w_n/n`. -/
theorem Eop_sq {n : ℕ} (hn : 1 ≤ n) {M : Matrix (Fin (mA n)) (Fin n) ℝ} (hM : M ∈ Eop n) :
    2 / ((mA n : ℕ) : ℝ) * opN M ^ 2 ≤ 4 * wn n / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
  have h1 : opN M ^ 2 ≤ (√(2 / (n : ℝ)) * ((n : ℝ) + 2 * √(n : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (opN_nonneg M) hM 2
  rw [mul_pow, Real.sq_sqrt (by positivity)] at h1
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  rw [hm]
  have h2 : 2 / (n : ℝ) ^ 2 * opN M ^ 2 ≤
      2 / (n : ℝ) ^ 2 * (2 / (n : ℝ) * ((n : ℝ) + 2 * √(n : ℝ)) ^ 2) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  refine h2.trans (le_of_eq ?_)
  unfold wn
  have e : (1 + 2 / √(n : ℝ)) = ((n : ℝ) + 2 * √(n : ℝ)) / n := by
    field_simp
    nlinarith [hss]
  rw [e]
  field_simp
  norm_num

/-! ## The covariance of the first hidden layer over the stand-in input -/

section cov

variable {m n : ℕ}

/-- `ξ ↦ ⟨w, ReLU(A₁(c + τξ))⟩` is Lipschitz with constant `|τ|·opN(A₁)·|w|`. -/
lemma h1_dot_lip (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) (w : Fin m → ℝ) :
    EuLip (fun ξ : Fin n → ℝ => w ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ))) (|τ| * opN A₁ * nrm w) := by
  intro ξ ξ'
  have e1 : w ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ)) - w ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ')) =
      w ⬝ᵥ (reluV (A₁ *ᵥ (c + τ • ξ)) - reluV (A₁ *ᵥ (c + τ • ξ'))) := by
    rw [dotProduct_sub]
  have e2 : A₁ *ᵥ (c + τ • ξ) - A₁ *ᵥ (c + τ • ξ') = A₁ *ᵥ (τ • (ξ - ξ')) := by
    rw [← Matrix.mulVec_sub]
    congr 1
    rw [smul_sub]
    abel
  have e3 : √(∑ i, (ξ i - ξ' i) ^ 2) = nrm (ξ - ξ') := rfl
  rw [e1, e3]
  calc |w ⬝ᵥ (reluV (A₁ *ᵥ (c + τ • ξ)) - reluV (A₁ *ᵥ (c + τ • ξ')))|
      ≤ nrm w * nrm (reluV (A₁ *ᵥ (c + τ • ξ)) - reluV (A₁ *ᵥ (c + τ • ξ'))) :=
        abs_dot_le_nrm _ _
    _ ≤ nrm w * nrm (A₁ *ᵥ (c + τ • ξ) - A₁ *ᵥ (c + τ • ξ')) :=
        mul_le_mul_of_nonneg_left (nrm_reluV_sub_le _ _) (nrm_nonneg w)
    _ = nrm w * nrm (A₁ *ᵥ (τ • (ξ - ξ'))) := by rw [e2]
    _ ≤ nrm w * (opN A₁ * nrm (τ • (ξ - ξ'))) :=
        mul_le_mul_of_nonneg_left (nrm_mulVec_le _ _) (nrm_nonneg w)
    _ = |τ| * opN A₁ * nrm w * nrm (ξ - ξ') := by rw [nrm_smul]; ring

/-- **Lemma L1 (a), the covariance of the first hidden layer.** For every matrix `A₁`, every
`c`, `τ` and every vector `w`: `Var_ξ ⟨w, ReLU(A₁y)⟩ ≤ τ²·opN(A₁)²·|w|²`, `y = c + τξ`.
With `t_A` in front and `|w| = 1` this is `‖H‖_op ≤ ℓ²`, `ℓ² = τ²·t_A·opN(A₁)²`. -/
theorem covH_le (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) (w : Fin m → ℝ) :
    Integrable (fun ξ : Fin n → ℝ => (w ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ)) -
      ∫ ξ', w ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2) (stdGauss (Fin n)) ∧
    ∫ ξ, (w ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ)) -
      ∫ ξ', w ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
      τ ^ 2 * opN A₁ ^ 2 * normSq w := by
  have hL0 : 0 ≤ |τ| * opN A₁ * nrm w :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (opN_nonneg _)) (nrm_nonneg _)
  obtain ⟨hi, hv⟩ := gaussVar_le_sharp hL0 (h1_dot_lip A₁ c τ w)
  refine ⟨hi, hv.trans (le_of_eq ?_)⟩
  rw [mul_pow, mul_pow, sq_abs, nrm_sq]

/-- **Lemma L1 (a) on `E_op`**: `t_A·Var_ξ ⟨w, ReLU(A₁y)⟩ ≤ (4w_nτ²/n)·|w|²`. -/
theorem covH_le_Eop {n : ℕ} (hn : 1 ≤ n) {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} (hA : A₁ ∈ Eop n)
    (c : Fin n → ℝ) (τ : ℝ) (w : Fin (mA n) → ℝ) :
    2 / ((mA n : ℕ) : ℝ) * ∫ ξ, (w ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ)) -
      ∫ ξ', w ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
      4 * wn n * τ ^ 2 / n * normSq w := by
  have h1 := (covH_le A₁ c τ w).2
  have h2 := Eop_sq hn hA
  have hm : (0 : ℝ) ≤ 2 / ((mA n : ℕ) : ℝ) := by positivity
  calc 2 / ((mA n : ℕ) : ℝ) * ∫ ξ, (w ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ)) -
        ∫ ξ', w ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n)
      ≤ 2 / ((mA n : ℕ) : ℝ) * (τ ^ 2 * opN A₁ ^ 2 * normSq w) :=
        mul_le_mul_of_nonneg_left h1 hm
    _ = (2 / ((mA n : ℕ) : ℝ) * opN A₁ ^ 2) * (τ ^ 2 * normSq w) := by ring
    _ ≤ (4 * wn n / n) * (τ ^ 2 * normSq w) :=
        mul_le_mul_of_nonneg_right h2 (mul_nonneg (sq_nonneg _) (normSq_nonneg _))
    _ = 4 * wn n * τ ^ 2 / n * normSq w := by ring

/-! ## The energy `Γ` -/

/-- `E_ξ|c + τξ|² = |c|² + nτ²` (`= ρ²`). -/
theorem int_normSq_shift (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (fun ξ : Fin n → ℝ => normSq (c + τ • ξ)) (stdGauss (Fin n)) ∧
    ∫ ξ, normSq (c + τ • ξ) ∂stdGauss (Fin n) = normSq c + (n : ℝ) * τ ^ 2 := by
  classical
  have e : ∀ ξ : Fin n → ℝ, normSq (c + τ • ξ) =
      ∑ i, (c i ^ 2 + 2 * c i * τ * ξ i + τ ^ 2 * (ξ i * ξ i)) := by
    intro ξ
    unfold normSq
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hi : ∀ i : Fin n, Integrable (fun ξ : Fin n → ℝ =>
      c i ^ 2 + 2 * c i * τ * ξ i + τ ^ 2 * (ξ i * ξ i)) (stdGauss (Fin n)) := fun i =>
    ((integrable_const _).add ((BstLean.Part112.int_coord i).const_mul _)).add
      ((stdGauss_mul_integrable i i).const_mul _)
  simp_rw [e]
  refine ⟨integrable_finsetSum _ fun i _ => hi i, ?_⟩
  rw [integral_finsetSum _ fun i _ => hi i]
  have h1 : ∀ i : Fin n, ∫ ξ : Fin n → ℝ, (c i ^ 2 + 2 * c i * τ * ξ i + τ ^ 2 * (ξ i * ξ i))
      ∂stdGauss (Fin n) = c i ^ 2 + τ ^ 2 := by
    intro i
    have ia : Integrable (fun ξ : Fin n → ℝ => c i ^ 2 + 2 * c i * τ * ξ i) (stdGauss (Fin n)) :=
      (integrable_const _).add ((BstLean.Part112.int_coord i).const_mul _)
    have ib : Integrable (fun ξ : Fin n → ℝ => τ ^ 2 * (ξ i * ξ i)) (stdGauss (Fin n)) :=
      (stdGauss_mul_integrable i i).const_mul _
    have ic : Integrable (fun ξ : Fin n → ℝ => 2 * c i * τ * ξ i) (stdGauss (Fin n)) :=
      (BstLean.Part112.int_coord i).const_mul _
    have e1 := integral_add ia ib
    have e2 := integral_add (integrable_const (c i ^ 2)) ic
    rw [e1, e2, integral_const_mul, integral_const_mul, BstLean.Part112.integral_coord,
      stdGauss_cov]
    simp
  simp_rw [h1]
  rw [Finset.sum_add_distrib]
  unfold normSq
  simp

/-- **The energy** `Γ = t·E_ξ|ReLU(A₁y)|²`, `t = 2/m`, `y = c + τξ`. -/
noncomputable def GamS (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  2 / (m : ℝ) * ∫ ξ, normSq (reluV (A₁ *ᵥ (c + τ • ξ))) ∂stdGauss (Fin n)

lemma continuous_h1 (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Continuous (fun ξ : Fin n → ℝ => reluV (A₁ *ᵥ (c + τ • ξ))) :=
  continuous_reluV.comp (Continuous.matrix_mulVec continuous_const
    (continuous_const.add (continuous_const_smul τ)))

lemma integrable_h1_sq (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (fun ξ : Fin n → ℝ => normSq (reluV (A₁ *ᵥ (c + τ • ξ)))) (stdGauss (Fin n)) := by
  refine Integrable.mono' ((int_normSq_shift c τ).1.const_mul (opN A₁ ^ 2))
    (continuous_normSq.comp (continuous_h1 A₁ c τ)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (normSq_nonneg _)]
  exact (normSq_reluV_le _).trans (normSq_mulVec_le _ _)

lemma GamS_nonneg (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) : 0 ≤ GamS A₁ c τ :=
  mul_nonneg (by positivity) (integral_nonneg fun _ => normSq_nonneg _)

/-- `Γ ≤ t·opN(A₁)²·ρ²`. -/
theorem GamS_le (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    GamS A₁ c τ ≤ 2 / (m : ℝ) * opN A₁ ^ 2 * (normSq c + (n : ℝ) * τ ^ 2) := by
  unfold GamS
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← (int_normSq_shift c τ).2, ← integral_const_mul]
  exact integral_mono (integrable_h1_sq A₁ c τ) ((int_normSq_shift c τ).1.const_mul _)
    fun ξ => (normSq_reluV_le _).trans (normSq_mulVec_le _ _)

end cov

/-- On `E_op`: `Γ ≤ 4w_nρ²/n`. -/
theorem GamS_le_Eop {n : ℕ} (hn : 1 ≤ n) {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} (hA : A₁ ∈ Eop n)
    (c : Fin n → ℝ) (τ : ℝ) :
    GamS A₁ c τ ≤ 4 * wn n / n * (normSq c + (n : ℝ) * τ ^ 2) :=
  (GamS_le A₁ c τ).trans (mul_le_mul_of_nonneg_right (Eop_sq hn hA)
    (add_nonneg (normSq_nonneg _) (by positivity)))

/-- On `E_op`: `t_A·‖A₁‖_F² ≤ 4w_n`. -/
theorem fro_le_Eop {n : ℕ} (hn : 1 ≤ n) {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} (hA : A₁ ∈ Eop n) :
    2 / ((mA n : ℕ) : ℝ) * ∑ i, ∑ j, A₁ i j ^ 2 ≤ 4 * wn n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := fro_le A₁
  have h2 := Eop_sq hn hA
  calc 2 / ((mA n : ℕ) : ℝ) * ∑ i, ∑ j, A₁ i j ^ 2
      ≤ 2 / ((mA n : ℕ) : ℝ) * ((n : ℝ) * opN A₁ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (n : ℝ) * (2 / ((mA n : ℕ) : ℝ) * opN A₁ ^ 2) := by ring
    _ ≤ (n : ℝ) * (4 * wn n / n) := mul_le_mul_of_nonneg_left h2 hn0.le
    _ = 4 * wn n := by field_simp

end BstLean.Part153
