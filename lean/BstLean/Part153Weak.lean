import BstLean.Part153SJ

/-!
# Part 153, item 4: the weak covariance bound with an explicit constant

From the operator norms alone (no masks): `Ξ ≤ t_A·‖A₂‖²·‖A₁‖²/(n − 3)` for every `(A₁, A₂)`
(`XiS_le_op`, Part153SJ). On the two operator-norm events this is `Ξ ≤ C·γ_A/n` with
`C = Cweak n = 16·(1 + 1/(2√n))²·w_n·n/(n − 3)` (about `16.9` at `n = 8192`; the paper has
`M_P ≈ 1.2` by Lemma PP).

* `Eop2 n = {A₂ | opN A₂ ≤ √(2/n²)·(2n + √n)}`; `Eop2_prob`: `Pr(A₂ ∉ Eop2) ≤ exp(−n/2)`.
* **`XiS_le_weak`**: on `E_op ∩ Eop2`: `Ξ ≤ Cweak n·(2/n)/n`.
* **`weak_var_event`**: on `E_op ∩ Eop2`: `Var_x φ(q(x)) ≤ L_φ²·Cweak n·(2/n)/n`.
* `Cweak_le`: `Cweak n ≤ 17` for `n ≥ 8192`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part148 (EuLip)
open BstLean.Part130 BstLean.Part152

/-- The operator-norm event of `A₂`: `‖A₂‖_op ≤ √(t_A)·(2n + √n)`. -/
def Eop2 (n : ℕ) : Set (Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  {M | opN M ≤ √(2 / ((mA n : ℕ) : ℝ)) * (2 * (n : ℝ) + √(n : ℝ))}

theorem Eop2_prob {n : ℕ} (hn : 1 ≤ n) :
    (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))).real (Eop2 n)ᶜ ≤ Real.exp (-(n : ℝ) / 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by
    have : 0 < mA n := by unfold mA; positivity
    exact_mod_cast this
  have h := opN_tail' (p := mA n) (q := mA n) (v := 2 / ((mA n : ℕ) : ℝ)) (by positivity)
    (u := √(n : ℝ)) (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt hn0.le, sqrt_mA] at h
  refine le_trans (measureReal_mono (fun M hM => ?_)) h
  simp only [Eop2, mem_compl_iff, mem_ofPred_eq, not_le] at hM ⊢
  have e : (n : ℝ) + n + √(n : ℝ) = 2 * (n : ℝ) + √(n : ℝ) := by ring
  rw [e]
  exact hM.le

/-- The constant of the weak covariance bound. -/
noncomputable def Cweak (n : ℕ) : ℝ :=
  16 * (1 + 1 / (2 * √(n : ℝ))) ^ 2 * wn n * (n / ((n : ℝ) - 3))

lemma Eop2_sq {n : ℕ} (hn : 1 ≤ n) {M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ} (hM : M ∈ Eop2 n) :
    opN M ^ 2 ≤ 8 * (1 + 1 / (2 * √(n : ℝ))) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have h1 : opN M ^ 2 ≤ (√(2 / ((mA n : ℕ) : ℝ)) * (2 * (n : ℝ) + √(n : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (opN_nonneg M) hM 2
  rw [mul_pow, Real.sq_sqrt (by rw [hm]; positivity), hm] at h1
  refine h1.trans (le_of_eq ?_)
  have e : (1 + 1 / (2 * √(n : ℝ))) = (2 * (n : ℝ) + √(n : ℝ)) / (2 * n) := by
    field_simp
    nlinarith [hss]
  rw [e]
  field_simp
  ring

/-- **The weak bound of `Ξ` on the operator-norm events.** -/
theorem XiS_le_weak {n : ℕ} (hn : 4 ≤ n) {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ}
    {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ} (h1 : A₁ ∈ Eop n) (h2 : A₂ ∈ Eop2 n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    XiS A₁ A₂ c τ ≤ Cweak n * (2 / (n : ℝ)) / n := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn3 : (0 : ℝ) < (n : ℝ) - 3 := by
    have : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hx := XiS_le_op hn A₁ A₂ c hτ
  have ha := Eop_sq hn1 h1
  have hb := Eop2_sq hn1 h2
  have hw : 0 ≤ wn n := sq_nonneg _
  set β := (1 + 1 / (2 * √(n : ℝ))) ^ 2 with hβ
  have hβ0 : 0 ≤ β := sq_nonneg _
  have hprod : 2 / ((mA n : ℕ) : ℝ) * opN A₂ ^ 2 * opN A₁ ^ 2 ≤ 8 * β * (4 * wn n / n) := by
    calc 2 / ((mA n : ℕ) : ℝ) * opN A₂ ^ 2 * opN A₁ ^ 2
        = opN A₂ ^ 2 * (2 / ((mA n : ℕ) : ℝ) * opN A₁ ^ 2) := by ring
      _ ≤ 8 * β * (4 * wn n / n) :=
        mul_le_mul hb ha (mul_nonneg (by positivity) (sq_nonneg _)) (by positivity)
  refine hx.trans ?_
  calc 2 / ((mA n : ℕ) : ℝ) * opN A₂ ^ 2 * opN A₁ ^ 2 / ((n : ℝ) - 3)
      ≤ 8 * β * (4 * wn n / n) / ((n : ℝ) - 3) := div_le_div_of_nonneg_right hprod hn3.le
    _ = Cweak n * (2 / (n : ℝ)) / n := by
        unfold Cweak
        rw [← hβ]
        field_simp
        ring

/-- **The weak covariance bound on the operator-norm events**: for a Lipschitz `φ`,
`Var_x φ(q(x)) ≤ L_φ²·Cweak n·γ_A/n`, `q(x) = √t_A·a₂(x)`. -/
theorem weak_var_event {n : ℕ} (hn : 6 ≤ n) {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ}
    {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ} (h1 : A₁ ∈ Eop n) (h2 : A₂ ∈ Eop2 n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {φ : (Fin (mA n) → ℝ) → ℝ} {Lφ : ℝ} (hL : 0 ≤ Lφ)
    (hφ : EuLip φ Lφ) :
    ∫ ξ, (φ (√(2 / ((mA n : ℕ) : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) -
      ∫ ξ', φ (√(2 / ((mA n : ℕ) : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ'))) ∂stdGauss (Fin n)) ^ 2
        ∂stdGauss (Fin n) ≤ Lφ ^ 2 * (Cweak n * (2 / (n : ℝ)) / n) :=
  ((lemmaS_jac hn A₁ A₂ c hτ hL hφ).2).trans
    (mul_le_mul_of_nonneg_left (XiS_le_weak (by omega) h1 h2 c hτ) (sq_nonneg _))

/-- `Cweak n ≤ 17` for `n ≥ 8192`. -/
theorem Cweak_le {n : ℕ} (hn : 8192 ≤ n) : Cweak n ≤ 17 := by
  have hn0 : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (90 : ℝ) ≤ √(n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h1 : 1 / (2 * √(n : ℝ)) ≤ 1 / 180 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h1' : (0 : ℝ) ≤ 1 / (2 * √(n : ℝ)) := by positivity
  have h2 : 2 / √(n : ℝ) ≤ 2 / 90 := by
    rw [div_le_div_iff₀ hs0 (by norm_num)]
    linarith
  have h2' : (0 : ℝ) ≤ 2 / √(n : ℝ) := by positivity
  have h3 : (n : ℝ) / ((n : ℝ) - 3) ≤ 8192 / 8189 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h3' : (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) - 3) := div_nonneg (by linarith) (by linarith)
  have ha : (1 + 1 / (2 * √(n : ℝ))) ^ 2 ≤ (1 + 1 / 180) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hb : wn n ≤ (1 + 2 / 90) ^ 2 := by
    unfold wn
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hw0 : 0 ≤ wn n := sq_nonneg _
  unfold Cweak
  calc 16 * (1 + 1 / (2 * √(n : ℝ))) ^ 2 * wn n * (n / ((n : ℝ) - 3))
      ≤ 16 * (1 + 1 / 180) ^ 2 * (1 + 2 / 90) ^ 2 * (8192 / 8189) := by
        apply mul_le_mul _ h3 h3' (by positivity)
        apply mul_le_mul _ hb hw0 (by positivity)
        exact mul_le_mul_of_nonneg_left ha (by norm_num)
    _ ≤ 17 := by norm_num

#print axioms Eop2_prob
#print axioms XiS_le_weak
#print axioms weak_var_event
#print axioms Cweak_le

end BstLean.Part153
