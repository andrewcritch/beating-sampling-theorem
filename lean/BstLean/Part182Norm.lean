import BstLean.Part182Kap
import BstLean.Part152GC
import BstLean.Part153Op
import BstLean.Part130Layer

/-!
# Part 182 (file `Norm`): the five norm tails of Lemma TI and the overlap bound `c₁⁺`

No proof is left open; no `native_decide` or `axiom` is used.

Paper source: `proofs/option-n/theorem7-04-frame-numerator.tex`, Lemma `t7:p04:ti`, the table row
"`a₋ ≤ |a|, |a'| ≤ a₊`; `|a − a'| ≥ d₋`" (5 tails) and the sentence "These facts give the five
norm tails and the upper overlap `c₁⁺`". Setting: `A₁ ~ gaussMat (mA n) n (2/n)`, unit `x`, `x'`,
`c = x·x'`, `a = ReLU(A₁x)`, `a' = ReLU(A₁x')`, `γ = 2/n`, `υ = √(2τ)`.

* `nmA_mom`, `nmD_mom`: `E|a|² = m v/2` (`= n`), `E|a − a'|² = m v (1 − κ(c))` (`= 2n(1 − κ(c))`),
  from Part 130's `row_formula`.
* `nm_mean`, `nm_upper`, `nm_lower`: for a nonnegative Frobenius-Lipschitz `g`,
  `√(E g² − vL²) ≤ E g ≤ √(E g²)`, and the two tails from Part 152's SHARP Gaussian concentration
  (`exp(−t²/(2vL²))`) and Poincaré (`Var g ≤ vL²`).
* **`nm_tail_a_upper`**, **`nm_tail_a_lower`**, **`nm_tail_d_lower`**: the paper's tails with the
  paper's constants: `Pr(|a| ≥ √n + υ√γ)`, `Pr(|a| ≤ √(n−γ) − υ√γ)`,
  `Pr(|a − a'| ≤ √(2n(1 − κ(c)) − 4γ) − 2υ√γ)`, each `≤ e^{−τ}` (non-strict inequalities, so
  slightly larger sets than the paper's).
* **`nm_cos_le`**: the deterministic overlap bound `a·a'/(|a||a'|) ≤ (2a₊² − d₋²)/(2a₋²)`
  (needs `d₋² ≤ 2a₊²`, i.e. `c₁⁺ ≥ 0`, as in the paper's condition `0 < c₁⁺`).
* **`nm_overlap_tail`**: outside an event of probability `≤ 5e^{−τ}`, `a, a' ≠ 0` and
  `q ≤ c₁⁺`.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130
open BstLean.Part153 (nrm nrm_nonneg nrm_sq nrm_reluV_sub_le abs_nrm_sub_le nrm_add_le)

variable {m k : ℕ}

/-! ## Frobenius–Lipschitz bounds -/

lemma nm_normSq_mulVec_le (N : Matrix (Fin m) (Fin k) ℝ) (x : Fin k → ℝ) :
    normSq (N *ᵥ x) ≤ (∑ i, ∑ j, N i j ^ 2) * normSq x := by
  unfold normSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma nm_nrm_mulVec_sub (M M' : Matrix (Fin m) (Fin k) ℝ) {x : Fin k → ℝ}
    (hx : normSq x = 1) :
    nrm (M *ᵥ x - M' *ᵥ x) ≤ √(∑ i, ∑ j, (M i j - M' i j) ^ 2) := by
  rw [← Matrix.sub_mulVec]
  unfold nrm
  apply Real.sqrt_le_sqrt
  have := nm_normSq_mulVec_le (M - M') x
  rw [hx, mul_one] at this
  simpa [Matrix.sub_apply] using this

/-- `|a| = |ReLU(M x)|`. -/
noncomputable def nmA (x : Fin k → ℝ) (M : Matrix (Fin m) (Fin k) ℝ) : ℝ := nrm (reluV (M *ᵥ x))

/-- `|a − a'| = |ReLU(M x) − ReLU(M x')|`. -/
noncomputable def nmD (x x' : Fin k → ℝ) (M : Matrix (Fin m) (Fin k) ℝ) : ℝ :=
  nrm (reluV (M *ᵥ x) - reluV (M *ᵥ x'))

lemma nmA_lip {x : Fin k → ℝ} (hx : normSq x = 1) (M M' : Matrix (Fin m) (Fin k) ℝ) :
    |nmA x M - nmA x M'| ≤ 1 * √(∑ i, ∑ j, (M i j - M' i j) ^ 2) := by
  rw [one_mul]
  exact ((abs_nrm_sub_le _ _).trans (nrm_reluV_sub_le _ _)).trans (nm_nrm_mulVec_sub M M' hx)

lemma nm_nrm_sub_le (u v : Fin m → ℝ) : nrm (u - v) ≤ nrm u + nrm v := by
  have h := nrm_add_le u (-v)
  have e : nrm (-v) = nrm v := by unfold nrm normSq; simp
  rw [← sub_eq_add_neg, e] at h
  exact h

lemma nmD_lip {x x' : Fin k → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    (M M' : Matrix (Fin m) (Fin k) ℝ) :
    |nmD x x' M - nmD x x' M'| ≤ 2 * √(∑ i, ∑ j, (M i j - M' i j) ^ 2) := by
  unfold nmD
  refine (abs_nrm_sub_le _ _).trans ?_
  have e : reluV (M *ᵥ x) - reluV (M *ᵥ x') - (reluV (M' *ᵥ x) - reluV (M' *ᵥ x')) =
      (reluV (M *ᵥ x) - reluV (M' *ᵥ x)) - (reluV (M *ᵥ x') - reluV (M' *ᵥ x')) := by abel
  rw [e]
  refine (nm_nrm_sub_le _ _).trans ?_
  have h1 := (nrm_reluV_sub_le (M *ᵥ x) (M' *ᵥ x)).trans (nm_nrm_mulVec_sub M M' hx)
  have h2 := (nrm_reluV_sub_le (M *ᵥ x') (M' *ᵥ x')).trans (nm_nrm_mulVec_sub M M' hx')
  linarith

/-! ## Mean bounds and tails from the second moment -/

section gen

variable {g : Matrix (Fin m) (Fin k) ℝ → ℝ} {L v S : ℝ}

/-- **The mean of a nonnegative Frobenius-Lipschitz function of a Gaussian matrix** lies between
`√(E g² − v L²)` and `√(E g²)`. -/
theorem nm_mean (hL0 : 0 ≤ L)
    (hL : ∀ M M' : Matrix (Fin m) (Fin k) ℝ,
      |g M - g M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2))
    (hv : 0 ≤ v) (hg0 : ∀ M, 0 ≤ g M)
    (hSi : Integrable (fun M => g M ^ 2) (gaussMat m k v))
    (hS : ∫ M, g M ^ 2 ∂gaussMat m k v = S) :
    ∫ M, g M ∂gaussMat m k v ≤ √S ∧ √(S - v * L ^ 2) ≤ ∫ M, g M ∂gaussMat m k v := by
  have hgc := BstLean.Part148.matLip_continuous hL
  have hgm := hgc.measurable
  set μ := ∫ M, g M ∂gaussMat m k v with hμ
  have hgi : Integrable g (gaussMat m k v) := by
    refine (hSi.add (integrable_const (1 : ℝ))).mono' hgm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun M => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 M)]
    nlinarith [sq_nonneg (g M - 1)]
  obtain ⟨-, hvar⟩ := BstLean.Part152.gaussVar_mat_le_sharp hL0 hL hv
  rw [← hμ] at hvar
  have hexp : ∫ M, (g M - μ) ^ 2 ∂gaussMat m k v = S - μ ^ 2 := by
    have e : (fun M => (g M - μ) ^ 2) = fun M => g M ^ 2 + (-(2 * μ) * g M + μ ^ 2) := by
      funext M; ring
    rw [e, integral_add (f := fun M => g M ^ 2) (g := fun M => -(2 * μ) * g M + μ ^ 2) hSi
        ((hgi.const_mul _).add (integrable_const _)),
      integral_add (f := fun M => -(2 * μ) * g M) (g := fun _ => μ ^ 2) (hgi.const_mul _)
        (integrable_const _), integral_const_mul, integral_const,
      probReal_univ, one_smul, hS, ← hμ]
    ring
  rw [hexp] at hvar
  have h0 : 0 ≤ ∫ M, (g M - μ) ^ 2 ∂gaussMat m k v := integral_nonneg fun M => sq_nonneg _
  rw [hexp] at h0
  have hμ0 : 0 ≤ μ := integral_nonneg hg0
  constructor
  · rw [show μ = √(μ ^ 2) from (Real.sqrt_sq hμ0).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  · rw [show μ = √(μ ^ 2) from (Real.sqrt_sq hμ0).symm]
    exact Real.sqrt_le_sqrt (by linarith)

/-- Upper tail from the second moment: `Pr(g ≥ √(E g²) + t) ≤ exp(−t²/(2vL²))`. -/
theorem nm_upper (hL0 : 0 ≤ L)
    (hL : ∀ M M' : Matrix (Fin m) (Fin k) ℝ,
      |g M - g M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2))
    (hv : 0 ≤ v) (hg0 : ∀ M, 0 ≤ g M)
    (hSi : Integrable (fun M => g M ^ 2) (gaussMat m k v))
    (hS : ∫ M, g M ^ 2 ∂gaussMat m k v = S) {t : ℝ} (ht : 0 ≤ t) :
    (gaussMat m k v).real {M | √S + t ≤ g M} ≤ Real.exp (-t ^ 2 / (2 * (v * L ^ 2))) := by
  have hm := (nm_mean hL0 hL hv hg0 hSi hS).1
  refine le_trans (measureReal_mono (fun M hM => ?_) (measure_ne_top _ _))
    (BstLean.Part152.gaussConc_mat_upper_sharp hL0 hL hv ht)
  simp only [Set.mem_setOf_eq] at hM ⊢
  linarith

/-- Lower tail from the second moment: `Pr(g ≤ √(E g² − vL²) − t) ≤ exp(−t²/(2vL²))`. -/
theorem nm_lower (hL0 : 0 ≤ L)
    (hL : ∀ M M' : Matrix (Fin m) (Fin k) ℝ,
      |g M - g M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2))
    (hv : 0 ≤ v) (hg0 : ∀ M, 0 ≤ g M)
    (hSi : Integrable (fun M => g M ^ 2) (gaussMat m k v))
    (hS : ∫ M, g M ^ 2 ∂gaussMat m k v = S) {t : ℝ} (ht : 0 ≤ t) :
    (gaussMat m k v).real {M | g M ≤ √(S - v * L ^ 2) - t} ≤
      Real.exp (-t ^ 2 / (2 * (v * L ^ 2))) := by
  have hm := (nm_mean hL0 hL hv hg0 hSi hS).2
  refine le_trans (measureReal_mono (fun M hM => ?_) (measure_ne_top _ _))
    (BstLean.Part152.gaussConc_mat_lower_sharp hL0 hL hv ht)
  simp only [Set.mem_setOf_eq] at hM ⊢
  linarith

end gen

/-! ## The second moments -/

section mom

variable {v : ℝ}

lemma nm_continuous_coord (x : Fin k → ℝ) (i : Fin m) :
    Continuous (fun M : Matrix (Fin m) (Fin k) ℝ => relu ((M *ᵥ x) i)) := by
  have h1 : Continuous (fun M : Matrix (Fin m) (Fin k) ℝ => (M *ᵥ x) i) := by
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  exact continuous_relu.comp h1

lemma nm_sum_self {x : Fin k → ℝ} (hx : normSq x = 1) : ∑ j, x j * x j = 1 := by
  rw [← hx]; unfold normSq; exact Finset.sum_congr rfl fun j _ => (sq _).symm

/-- `E[ReLU((Mx)_i)²] = v/2` for a unit `x`. -/
lemma nm_sq_int (hv : 0 ≤ v) {x : Fin k → ℝ} (hx : normSq x = 1) (i : Fin m) :
    ∫ M, relu ((M *ᵥ x) i) ^ 2 ∂gaussMat m k v = v / 2 := by
  have h := row_formula hv x x i
  rw [nm_sum_self hx, hx, Real.sqrt_one, one_mul, div_one, kappa_one] at h
  have e : (fun M : Matrix (Fin m) (Fin k) ℝ => relu ((M *ᵥ x) i) ^ 2) =
      fun M => relu ((M.mulVec x) i) * relu ((M.mulVec x) i) := by
    funext M; rw [sq]
  rw [e]
  linarith

/-- `E[ReLU((Mx)_i)·ReLU((Mx')_i)] = v κ(x·x')/2` for unit `x`, `x'`. -/
lemma nm_cross_int (hv : 0 ≤ v) {x x' : Fin k → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    (i : Fin m) :
    ∫ M, relu ((M *ᵥ x) i) * relu ((M *ᵥ x') i) ∂gaussMat m k v = v * kappa (x ⬝ᵥ x') / 2 := by
  have h := row_formula hv x x' i
  rw [hx, hx', Real.sqrt_one, one_mul, div_one] at h
  have e : (∑ j, x j * x' j) = x ⬝ᵥ x' := rfl
  rw [e] at h
  change 2 * ∫ M, relu ((M *ᵥ x) i) * relu ((M *ᵥ x') i) ∂gaussMat m k v = _ at h
  linarith

lemma nm_sq_integrable (hv : 0 < v) {x : Fin k → ℝ} (hx : normSq x = 1) (i : Fin m) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => relu ((M *ᵥ x) i) ^ 2) (gaussMat m k v) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [nm_sq_int hv.le hx i]
  positivity

lemma nm_cross_integrable (hv : 0 < v) {x x' : Fin k → ℝ} (hx : normSq x = 1)
    (hx' : normSq x' = 1) (i : Fin m) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => relu ((M *ᵥ x) i) * relu ((M *ᵥ x') i))
      (gaussMat m k v) := by
  refine (((nm_sq_integrable hv hx i).add (nm_sq_integrable hv hx' i)).div_const 2).mono'
    ((nm_continuous_coord x i).mul (nm_continuous_coord x' i)).measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun M => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [abs_mul]
  nlinarith [sq_nonneg (|relu ((M *ᵥ x) i)| - |relu ((M *ᵥ x') i)|), sq_abs (relu ((M *ᵥ x) i)),
    sq_abs (relu ((M *ᵥ x') i))]

lemma nmA_sq (x : Fin k → ℝ) (M : Matrix (Fin m) (Fin k) ℝ) :
    nmA x M ^ 2 = ∑ i, relu ((M *ᵥ x) i) ^ 2 := by
  unfold nmA; rw [nrm_sq]; rfl

lemma nmD_sq (x x' : Fin k → ℝ) (M : Matrix (Fin m) (Fin k) ℝ) :
    nmD x x' M ^ 2 = ∑ i, (relu ((M *ᵥ x) i) ^ 2 + relu ((M *ᵥ x') i) ^ 2 -
      2 * (relu ((M *ᵥ x) i) * relu ((M *ᵥ x') i))) := by
  unfold nmD; rw [nrm_sq]; unfold normSq
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, reluV]
  ring

/-- **`E|ReLU(Mx)|² = m v/2`** for a unit `x`. -/
theorem nmA_mom (hv : 0 < v) {x : Fin k → ℝ} (hx : normSq x = 1) :
    Integrable (fun M => nmA x M ^ 2) (gaussMat m k v) ∧
    ∫ M, nmA x M ^ 2 ∂gaussMat m k v = m * (v / 2) := by
  simp_rw [nmA_sq]
  refine ⟨integrable_finset_sum _ fun i _ => nm_sq_integrable hv hx i, ?_⟩
  rw [integral_finset_sum _ fun i _ => nm_sq_integrable hv hx i]
  simp_rw [nm_sq_int hv.le hx]
  simp

/-- **`E|ReLU(Mx) − ReLU(Mx')|² = m v (1 − κ(x·x'))`** for unit `x`, `x'`. -/
theorem nmD_mom (hv : 0 < v) {x x' : Fin k → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    Integrable (fun M => nmD x x' M ^ 2) (gaussMat m k v) ∧
    ∫ M, nmD x x' M ^ 2 ∂gaussMat m k v = m * (v * (1 - kappa (x ⬝ᵥ x'))) := by
  simp_rw [nmD_sq]
  have hi : ∀ i : Fin m, Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      relu ((M *ᵥ x) i) ^ 2 + relu ((M *ᵥ x') i) ^ 2 -
        2 * (relu ((M *ᵥ x) i) * relu ((M *ᵥ x') i))) (gaussMat m k v) := fun i =>
    ((nm_sq_integrable hv hx i).add (nm_sq_integrable hv hx' i)).sub
      ((nm_cross_integrable hv hx hx' i).const_mul 2)
  refine ⟨integrable_finset_sum _ fun i _ => hi i, ?_⟩
  rw [integral_finset_sum _ fun i _ => hi i]
  have he : ∀ i : Fin m, ∫ M, (relu ((M *ᵥ x) i) ^ 2 + relu ((M *ᵥ x') i) ^ 2 -
      2 * (relu ((M *ᵥ x) i) * relu ((M *ᵥ x') i))) ∂gaussMat m k v =
      v * (1 - kappa (x ⬝ᵥ x')) := by
    intro i
    rw [integral_sub (f := fun M : Matrix (Fin m) (Fin k) ℝ =>
        relu ((M *ᵥ x) i) ^ 2 + relu ((M *ᵥ x') i) ^ 2)
      (g := fun M => 2 * (relu ((M *ᵥ x) i) * relu ((M *ᵥ x') i)))
      ((nm_sq_integrable hv hx i).add (nm_sq_integrable hv hx' i))
      ((nm_cross_integrable hv hx hx' i).const_mul 2),
      integral_add (nm_sq_integrable hv hx i) (nm_sq_integrable hv hx' i), integral_const_mul,
      nm_sq_int hv.le hx, nm_sq_int hv.le hx', nm_cross_int hv.le hx hx']
    ring
  simp_rw [he]
  simp

end mom

/-! ## The five norm tails of Lemma TI at `v = γ = 2/n`, `m = n²` -/

section tails

variable {n : ℕ}

lemma nm_mA_half (hn : 1 ≤ n) : ((mA n : ℕ) : ℝ) * (2 / (n : ℝ) / 2) = n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold mA; push_cast; field_simp

lemma nm_exp_eq {τ L : ℝ} (hn : 1 ≤ n) (hL : 0 < L) (hτ : 0 ≤ τ) :
    Real.exp (-(L * (√(2 * τ) * √(2 / (n : ℝ)))) ^ 2 / (2 * (2 / (n : ℝ) * L ^ 2))) =
      Real.exp (-τ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  congr 1
  rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by positivity)]
  field_simp

/-- **Upper tail of `|a|`**: `Pr(|ReLU(A₁x)| ≥ √n + υ√γ) ≤ e^{−τ}` (`υ = √(2τ)`, `γ = 2/n`). -/
theorem nm_tail_a_upper (hn : 1 ≤ n) {x : Fin n → ℝ} (hx : normSq x = 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      {M | √(n : ℝ) + √(2 * τ) * √(2 / (n : ℝ)) ≤ nmA x M} ≤ Real.exp (-τ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  obtain ⟨hi, hS⟩ := nmA_mom (m := mA n) hv hx
  rw [nm_mA_half hn] at hS
  have h := nm_upper (L := 1) zero_le_one (nmA_lip hx) hv.le (fun M => nrm_nonneg _) hi hS
    (t := 1 * (√(2 * τ) * √(2 / (n : ℝ)))) (by positivity)
  rw [nm_exp_eq hn one_pos hτ, one_mul] at h
  exact h

/-- **Lower tail of `|a|`**: `Pr(|ReLU(A₁x)| ≤ √(n − γ) − υ√γ) ≤ e^{−τ}`. -/
theorem nm_tail_a_lower (hn : 1 ≤ n) {x : Fin n → ℝ} (hx : normSq x = 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      {M | nmA x M ≤ √((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ))} ≤ Real.exp (-τ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  obtain ⟨hi, hS⟩ := nmA_mom (m := mA n) hv hx
  rw [nm_mA_half hn] at hS
  have h := nm_lower (L := 1) zero_le_one (nmA_lip hx) hv.le (fun M => nrm_nonneg _) hi hS
    (t := 1 * (√(2 * τ) * √(2 / (n : ℝ)))) (by positivity)
  rw [nm_exp_eq hn one_pos hτ, one_mul, one_pow, mul_one] at h
  exact h

/-- **Lower tail of `|a − a'|`**: `Pr(|ReLU(A₁x) − ReLU(A₁x')| ≤ √(2n(1 − κ(c)) − 4γ) − 2υ√γ)
≤ e^{−τ}`, `c = x·x'`. -/
theorem nm_tail_d_lower (hn : 1 ≤ n) {x x' : Fin n → ℝ} (hx : normSq x = 1)
    (hx' : normSq x' = 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      {M | nmD x x' M ≤ √(2 * n * (1 - kappa (x ⬝ᵥ x')) - 4 * (2 / n)) -
        2 * (√(2 * τ) * √(2 / (n : ℝ)))} ≤ Real.exp (-τ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  obtain ⟨hi, hS⟩ := nmD_mom (m := mA n) hv hx hx'
  have e : ((mA n : ℕ) : ℝ) * (2 / (n : ℝ) * (1 - kappa (x ⬝ᵥ x'))) =
      2 * n * (1 - kappa (x ⬝ᵥ x')) := by
    unfold mA; push_cast; field_simp
  rw [e] at hS
  have h := nm_lower (L := 2) zero_le_two (nmD_lip hx hx') hv.le (fun M => nrm_nonneg _) hi hS
    (t := 2 * (√(2 * τ) * √(2 / (n : ℝ)))) (by positivity)
  rw [nm_exp_eq hn two_pos hτ] at h
  have e2 : 2 / (n : ℝ) * 2 ^ 2 = 4 * (2 / n) := by ring
  rw [e2] at h
  exact h

end tails

/-! ## The overlap bound `q ≤ c₁⁺` -/

lemma nm_normSq_sub (a b : Fin m → ℝ) : normSq (a - b) = normSq a + normSq b - 2 * (a ⬝ᵥ b) := by
  unfold normSq dotProduct
  simp only [Pi.sub_apply, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum]
  ring_nf

/-- **The deterministic overlap bound** (paper: "These facts give … the upper overlap `c₁⁺`"): if
`0 < a₋ ≤ |a|, |a'| ≤ a₊`, `|a − a'| ≥ d₋ ≥ 0` and `d₋² ≤ 2a₊²`, then
`a·a'/(|a||a'|) ≤ (2a₊² − d₋²)/(2a₋²)`. -/
theorem nm_cos_le {a b : Fin m → ℝ} {am ap dm : ℝ} (ham : 0 < am) (hdm : 0 ≤ dm)
    (h1 : am ≤ nrm a) (h2 : nrm a ≤ ap) (h3 : am ≤ nrm b) (h4 : nrm b ≤ ap)
    (h5 : dm ≤ nrm (a - b)) (h6 : dm ^ 2 ≤ 2 * ap ^ 2) :
    (a ⬝ᵥ b) / (nrm a * nrm b) ≤ (2 * ap ^ 2 - dm ^ 2) / (2 * am ^ 2) := by
  have ha0 : 0 < nrm a := lt_of_lt_of_le ham h1
  have hb0 : 0 < nrm b := lt_of_lt_of_le ham h3
  have hab : 0 < nrm a * nrm b := mul_pos ha0 hb0
  have hS := nm_normSq_sub a b
  rw [← nrm_sq, ← nrm_sq, ← nrm_sq] at hS
  have hd2 : dm ^ 2 ≤ nrm (a - b) ^ 2 := pow_le_pow_left₀ hdm h5 2
  have ha2 : nrm a ^ 2 ≤ ap ^ 2 := pow_le_pow_left₀ ha0.le h2 2
  have hb2 : nrm b ^ 2 ≤ ap ^ 2 := pow_le_pow_left₀ hb0.le h4 2
  have hdot : a ⬝ᵥ b ≤ (2 * ap ^ 2 - dm ^ 2) / 2 := by linarith
  have hR : 0 ≤ (2 * ap ^ 2 - dm ^ 2) / (2 * am ^ 2) := by
    apply div_nonneg <;> nlinarith
  rcases lt_or_ge (a ⬝ᵥ b) 0 with hneg | hpos
  · exact le_trans (div_nonpos_of_nonpos_of_nonneg hneg.le hab.le) hR
  · have hlow : am ^ 2 ≤ nrm a * nrm b := by nlinarith
    rw [div_le_div_iff₀ hab (by positivity)]
    nlinarith

/-- **The overlap event of Lemma TI** (five tails): with `υ = √(2τ)`, `γ = 2/n`,
`a₊ = √n + υ√γ`, `a₋ = √(n − γ) − υ√γ`, `d₋ = √(2n(1 − κ(c)) − 4γ) − 2υ√γ` (`c = x·x'`), if
`a₋ > 0`, `d₋ ≥ 0` and `d₋² ≤ 2a₊²`, then outside an event of probability `≤ 5e^{−τ}` the
cosine `q` of `a = ReLU(A₁x)`, `a' = ReLU(A₁x')` satisfies `q ≤ (2a₊² − d₋²)/(2a₋²) = c₁⁺`, and
`a, a' ≠ 0`. -/
theorem nm_overlap_tail {n : ℕ} (hn : 1 ≤ n) {x x' : Fin n → ℝ} (hx : normSq x = 1)
    (hx' : normSq x' = 1) {τ : ℝ} (hτ : 0 ≤ τ)
    (ham : 0 < √((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ)))
    (hdm : 0 ≤ √(2 * n * (1 - kappa (x ⬝ᵥ x')) - 4 * (2 / n)) - 2 * (√(2 * τ) * √(2 / (n : ℝ))))
    (h6 : (√(2 * n * (1 - kappa (x ⬝ᵥ x')) - 4 * (2 / n)) - 2 * (√(2 * τ) * √(2 / (n : ℝ)))) ^ 2 ≤
      2 * (√(n : ℝ) + √(2 * τ) * √(2 / (n : ℝ))) ^ 2) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      {M | ¬ (0 < nmA x M ∧ 0 < nmA x' M ∧
        (reluV (M *ᵥ x) ⬝ᵥ reluV (M *ᵥ x')) / (nmA x M * nmA x' M) ≤
          (2 * (√(n : ℝ) + √(2 * τ) * √(2 / (n : ℝ))) ^ 2 -
            (√(2 * n * (1 - kappa (x ⬝ᵥ x')) - 4 * (2 / n)) -
              2 * (√(2 * τ) * √(2 / (n : ℝ)))) ^ 2) /
          (2 * (√((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ))) ^ 2))} ≤
      5 * Real.exp (-τ) := by
  set ap := √(n : ℝ) + √(2 * τ) * √(2 / (n : ℝ)) with hap
  set am := √((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ)) with ham'
  set dm := √(2 * n * (1 - kappa (x ⬝ᵥ x')) - 4 * (2 / n)) - 2 * (√(2 * τ) * √(2 / (n : ℝ)))
    with hdm'
  set μ := gaussMat (mA n) n (2 / (n : ℝ))
  set U1 := {M : Matrix (Fin (mA n)) (Fin n) ℝ | ap ≤ nmA x M}
  set U2 := {M : Matrix (Fin (mA n)) (Fin n) ℝ | ap ≤ nmA x' M}
  set L1 := {M : Matrix (Fin (mA n)) (Fin n) ℝ | nmA x M ≤ am}
  set L2 := {M : Matrix (Fin (mA n)) (Fin n) ℝ | nmA x' M ≤ am}
  set D := {M : Matrix (Fin (mA n)) (Fin n) ℝ | nmD x x' M ≤ dm}
  have hsub : {M | ¬ (0 < nmA x M ∧ 0 < nmA x' M ∧
      (reluV (M *ᵥ x) ⬝ᵥ reluV (M *ᵥ x')) / (nmA x M * nmA x' M) ≤
        (2 * ap ^ 2 - dm ^ 2) / (2 * am ^ 2))} ⊆ U1 ∪ U2 ∪ L1 ∪ L2 ∪ D := by
    intro M hM
    by_contra hc
    simp only [Set.mem_union, not_or, U1, U2, L1, L2, D, Set.mem_setOf_eq, not_le] at hc
    obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩ := hc
    apply hM
    refine ⟨ham.trans c3, ham.trans c4, ?_⟩
    exact nm_cos_le ham hdm c3.le c1.le c4.le c2.le c5.le h6
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  have u1 := nm_tail_a_upper hn hx hτ
  have u2 := nm_tail_a_upper hn hx' hτ
  have l1 := nm_tail_a_lower hn hx hτ
  have l2 := nm_tail_a_lower hn hx' hτ
  have d1 := nm_tail_d_lower hn hx hx' hτ
  calc μ.real (U1 ∪ U2 ∪ L1 ∪ L2 ∪ D)
      ≤ μ.real (U1 ∪ U2 ∪ L1 ∪ L2) + μ.real D := measureReal_union_le _ _
    _ ≤ μ.real (U1 ∪ U2 ∪ L1) + μ.real L2 + μ.real D := by
        gcongr; exact measureReal_union_le _ _
    _ ≤ μ.real (U1 ∪ U2) + μ.real L1 + μ.real L2 + μ.real D := by
        gcongr; exact measureReal_union_le _ _
    _ ≤ μ.real U1 + μ.real U2 + μ.real L1 + μ.real L2 + μ.real D := by
        gcongr; exact measureReal_union_le _ _
    _ ≤ 5 * Real.exp (-τ) := by linarith

end BstLean.Part182

open BstLean.Part182 in
#print axioms nm_overlap_tail
open BstLean.Part182 in
#print axioms nm_tail_a_upper
open BstLean.Part182 in
#print axioms nm_tail_a_lower
open BstLean.Part182 in
#print axioms nm_tail_d_lower
open BstLean.Part182 in
#print axioms nm_cos_le
open BstLean.Part182 in
#print axioms nmD_mom
