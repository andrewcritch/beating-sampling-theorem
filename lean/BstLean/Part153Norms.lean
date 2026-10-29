import BstLean.Part153Conc
import BstLean.Part153Pt
import BstLean.Part130Mean
import BstLean.Part149CDefs

/-!
# Part 153: norms of the hidden vectors over the stand-in input (Lemma N)

Paper source: `proofs/option-n/theorem5-07-norms.tex`, Lemma N.

Notation. `n ≥ 1` is the dimension, `m_A = mA n = n²`, `γ_A = 2/n`, `t_A = 2/m_A`. The stand-in
input is `y = c + τ·ξ`, `ξ` a standard Gaussian vector of `ℝⁿ`, and `x = sphPt y` (a unit
vector). `A₁` is an `m_A × n` matrix and `A₂` an `m_A × m_A` matrix.

* `sq1 A₁ c τ ξ = √ω₁(x) = |ReLU(A₁x)|/√n`; `sq2 A₁ A₂ c τ ξ = √ω₂(x) = |ReLU(A₂ReLU(A₁x))|/√n`.
* `N1 k A₁ c τ = ‖√ω₁ − 1‖_{L^k(ξ)}`; `N2 k A₁ A₂ c τ = ‖√ω₂ − 1‖_{L^k(ξ)}`.
* `x4n n = (75 + 558/n²)^{1/4}` (`≤ 3` for `n ≥ 10`), `N12bar`, `N14bar`, `N22bar`, `N24bar`.
* (i) `N1_lip`, `N1_event`, `N1_mean2`, `N1_mean4`, `N12_event`, `N14_event`.
* (ii-a), (ii-b) `N2_lip`, `lpNorm_sq1_le_one_add`, `lpNorm_sq1_le_opN`, `N22_event`, `N24_event`.
* Items (ii-c), (ii-d) and (iii) are in `Part153Norms2.lean`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open scoped ENNReal NNReal

/-! ## General tools -/

section tools

variable {m k : ℕ}

/-- `| |ReLU(Mv)| − |ReLU(M'v)| | ≤ ‖M − M'‖_F·|v|`. -/
lemma abs_layer_sub_le (M M' : Matrix (Fin m) (Fin k) ℝ) (v : Fin k → ℝ) :
    |nrm (reluV (M *ᵥ v)) - nrm (reluV (M' *ᵥ v))| ≤
      √(∑ i, ∑ j, (M i j - M' i j) ^ 2) * nrm v := by
  have e : M *ᵥ v - M' *ᵥ v = (M - M') *ᵥ v := (Matrix.sub_mulVec M M' v).symm
  have hF : opN (M - M') ≤ √(∑ i, ∑ j, (M i j - M' i j) ^ 2) := by
    simpa [Matrix.sub_apply] using opN_le_frob (M - M')
  calc |nrm (reluV (M *ᵥ v)) - nrm (reluV (M' *ᵥ v))|
      ≤ nrm (reluV (M *ᵥ v) - reluV (M' *ᵥ v)) := abs_nrm_sub_le _ _
    _ ≤ nrm (M *ᵥ v - M' *ᵥ v) := nrm_reluV_sub_le _ _
    _ = nrm ((M - M') *ᵥ v) := by rw [e]
    _ ≤ opN (M - M') * nrm v := nrm_mulVec_le _ _
    _ ≤ √(∑ i, ∑ j, (M i j - M' i j) ^ 2) * nrm v :=
        mul_le_mul_of_nonneg_right hF (nrm_nonneg v)

/-- `|ReLU(Mv)| ≤ opN M·|v|`. -/
lemma nrm_layer_le (M : Matrix (Fin m) (Fin k) ℝ) (v : Fin k → ℝ) :
    nrm (reluV (M *ᵥ v)) ≤ opN M * nrm v :=
  (nrm_reluV_le _).trans (nrm_mulVec_le _ _)

lemma measurable_layer_joint {Ξ : Type*} [MeasurableSpace Ξ] {f : Ξ → Fin k → ℝ}
    (hf : Measurable f) :
    Measurable (fun p : Matrix (Fin m) (Fin k) ℝ × Ξ => nrm (reluV (p.1 *ᵥ f p.2))) := by
  have hc : Continuous (fun q : Matrix (Fin m) (Fin k) ℝ × (Fin k → ℝ) => q.1 *ᵥ q.2) :=
    Continuous.matrix_mulVec continuous_fst continuous_snd
  have h1 : Measurable (fun p : Matrix (Fin m) (Fin k) ℝ × Ξ => p.1 *ᵥ f p.2) :=
    hc.measurable.comp (measurable_fst.prodMk (hf.comp measurable_snd))
  exact (continuous_normSq.measurable.comp (measurable_reluV.comp h1)).sqrt

lemma conc_const {x : ℝ} {Lc : ℝ} (hLc : 0 ≤ Lc) :
    √(2 * Lc * (2 / x)) = 2 * √Lc / √x := by
  rw [show 2 * Lc * (2 / x) = 2 ^ 2 * (Lc / x) by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num), Real.sqrt_div hLc]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma lpNorm_const_prob {p : ℕ} (hp : 1 ≤ p) (a : ℝ) :
    lpNorm (fun _ : Ω => a) (p : ℝ≥0∞) μ = |a| := by
  rw [lpNorm_const' (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hp) (ENNReal.natCast_ne_top p)]
  simp

/-- `‖f‖_p ≤ 1 + ‖f − 1‖_p` on a probability space. -/
lemma lpNorm_le_one_add {p : ℕ} (hp : 1 ≤ p) {f : Ω → ℝ}
    (hf : MemLp (fun x => f x - 1) (p : ℝ≥0∞) μ) :
    lpNorm f (p : ℝ≥0∞) μ ≤ 1 + lpNorm (fun x => f x - 1) (p : ℝ≥0∞) μ := by
  have h := lpNorm_add_le (g := fun _ => (1 : ℝ)) hf (by exact_mod_cast hp)
  have e : (fun x => f x - 1) + (fun _ => (1 : ℝ)) = f := by funext x; simp
  rw [e, lpNorm_const_prob hp, abs_one] at h
  linarith

omit [IsProbabilityMeasure μ] in
/-- `(∫ |f|^2)^{1/2} = ‖f‖_2`. -/
lemma rpow_half_eq {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) :
    (∫ x, |f x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = lpNorm f ((2 : ℕ) : ℝ≥0∞) μ := by
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, ← lpNorm_nat_pow (by norm_num) hf, Real.sqrt_sq lpNorm_nonneg]

end tools

/-! ## The definitions -/

variable {n : ℕ}

/-- `√ω₁(x) = |ReLU(A₁x)|/√n`, `x = sphPt (c + τξ)`. -/
noncomputable def sq1 (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (ξ : Fin n → ℝ) : ℝ :=
  nrm (reluV (A₁ *ᵥ sphPt (c + τ • ξ))) / √(n : ℝ)

/-- `√ω₂(x) = √(t_A/γ_A)·|ReLU(A₂ReLU(A₁x))| = |a₂(x)|/√n`, `x = sphPt (c + τξ)`. -/
noncomputable def sq2 (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) : ℝ :=
  nrm (reluV (A₂ *ᵥ reluV (A₁ *ᵥ sphPt (c + τ • ξ)))) / √(n : ℝ)

/-- `N_{1k} = ‖√ω₁ − 1‖_{L^k(x)}`. -/
noncomputable def N1 (k : ℕ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  lpNorm (fun ξ => sq1 A₁ c τ ξ - 1) (k : ℝ≥0∞) (stdGauss (Fin n))

/-- `N_{2k} = ‖√ω₂ − 1‖_{L^k(x)}`. -/
noncomputable def N2 (k : ℕ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  lpNorm (fun ξ => sq2 A₁ A₂ c τ ξ - 1) (k : ℝ≥0∞) (stdGauss (Fin n))

/-- The vector inside `sq1` is the first hidden vector `a1` of Part 149. -/
lemma sq1_eq_a1 (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) :
    sq1 A₁ c τ ξ = nrm (BstLean.Part149.a1 c τ A₁ ξ) / √(n : ℝ) := rfl

/-- The vector inside `sq2` is the last hidden vector `hid2` of Part 130. -/
lemma sq2_eq_hid2 (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) :
    sq2 A₁ A₂ c τ ξ = nrm (hid2 A₁ A₂ (sphPt (c + τ • ξ))) / √(n : ℝ) := rfl

/-- `x₄(n) = (75 + 558/n²)^{1/4}`. This is sharper than the constant `x₄ ≤ 3.949` of the paper
(`x4n_le`: `x₄(n) ≤ 3` for `n ≥ 10`). -/
noncomputable def x4n (n : ℕ) : ℝ := (75 + 558 / (n : ℝ) ^ 2) ^ ((1 : ℝ) / 4)

/-- `N̄₁₂ = (√5 + 2√L_c)/n`. -/
noncomputable def N12bar (n : ℕ) (Lc : ℝ) : ℝ := (√5 + 2 * √Lc) / n

/-- `N̄₁₄ = (x₄ + 2√L_c)/n`. -/
noncomputable def N14bar (n : ℕ) (Lc : ℝ) : ℝ := (x4n n + 2 * √Lc) / n

/-- `N̄₂₂ = N̄₁₂(2 + N̄₁₂)`. -/
noncomputable def N22bar (n : ℕ) (Lc : ℝ) : ℝ := N12bar n Lc * (2 + N12bar n Lc)

/-- `N̄₂₄ = x₄(1 + N̄₁₄)/n + N̄₁₄ + 2√(2L_c w_n)/n`. -/
noncomputable def N24bar (n : ℕ) (Lc : ℝ) : ℝ :=
  x4n n * (1 + N14bar n Lc) / n + N14bar n Lc + 2 * √(2 * Lc * wn n) / n

lemma x4n_nonneg (n : ℕ) : 0 ≤ x4n n := Real.rpow_nonneg (by positivity) _

lemma x4n_pow (n : ℕ) : x4n n ^ 4 = 75 + 558 / (n : ℝ) ^ 2 := by
  unfold x4n
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

/-- `x₄(n) ≤ 3` for `n ≥ 10`. -/
theorem x4n_le {n : ℕ} (hn : 10 ≤ n) : x4n n ≤ 3 := by
  have hn' : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (558 : ℝ) / (n : ℝ) ^ 2 ≤ 6 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  by_contra h
  rw [not_le] at h
  have h2 : (3 : ℝ) ^ 4 < x4n n ^ 4 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  rw [x4n_pow] at h2
  norm_num at h2
  linarith

/-! ## Basic facts on `sq1` and `sq2` -/

lemma mA_cast (n : ℕ) : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring

lemma one_le_mA (hn : 1 ≤ n) : 1 ≤ mA n := Nat.one_le_pow _ _ hn

lemma nrm_sphPt (hn : 1 ≤ n) (y : Fin n → ℝ) : nrm (sphPt y) = 1 := by
  unfold nrm
  rw [normSq_sphPt hn, Real.sqrt_one]

lemma measurable_x (c : Fin n → ℝ) (τ : ℝ) : Measurable (fun ξ : Fin n → ℝ => sphPt (c + τ • ξ)) :=
  measurable_sphPt.comp (continuous_const.add (continuous_const_smul τ)).measurable

lemma measurable_a1v (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun ξ : Fin n → ℝ => reluV (A₁ *ᵥ sphPt (c + τ • ξ))) :=
  measurable_reluV.comp ((Continuous.matrix_mulVec continuous_const continuous_id).measurable.comp
    (measurable_x c τ))

lemma measurable_sq1_joint (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin n → ℝ) => sq1 p.1 c τ p.2) :=
  (measurable_layer_joint (measurable_x c τ)).div_const _

lemma measurable_sq2_joint (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun p : Matrix (Fin (mA n)) (Fin (mA n)) ℝ × (Fin n → ℝ) =>
      sq2 A₁ p.1 c τ p.2) :=
  (measurable_layer_joint (measurable_a1v A₁ c τ)).div_const _

lemma measurable_sq1 (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (sq1 A₁ c τ) := by
  change Measurable ((fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin n → ℝ) => sq1 p.1 c τ p.2) ∘
    (fun ξ : Fin n → ℝ => (A₁, ξ)))
  exact (measurable_sq1_joint c τ).comp measurable_prodMk_left

lemma measurable_sq2 (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) : Measurable (sq2 A₁ A₂ c τ) := by
  change Measurable ((fun p : Matrix (Fin (mA n)) (Fin (mA n)) ℝ × (Fin n → ℝ) =>
    sq2 A₁ p.1 c τ p.2) ∘ (fun ξ : Fin n → ℝ => (A₂, ξ)))
  exact (measurable_sq2_joint A₁ c τ).comp measurable_prodMk_left

lemma sq1_nonneg (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) :
    0 ≤ sq1 A₁ c τ ξ := div_nonneg (nrm_nonneg _) (Real.sqrt_nonneg _)

lemma sq2_nonneg (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) :
    0 ≤ sq2 A₁ A₂ c τ ξ := div_nonneg (nrm_nonneg _) (Real.sqrt_nonneg _)

/-- `√ω₁ ≤ ‖A₁‖_op/√n` pointwise. -/
lemma sq1_le_opN (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (ξ : Fin n → ℝ) : sq1 A₁ c τ ξ ≤ opN A₁ / √(n : ℝ) := by
  unfold sq1
  have h := nrm_layer_le A₁ (sphPt (c + τ • ξ))
  rw [nrm_sphPt hn, mul_one] at h
  exact div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)

/-- `√ω₂ ≤ ‖A₂‖_op·√ω₁` pointwise. -/
lemma sq2_le_opN (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) : sq2 A₁ A₂ c τ ξ ≤ opN A₂ * sq1 A₁ c τ ξ := by
  unfold sq2 sq1
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (nrm_layer_le A₂ _) (Real.sqrt_nonneg _)

lemma memLp_sq1 (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (p : ℝ≥0∞) : MemLp (sq1 A₁ c τ) p (stdGauss (Fin n)) :=
  MemLp.of_bound (measurable_sq1 A₁ c τ).aestronglyMeasurable (opN A₁ / √(n : ℝ))
    (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (sq1_nonneg _ _ _ _)]; exact sq1_le_opN hn A₁ c τ ξ)

lemma memLp_sq2 (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (p : ℝ≥0∞) : MemLp (sq2 A₁ A₂ c τ) p (stdGauss (Fin n)) :=
  MemLp.of_bound (measurable_sq2 A₁ A₂ c τ).aestronglyMeasurable
    (opN A₂ * (opN A₁ / √(n : ℝ)))
    (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (sq2_nonneg _ _ _ _ _)]
      exact (sq2_le_opN A₁ A₂ c τ ξ).trans
        (mul_le_mul_of_nonneg_left (sq1_le_opN hn A₁ c τ ξ) (opN_nonneg _)))

lemma memLp_sq1_sub (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (p : ℝ≥0∞) : MemLp (fun ξ => sq1 A₁ c τ ξ - 1) p (stdGauss (Fin n)) :=
  (memLp_sq1 hn A₁ c τ p).sub (memLp_const 1)

lemma memLp_sq2_sub (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (p : ℝ≥0∞) : MemLp (fun ξ => sq2 A₁ A₂ c τ ξ - 1) p (stdGauss (Fin n)) :=
  (memLp_sq2 hn A₁ A₂ c τ p).sub (memLp_const 1)

lemma N1_nonneg (k : ℕ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    0 ≤ N1 k A₁ c τ := lpNorm_nonneg

lemma N2_nonneg (k : ℕ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    0 ≤ N2 k A₁ A₂ c τ := lpNorm_nonneg

/-! ## (i) The first layer: integrate `A₁` -/

/-- **(i-a)** `N_{1k}` is Lipschitz in `A₁` for the Frobenius norm, with constant `1/√n`. -/
theorem N1_lip (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (A₁ A₁' : Matrix (Fin (mA n)) (Fin n) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) :
    |N1 k A₁ c τ - N1 k A₁' c τ| ≤
      1 / √(n : ℝ) * √(∑ i, ∑ j, (A₁ i j - A₁' i j) ^ 2) := by
  have hp : (1 : ℝ≥0∞) ≤ (k : ℝ≥0∞) := by exact_mod_cast hk
  refine (abs_lpNorm_sub_le hp (memLp_sq1_sub hn A₁ c τ _) (memLp_sq1_sub hn A₁' c τ _)).trans ?_
  have h := lpNorm_le_mul (μ := stdGauss (Fin n)) (p := (k : ℝ≥0∞))
    (f := (fun ξ => sq1 A₁ c τ ξ - 1) - (fun ξ => sq1 A₁' c τ ξ - 1)) (ℓ := fun _ => (1 : ℝ))
    (memLp_const 1) (D := 1 / √(n : ℝ) * √(∑ i, ∑ j, (A₁ i j - A₁' i j) ^ 2))
    (by positivity) (fun ξ => by
      have e : ((fun ξ => sq1 A₁ c τ ξ - 1) - (fun ξ => sq1 A₁' c τ ξ - 1)) ξ =
          (nrm (reluV (A₁ *ᵥ sphPt (c + τ • ξ))) - nrm (reluV (A₁' *ᵥ sphPt (c + τ • ξ)))) /
            √(n : ℝ) := by
        simp only [Pi.sub_apply, sq1]; ring
      rw [e, abs_div, abs_of_nonneg (Real.sqrt_nonneg _), mul_one]
      have h1 := abs_layer_sub_le A₁ A₁' (sphPt (c + τ • ξ))
      rw [nrm_sphPt hn, mul_one] at h1
      calc _ ≤ √(∑ i, ∑ j, (A₁ i j - A₁' i j) ^ 2) / √(n : ℝ) :=
            div_le_div_of_nonneg_right h1 (Real.sqrt_nonneg _)
        _ = _ := by ring)
  rwa [lpNorm_const_prob hk, abs_one, mul_one] at h

/-- **(i-b)** The event `E_{N1k}`: `Pr(N_{1k} > E N_{1k} + 2√L_c/n) ≤ exp(−L_c)`. -/
theorem N1_event (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (c : Fin n → ℝ) (τ : ℝ) {Lc : ℝ}
    (hLc : 0 ≤ Lc) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      {A₁ | ∫ A₁, N1 k A₁ c τ ∂gaussMat (mA n) n (2 / (n : ℝ)) + 2 * √Lc / n < N1 k A₁ c τ} ≤
      Real.exp (-Lc) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := conc_upper_strict (g := fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ => N1 k A₁ c τ)
    (L := 1 / √(n : ℝ)) (by positivity) (fun M M' => N1_lip hn hk M M' c τ)
    (v := 2 / (n : ℝ)) (by positivity) hLc
  have e : √(2 * Lc * (2 / (n : ℝ))) * (1 / √(n : ℝ)) = 2 * √Lc / n := by
    rw [conc_const hLc, div_mul_div_comm, mul_one, Real.mul_self_sqrt hn0.le]
  rwa [e] at h

/-- The deviation of the normalized norm of one layer of width `m_A`, second moment. -/
lemma devA2 (hn : 1 ≤ n) {k : ℕ} {v : ℝ} (hv : 0 < v) {a : Fin k → ℝ} (ha : 0 < normSq a)
    {s : ℝ} (hs : s = √(((mA n : ℕ) : ℝ) / 2 * (v * normSq a))) :
    Integrable (fun M : Matrix (Fin (mA n)) (Fin k) ℝ => |nrm (reluV (M *ᵥ a)) / s - 1| ^ 2)
      (gaussMat (mA n) k v) ∧
    ∫ M, |nrm (reluV (M *ᵥ a)) / s - 1| ^ 2 ∂gaussMat (mA n) k v ≤ (√5 / (n : ℝ)) ^ 2 := by
  subst hs
  simp only [sq_abs]
  obtain ⟨hi, hb⟩ := relu_norm_dev2 (one_le_mA hn) hv ha
  refine ⟨hi, hb.trans (le_of_eq ?_)⟩
  rw [mA_cast, div_pow, Real.sq_sqrt (by norm_num)]

/-- The deviation of the normalized norm of one layer of width `m_A`, fourth moment. -/
lemma devA4 (hn : 1 ≤ n) {k : ℕ} {v : ℝ} (hv : 0 < v) {a : Fin k → ℝ} (ha : 0 < normSq a)
    {s : ℝ} (hs : s = √(((mA n : ℕ) : ℝ) / 2 * (v * normSq a))) :
    Integrable (fun M : Matrix (Fin (mA n)) (Fin k) ℝ => |nrm (reluV (M *ᵥ a)) / s - 1| ^ 4)
      (gaussMat (mA n) k v) ∧
    ∫ M, |nrm (reluV (M *ᵥ a)) / s - 1| ^ 4 ∂gaussMat (mA n) k v ≤ (x4n n / (n : ℝ)) ^ 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  subst hs
  have e4 : ∀ x : ℝ, |x| ^ 4 = x ^ 4 := fun x => by
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  simp only [e4]
  obtain ⟨hi, hb⟩ := relu_norm_dev4 (one_le_mA hn) hv ha
  refine ⟨hi, hb.trans (le_of_eq ?_)⟩
  rw [mA_cast, div_pow, x4n_pow]
  field_simp

/-- The mean of `N_{1k}` from a bound for one fixed unit input. -/
theorem N1_mean_gen (hn : 1 ≤ n) {k : ℕ} (hk : k ≠ 0) (c : Fin n → ℝ) (τ : ℝ) {κ : ℝ}
    (hκ : 0 ≤ κ)
    (hdev : ∀ a : Fin n → ℝ, normSq a = 1 →
      Integrable (fun M : Matrix (Fin (mA n)) (Fin n) ℝ =>
        |nrm (reluV (M *ᵥ a)) / √(n : ℝ) - 1| ^ k) (gaussMat (mA n) n (2 / (n : ℝ))) ∧
      ∫ M, |nrm (reluV (M *ᵥ a)) / √(n : ℝ) - 1| ^ k ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤ κ ^ k) :
    Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ => N1 k A₁ c τ) ∧
    Integrable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ => N1 k A₁ c τ)
      (gaussMat (mA n) n (2 / (n : ℝ))) ∧
    ∫ A₁, N1 k A₁ c τ ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤ κ := by
  refine mean_lpNorm_le (ν := gaussMat (mA n) n (2 / (n : ℝ))) (μ := stdGauss (Fin n)) hk
    (G := fun A₁ ξ => sq1 A₁ c τ ξ - 1) ((measurable_sq1_joint c τ).sub_const 1)
    (fun A₁ => memLp_sq1_sub hn A₁ c τ _) (b := fun _ => κ ^ k) (fun ξ => ?_) hκ ?_
  · obtain ⟨hi, hb⟩ := hdev (sphPt (c + τ • ξ)) (normSq_sphPt hn _)
    change ∫⁻ M : Matrix (Fin (mA n)) (Fin n) ℝ, ENNReal.ofReal
      (|nrm (reluV (M *ᵥ sphPt (c + τ • ξ))) / √(n : ℝ) - 1| ^ k)
        ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => by
      positivity)]
    exact ENNReal.ofReal_le_ofReal hb
  · simp

lemma dev_unit (hn : 1 ≤ n) {a : Fin n → ℝ} (ha : normSq a = 1) :
    √(n : ℝ) = √(((mA n : ℕ) : ℝ) / 2 * (2 / (n : ℝ) * normSq a)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [ha, mA_cast]
  congr 1
  field_simp

/-- **(i-c)** `E N₁₂ ≤ √5/n`. -/
theorem N1_mean2 (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) :
    ∫ A₁, N1 2 A₁ c τ ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤ √5 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  exact (N1_mean_gen hn (by norm_num) c τ (by positivity) fun a ha =>
    devA2 hn (by positivity) (by rw [ha]; norm_num) (dev_unit hn ha)).2.2

/-- **(i-c)** `E N₁₄ ≤ x₄(n)/n`. -/
theorem N1_mean4 (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) :
    ∫ A₁, N1 4 A₁ c τ ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤ x4n n / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  exact (N1_mean_gen hn (by norm_num) c τ (div_nonneg (x4n_nonneg n) hn0.le) fun a ha =>
    devA4 hn (by positivity) (by rw [ha]; norm_num) (dev_unit hn ha)).2.2

/-- **(i-d)** `Pr(N₁₂ > N̄₁₂) ≤ exp(−L_c)`. -/
theorem N12_event (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) {Lc : ℝ} (hLc : 0 ≤ Lc) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real {A₁ | N12bar n Lc < N1 2 A₁ c τ} ≤
      Real.exp (-Lc) := by
  refine le_trans (measureReal_mono (fun A₁ hA => ?_)) (N1_event hn (k := 2) (by norm_num) c τ hLc)
  simp only [mem_ofPred_eq] at hA ⊢
  have h := N1_mean2 hn c τ
  have e : N12bar n Lc = √5 / n + 2 * √Lc / n := by unfold N12bar; ring
  linarith

/-- **(i-d)** `Pr(N₁₄ > N̄₁₄) ≤ exp(−L_c)`. -/
theorem N14_event (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) {Lc : ℝ} (hLc : 0 ≤ Lc) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real {A₁ | N14bar n Lc < N1 4 A₁ c τ} ≤
      Real.exp (-Lc) := by
  refine le_trans (measureReal_mono (fun A₁ hA => ?_)) (N1_event hn (k := 4) (by norm_num) c τ hLc)
  simp only [mem_ofPred_eq] at hA ⊢
  have h := N1_mean4 hn c τ
  have e : N14bar n Lc = x4n n / n + 2 * √Lc / n := by unfold N14bar; ring
  linarith

/-! ## (ii) The second layer: fix `A₁`, integrate `A₂` -/

/-- **(ii-a)** `N_{2k}` is Lipschitz in `A₂` for the Frobenius norm, with constant
`‖√ω₁‖_{L^k(x)}`. -/
theorem N2_lip (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ A₂' : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    |N2 k A₁ A₂ c τ - N2 k A₁ A₂' c τ| ≤
      lpNorm (sq1 A₁ c τ) (k : ℝ≥0∞) (stdGauss (Fin n)) *
        √(∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) := by
  have hp : (1 : ℝ≥0∞) ≤ (k : ℝ≥0∞) := by exact_mod_cast hk
  refine (abs_lpNorm_sub_le hp (memLp_sq2_sub hn A₁ A₂ c τ _)
    (memLp_sq2_sub hn A₁ A₂' c τ _)).trans ?_
  have h := lpNorm_le_mul (μ := stdGauss (Fin n)) (p := (k : ℝ≥0∞))
    (f := (fun ξ => sq2 A₁ A₂ c τ ξ - 1) - (fun ξ => sq2 A₁ A₂' c τ ξ - 1)) (ℓ := sq1 A₁ c τ)
    (memLp_sq1 hn A₁ c τ _) (D := √(∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2))
    (Real.sqrt_nonneg _) (fun ξ => by
      have e : ((fun ξ => sq2 A₁ A₂ c τ ξ - 1) - (fun ξ => sq2 A₁ A₂' c τ ξ - 1)) ξ =
          (nrm (reluV (A₂ *ᵥ reluV (A₁ *ᵥ sphPt (c + τ • ξ)))) -
            nrm (reluV (A₂' *ᵥ reluV (A₁ *ᵥ sphPt (c + τ • ξ))))) / √(n : ℝ) := by
        simp only [Pi.sub_apply, sq2]; ring
      rw [e, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
      have h1 := abs_layer_sub_le A₂ A₂' (reluV (A₁ *ᵥ sphPt (c + τ • ξ)))
      calc _ ≤ √(∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) * nrm (reluV (A₁ *ᵥ sphPt (c + τ • ξ))) /
              √(n : ℝ) := div_le_div_of_nonneg_right h1 (Real.sqrt_nonneg _)
        _ = _ := by unfold sq1; ring)
  linarith [mul_comm (√(∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2))
    (lpNorm (sq1 A₁ c τ) (k : ℝ≥0∞) (stdGauss (Fin n)))]

/-- **(ii-a)** `‖√ω₁‖_{L^k} ≤ 1 + N_{1k}`. -/
theorem lpNorm_sq1_le_one_add (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    lpNorm (sq1 A₁ c τ) (k : ℝ≥0∞) (stdGauss (Fin n)) ≤ 1 + N1 k A₁ c τ :=
  lpNorm_le_one_add hk (memLp_sq1_sub hn A₁ c τ _)

/-- **(ii-a)** `‖√ω₁‖_{L^k} ≤ ‖A₁‖_op/√n`. -/
theorem lpNorm_sq1_le_opN (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    lpNorm (sq1 A₁ c τ) (k : ℝ≥0∞) (stdGauss (Fin n)) ≤ opN A₁ / √(n : ℝ) := by
  have h := lpNorm_le_mul (μ := stdGauss (Fin n)) (p := (k : ℝ≥0∞)) (f := sq1 A₁ c τ)
    (ℓ := fun _ => (1 : ℝ)) (memLp_const 1) (D := opN A₁ / √(n : ℝ))
    (div_nonneg (opN_nonneg _) (Real.sqrt_nonneg _)) (fun ξ => by
      rw [abs_of_nonneg (sq1_nonneg _ _ _ _), mul_one]; exact sq1_le_opN hn A₁ c τ ξ)
  rwa [lpNorm_const_prob hk, abs_one, mul_one] at h

/-- **(ii-b)** The event `E_{N22}`:
`Pr(N₂₂ > E[N₂₂ | A₁] + 2√L_c(1 + N₁₂)/n) ≤ exp(−L_c)`. -/
theorem N22_event (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    {Lc : ℝ} (hLc : 0 ≤ Lc) :
    (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))).real
      {A₂ | ∫ A₂, N2 2 A₁ A₂ c τ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) +
        2 * √Lc * (1 + N1 2 A₁ c τ) / n < N2 2 A₁ A₂ c τ} ≤ Real.exp (-Lc) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by rw [mA_cast]; positivity
  have h := conc_upper_strict
    (g := fun A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ => N2 2 A₁ A₂ c τ)
    (L := 1 + N1 2 A₁ c τ) (add_nonneg zero_le_one (N1_nonneg _ _ _ _))
    (fun M M' => (N2_lip hn (by norm_num) A₁ M M' c τ).trans
      (mul_le_mul_of_nonneg_right (lpNorm_sq1_le_one_add hn (by norm_num) A₁ c τ)
        (Real.sqrt_nonneg _)))
    (v := 2 / ((mA n : ℕ) : ℝ)) (by positivity) hLc
  have e : √(2 * Lc * (2 / ((mA n : ℕ) : ℝ))) * (1 + N1 2 A₁ c τ) =
      2 * √Lc * (1 + N1 2 A₁ c τ) / n := by
    rw [conc_const hLc, sqrt_mA]; ring
  rwa [e] at h

/-- **(ii-b)** The event `E_{N24}`:
`Pr(N₂₄ > E[N₂₄ | A₁] + √(2L_c)·ℓ₂₄) ≤ exp(−L_c)`, `ℓ₂₄ = √t_A·‖A₁‖_op/√n`. -/
theorem N24_event (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    {Lc : ℝ} (hLc : 0 ≤ Lc) :
    (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))).real
      {A₂ | ∫ A₂, N2 4 A₁ A₂ c τ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) +
        √(2 * Lc) * (√(2 / ((mA n : ℕ) : ℝ)) * opN A₁ / √(n : ℝ)) < N2 4 A₁ A₂ c τ} ≤
      Real.exp (-Lc) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by rw [mA_cast]; positivity
  have h := conc_upper_strict
    (g := fun A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ => N2 4 A₁ A₂ c τ)
    (L := opN A₁ / √(n : ℝ)) (div_nonneg (opN_nonneg _) (Real.sqrt_nonneg _))
    (fun M M' => (N2_lip hn (by norm_num) A₁ M M' c τ).trans
      (mul_le_mul_of_nonneg_right (lpNorm_sq1_le_opN hn (by norm_num) A₁ c τ)
        (Real.sqrt_nonneg _)))
    (v := 2 / ((mA n : ℕ) : ℝ)) (by positivity) hLc
  have e : √(2 * Lc * (2 / ((mA n : ℕ) : ℝ))) * (opN A₁ / √(n : ℝ)) =
      √(2 * Lc) * (√(2 / ((mA n : ℕ) : ℝ)) * opN A₁ / √(n : ℝ)) := by
    rw [Real.sqrt_mul (by positivity)]; ring
  rwa [e] at h

end BstLean.Part153

#print axioms BstLean.Part153.x4n_le
#print axioms BstLean.Part153.N1_lip
#print axioms BstLean.Part153.N1_event
#print axioms BstLean.Part153.N1_mean2
#print axioms BstLean.Part153.N1_mean4
#print axioms BstLean.Part153.N12_event
#print axioms BstLean.Part153.N14_event
#print axioms BstLean.Part153.N2_lip
#print axioms BstLean.Part153.lpNorm_sq1_le_one_add
#print axioms BstLean.Part153.lpNorm_sq1_le_opN
#print axioms BstLean.Part153.N22_event
#print axioms BstLean.Part153.N24_event
