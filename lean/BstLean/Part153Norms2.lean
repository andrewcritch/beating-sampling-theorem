import BstLean.Part153Norms

/-!
# Part 153: norms of the hidden vectors over the stand-in input (Lemma N), second file

Paper source: `proofs/option-n/theorem5-07-norms.tex`, Lemma N (ii) and (iii). Definitions and
items (i), (ii-a), (ii-b) are in `Part153Norms.lean`.

* (ii-c) `N2_mean2`: `E[N₂₂ | A₁] ≤ (1 + N₁₂)·√5/n + N₁₂`;
  `N2_mean4`: `E[N₂₄ | A₁] ≤ (1 + N₁₄)·x₄(n)/n + N₁₄`.
* (ii-d) `N22_le_bar`: `N₂₂ ≤ N̄₂₂` on `E_{N12} ∩ E_{N22}`;
  `N24_le_bar`: `N₂₄ ≤ N̄₂₄` on `E_op ∩ E_{N14} ∩ E_{N24}`.
* (iii) `int_sq2_sq_le`: `E_x ω₂ ≤ (1 + N₂₂)²`;
  `int_abs_sq2_sq_sub_one_le`: `E_x|ω₂ − 1| ≤ N₂₂(2 + N₂₂)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open scoped ENNReal NNReal

variable {n : ℕ}

/-! ## (ii-c) The conditional means of `N₂₂` and `N₂₄` -/

/-- `E_x (√ω₁)^k = ‖√ω₁‖_{L^k}^k`. -/
lemma int_sq1_pow (hn : 1 ≤ n) {k : ℕ} (hk : k ≠ 0) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (fun ξ => sq1 A₁ c τ ξ ^ k) (stdGauss (Fin n)) ∧
    ∫ ξ, sq1 A₁ c τ ξ ^ k ∂stdGauss (Fin n) =
      lpNorm (sq1 A₁ c τ) (k : ℝ≥0∞) (stdGauss (Fin n)) ^ k := by
  constructor
  · refine memLp_one_iff_integrable.mp (MemLp.of_bound
      ((measurable_sq1 A₁ c τ).pow_const k).aestronglyMeasurable ((opN A₁ / √(n : ℝ)) ^ k)
      (Filter.Eventually.of_forall fun ξ => ?_))
    rw [Real.norm_of_nonneg (pow_nonneg (sq1_nonneg _ _ _ _) k)]
    exact pow_le_pow_left₀ (sq1_nonneg _ _ _ _) (sq1_le_opN hn A₁ c τ ξ) k
  · rw [lpNorm_nat_pow hk (measurable_sq1 A₁ c τ).aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => by
      simp only [abs_of_nonneg (sq1_nonneg A₁ c τ ξ)])

lemma vec_zero_of_normSq {ι : Type*} [Fintype ι] {a : ι → ℝ} (h : normSq a = 0) : a = 0 := by
  funext i
  have h1 : a i ^ 2 ≤ normSq a :=
    Finset.single_le_sum (f := fun i => a i ^ 2) (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)
  rw [h] at h1
  exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm h1 (sq_nonneg _))

/-- The mean of `N_{2k}` over `A₂`, from a bound for one fixed nonzero input. -/
theorem N2_mean_gen (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hdev : ∀ a : Fin (mA n) → ℝ, 0 < normSq a →
      Integrable (fun M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
        |nrm (reluV (M *ᵥ a)) / nrm a - 1| ^ k)
        (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) ∧
      ∫ M, |nrm (reluV (M *ᵥ a)) / nrm a - 1| ^ k
        ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤ κ ^ k) :
    ∫ A₂, N2 k A₁ A₂ c τ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤
      (1 + N1 k A₁ c τ) * κ + N1 k A₁ c τ := by
  have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  have hN1 : 0 ≤ N1 k A₁ c τ := N1_nonneg _ _ _ _
  set ν := gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) with hν
  have hmem : ∀ A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ,
      MemLp (fun ξ => sq2 A₁ A₂ c τ ξ - sq1 A₁ c τ ξ) (k : ℝ≥0∞) (stdGauss (Fin n)) :=
    fun A₂ => (memLp_sq2 hn A₁ A₂ c τ _).sub (memLp_sq1 hn A₁ c τ _)
  have hjoint : Measurable (Function.uncurry
      (fun (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (ξ : Fin n → ℝ) =>
        sq2 A₁ A₂ c τ ξ - sq1 A₁ c τ ξ)) :=
    (measurable_sq2_joint A₁ c τ).sub ((measurable_sq1 A₁ c τ).comp measurable_snd)
  obtain ⟨-, hDi, hDb⟩ := mean_lpNorm_le (ν := ν) (μ := stdGauss (Fin n)) hk0
    (G := fun A₂ ξ => sq2 A₁ A₂ c τ ξ - sq1 A₁ c τ ξ) hjoint hmem
    (b := fun ξ => sq1 A₁ c τ ξ ^ k * κ ^ k) (fun ξ => by
      change ∫⁻ M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ, ENNReal.ofReal
        (|sq2 A₁ M c τ ξ - sq1 A₁ c τ ξ| ^ k) ∂ν ≤ ENNReal.ofReal (sq1 A₁ c τ ξ ^ k * κ ^ k)
      set a : Fin (mA n) → ℝ := reluV (A₁ *ᵥ sphPt (c + τ • ξ)) with ha
      have hs1 : sq1 A₁ c τ ξ = nrm a / √(n : ℝ) := rfl
      have hs2 : ∀ M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ,
          sq2 A₁ M c τ ξ = nrm (reluV (M *ᵥ a)) / √(n : ℝ) := fun M => rfl
      rcases (normSq_nonneg a).eq_or_lt with h0 | hpos
      · have ha0 : a = 0 := vec_zero_of_normSq h0.symm
        have e : ∀ M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ,
            |sq2 A₁ M c τ ξ - sq1 A₁ c τ ξ| ^ k = 0 := by
          intro M
          have h1 : nrm (reluV (M *ᵥ a)) = 0 := by
            have := nrm_layer_le M a
            rw [ha0] at this ⊢
            have hz : nrm (0 : Fin (mA n) → ℝ) = 0 := by simp [nrm, normSq]
            rw [hz, mul_zero] at this
            exact le_antisymm this (nrm_nonneg _)
          have h2 : nrm a = 0 := by rw [ha0]; simp [nrm, normSq]
          rw [hs1, hs2, h1, h2]
          simp [hk0]
        simp only [e]
        simp
      · have hna : 0 < nrm a := Real.sqrt_pos.mpr hpos
        obtain ⟨hi, hb⟩ := hdev a hpos
        have e : ∀ M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ,
            |sq2 A₁ M c τ ξ - sq1 A₁ c τ ξ| ^ k =
              sq1 A₁ c τ ξ ^ k * |nrm (reluV (M *ᵥ a)) / nrm a - 1| ^ k := by
          intro M
          have e1 : sq2 A₁ M c τ ξ - sq1 A₁ c τ ξ =
              sq1 A₁ c τ ξ * (nrm (reluV (M *ᵥ a)) / nrm a - 1) := by
            rw [hs1, hs2]; field_simp
          rw [e1, abs_mul, abs_of_nonneg (sq1_nonneg _ _ _ _), mul_pow]
        simp only [e]
        rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul _)
          (Filter.Eventually.of_forall fun _ =>
            mul_nonneg (pow_nonneg (sq1_nonneg _ _ _ _) k) (by positivity)),
          integral_const_mul]
        exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left hb (pow_nonneg (sq1_nonneg _ _ _ _) k)))
    (C := (1 + N1 k A₁ c τ) * κ) (mul_nonneg (by linarith) hκ) (by
      obtain ⟨hi, he⟩ := int_sq1_pow hn hk0 A₁ c τ
      rw [← ofReal_integral_eq_lintegral_ofReal (hi.mul_const _)
        (Filter.Eventually.of_forall fun _ =>
          mul_nonneg (pow_nonneg (sq1_nonneg _ _ _ _) k) (pow_nonneg hκ k)),
        integral_mul_const, he, mul_pow]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ lpNorm_nonneg (lpNorm_sq1_le_one_add hn hk A₁ c τ) k)
        (pow_nonneg hκ k)))
  have hpt : ∀ A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ, N2 k A₁ A₂ c τ ≤
      lpNorm (fun ξ => sq2 A₁ A₂ c τ ξ - sq1 A₁ c τ ξ) (k : ℝ≥0∞) (stdGauss (Fin n)) +
        N1 k A₁ c τ := by
    intro A₂
    have h := lpNorm_add_le (g := fun ξ => sq1 A₁ c τ ξ - 1) (hmem A₂)
      (by exact_mod_cast hk : (1 : ℝ≥0∞) ≤ (k : ℝ≥0∞))
    have e : (fun ξ => sq2 A₁ A₂ c τ ξ - sq1 A₁ c τ ξ) + (fun ξ => sq1 A₁ c τ ξ - 1) =
        fun ξ => sq2 A₁ A₂ c τ ξ - 1 := by funext ξ; simp
    rw [e] at h
    exact h
  have h1 := integral_mono_of_nonneg (μ := ν)
    (Filter.Eventually.of_forall fun A₂ => N2_nonneg k A₁ A₂ c τ)
    (hDi.add (integrable_const (N1 k A₁ c τ))) (Filter.Eventually.of_forall hpt)
  simp only [Pi.add_apply] at h1
  rw [integral_add hDi (integrable_const _), integral_const, probReal_univ, one_smul] at h1
  linarith

lemma dev_self (hn : 1 ≤ n) (a : Fin (mA n) → ℝ) :
    nrm a = √(((mA n : ℕ) : ℝ) / 2 * (2 / ((mA n : ℕ) : ℝ) * normSq a)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by rw [mA_cast]; positivity
  unfold nrm
  congr 1
  field_simp

/-- **(ii-c)** `E[N₂₂ | A₁] ≤ (1 + N₁₂)·√5/n + N₁₂`. -/
theorem N2_mean2 (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    ∫ A₂, N2 2 A₁ A₂ c τ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤
      (1 + N1 2 A₁ c τ) * √5 / n + N1 2 A₁ c τ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by rw [mA_cast]; positivity
  have h := N2_mean_gen hn (k := 2) (by norm_num) A₁ c τ (κ := √5 / n) (by positivity)
    fun a ha => devA2 hn (by positivity) ha (dev_self hn a)
  rwa [← mul_div_assoc] at h

/-- **(ii-c)** `E[N₂₄ | A₁] ≤ (1 + N₁₄)·x₄(n)/n + N₁₄`. -/
theorem N2_mean4 (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    ∫ A₂, N2 4 A₁ A₂ c τ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤
      (1 + N1 4 A₁ c τ) * x4n n / n + N1 4 A₁ c τ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by rw [mA_cast]; positivity
  have h := N2_mean_gen hn (k := 4) (by norm_num) A₁ c τ (κ := x4n n / n)
    (div_nonneg (x4n_nonneg n) hn0.le)
    fun a ha => devA4 hn (by positivity) ha (dev_self hn a)
  rwa [← mul_div_assoc] at h

/-! ## (ii-d) The deterministic consequences on the events -/

lemma N12bar_nonneg (n : ℕ) (Lc : ℝ) : 0 ≤ N12bar n Lc := by unfold N12bar; positivity

lemma N14bar_nonneg (n : ℕ) (Lc : ℝ) : 0 ≤ N14bar n Lc :=
  div_nonneg (add_nonneg (x4n_nonneg n) (by positivity)) (Nat.cast_nonneg n)

/-- **(ii-d)** On `E_{N12} ∩ E_{N22}`: `N₂₂ ≤ N̄₂₂`. -/
theorem N22_le_bar (hn : 1 ≤ n) {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ}
    {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ} {c : Fin n → ℝ} {τ : ℝ} {Lc : ℝ}
    (h1 : N1 2 A₁ c τ ≤ N12bar n Lc)
    (h2 : A₂ ∉ {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      ∫ A₂, N2 2 A₁ A₂ c τ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) +
        2 * √Lc * (1 + N1 2 A₁ c τ) / n < N2 2 A₁ A₂ c τ}) :
    N2 2 A₁ A₂ c τ ≤ N22bar n Lc := by
  simp only [mem_ofPred_eq, not_lt] at h2
  have h3 := N2_mean2 hn A₁ c τ
  have hb := N12bar_nonneg n Lc
  have h0 := N1_nonneg 2 A₁ c τ
  have e : (1 + N1 2 A₁ c τ) * √5 / n + N1 2 A₁ c τ + 2 * √Lc * (1 + N1 2 A₁ c τ) / n =
      (1 + N1 2 A₁ c τ) * N12bar n Lc + N1 2 A₁ c τ := by unfold N12bar; ring
  unfold N22bar
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) hb]

/-- **(ii-d)** On `E_op ∩ E_{N14} ∩ E_{N24}`: `N₂₄ ≤ N̄₂₄`. -/
theorem N24_le_bar (hn : 1 ≤ n) {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ}
    {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ} {c : Fin n → ℝ} {τ : ℝ} {Lc : ℝ} (hLc : 0 ≤ Lc)
    (hA : A₁ ∈ Eop n) (h1 : N1 4 A₁ c τ ≤ N14bar n Lc)
    (h2 : A₂ ∉ {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      ∫ A₂, N2 4 A₁ A₂ c τ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) +
        √(2 * Lc) * (√(2 / ((mA n : ℕ) : ℝ)) * opN A₁ / √(n : ℝ)) < N2 4 A₁ A₂ c τ}) :
    N2 4 A₁ A₂ c τ ≤ N24bar n Lc := by
  simp only [mem_ofPred_eq, not_lt] at h2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  have hm0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by rw [mA_cast]; positivity
  have hw : 0 ≤ wn n := sq_nonneg _
  have h3 := N2_mean4 hn A₁ c τ
  have hx := x4n_nonneg n
  have hℓ1 : √(2 / ((mA n : ℕ) : ℝ)) * opN A₁ ≤ 2 * √(wn n) / √(n : ℝ) := by
    have e : √(2 / ((mA n : ℕ) : ℝ)) * opN A₁ = √(2 / ((mA n : ℕ) : ℝ) * opN A₁ ^ 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (opN_nonneg _)]
    rw [e]
    refine (Real.sqrt_le_sqrt (Eop_sq hn hA)).trans (le_of_eq ?_)
    rw [Real.sqrt_div (mul_nonneg (by norm_num) hw), show (4 : ℝ) * wn n = 2 ^ 2 * wn n by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hℓ : √(2 / ((mA n : ℕ) : ℝ)) * opN A₁ / √(n : ℝ) ≤ 2 * √(wn n) / n := by
    refine (div_le_div_of_nonneg_right hℓ1 hsn.le).trans (le_of_eq ?_)
    rw [div_div, Real.mul_self_sqrt hn0.le]
  have h4 : √(2 * Lc) * (√(2 / ((mA n : ℕ) : ℝ)) * opN A₁ / √(n : ℝ)) ≤
      2 * √(2 * Lc * wn n) / n := by
    refine (mul_le_mul_of_nonneg_left hℓ (Real.sqrt_nonneg _)).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity) (wn n)]
    ring
  have h5 : (1 + N1 4 A₁ c τ) * x4n n / n ≤ x4n n * (1 + N14bar n Lc) / n := by
    rw [mul_comm]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hx) hn0.le
  unfold N24bar
  linarith

/-! ## (iii) The moments of `ω₂` -/

/-- `‖√ω₂‖_{L²} ≤ 1 + N₂₂`. -/
lemma lpNorm_sq2_le (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    lpNorm (sq2 A₁ A₂ c τ) ((2 : ℕ) : ℝ≥0∞) (stdGauss (Fin n)) ≤ 1 + N2 2 A₁ A₂ c τ :=
  lpNorm_le_one_add (by norm_num) (memLp_sq2_sub hn A₁ A₂ c τ _)

/-- **(iii)** `E_x ω₂ ≤ (1 + N₂₂)²`. -/
theorem int_sq2_sq_le (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    ∫ ξ, sq2 A₁ A₂ c τ ξ ^ 2 ∂stdGauss (Fin n) ≤ (1 + N2 2 A₁ A₂ c τ) ^ 2 := by
  have e : ∫ ξ, sq2 A₁ A₂ c τ ξ ^ 2 ∂stdGauss (Fin n) =
      lpNorm (sq2 A₁ A₂ c τ) ((2 : ℕ) : ℝ≥0∞) (stdGauss (Fin n)) ^ 2 := by
    rw [lpNorm_nat_pow (by norm_num) (measurable_sq2 A₁ A₂ c τ).aestronglyMeasurable]
    simp only [sq_abs]
  rw [e]
  exact pow_le_pow_left₀ lpNorm_nonneg (lpNorm_sq2_le hn A₁ A₂ c τ) 2

/-- **(iii)** `E_x|ω₂ − 1| ≤ N₂₂(2 + N₂₂)`. -/
theorem int_abs_sq2_sq_sub_one_le (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    ∫ ξ, |sq2 A₁ A₂ c τ ξ ^ 2 - 1| ∂stdGauss (Fin n) ≤
      N2 2 A₁ A₂ c τ * (2 + N2 2 A₁ A₂ c τ) := by
  set μ := stdGauss (Fin n) with hμ
  have hm := measurable_sq2 A₁ A₂ c τ
  have hf : MemLp (fun ξ => |sq2 A₁ A₂ c τ ξ - 1|) (ENNReal.ofReal 2) μ :=
    (memLp_sq2_sub hn A₁ A₂ c τ _).abs
  have hg : MemLp (fun ξ => sq2 A₁ A₂ c τ ξ + 1) (ENNReal.ofReal 2) μ :=
    (memLp_sq2 hn A₁ A₂ c τ _).add (memLp_const 1)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun ξ => abs_nonneg (sq2 A₁ A₂ c τ ξ - 1))
    (Filter.Eventually.of_forall fun ξ => add_nonneg (sq2_nonneg A₁ A₂ c τ ξ) zero_le_one) hf hg
  have e0 : ∀ ξ, |sq2 A₁ A₂ c τ ξ ^ 2 - 1| = |sq2 A₁ A₂ c τ ξ - 1| * (sq2 A₁ A₂ c τ ξ + 1) := by
    intro ξ
    rw [show sq2 A₁ A₂ c τ ξ ^ 2 - 1 = (sq2 A₁ A₂ c τ ξ - 1) * (sq2 A₁ A₂ c τ ξ + 1) by ring,
      abs_mul, abs_of_nonneg (add_nonneg (sq2_nonneg A₁ A₂ c τ ξ) zero_le_one)]
  have e1 : (∫ ξ, |sq2 A₁ A₂ c τ ξ - 1| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = N2 2 A₁ A₂ c τ := by
    have := rpow_half_eq (μ := μ) (f := fun ξ => sq2 A₁ A₂ c τ ξ - 1)
      (hm.sub_const 1).aestronglyMeasurable
    exact this
  have e2 : (∫ ξ, (sq2 A₁ A₂ c τ ξ + 1) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) =
      lpNorm (fun ξ => sq2 A₁ A₂ c τ ξ + 1) ((2 : ℕ) : ℝ≥0∞) μ := by
    rw [← rpow_half_eq (hm.add_const 1).aestronglyMeasurable]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => by
      simp only [abs_of_nonneg (add_nonneg (sq2_nonneg A₁ A₂ c τ ξ) zero_le_one)])
  have h6 : lpNorm (fun ξ => sq2 A₁ A₂ c τ ξ + 1) ((2 : ℕ) : ℝ≥0∞) μ ≤
      2 + N2 2 A₁ A₂ c τ := by
    have h7 := lpNorm_add_le (μ := μ) (g := fun _ : Fin n → ℝ => (2 : ℝ))
      (memLp_sq2_sub hn A₁ A₂ c τ ((2 : ℕ) : ℝ≥0∞)) (by norm_num)
    have e : (fun ξ => sq2 A₁ A₂ c τ ξ - 1) + (fun _ : Fin n → ℝ => (2 : ℝ)) =
        fun ξ => sq2 A₁ A₂ c τ ξ + 1 := by funext ξ; simp only [Pi.add_apply]; ring
    rw [e, lpNorm_const_prob (by norm_num)] at h7
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h7
    unfold N2
    linarith
  simp only [e0]
  rw [e1, e2] at h
  exact h.trans (mul_le_mul_of_nonneg_left h6 (N2_nonneg _ _ _ _ _))

end BstLean.Part153

#print axioms BstLean.Part153.N2_mean2
#print axioms BstLean.Part153.N2_mean4
#print axioms BstLean.Part153.N22_le_bar
#print axioms BstLean.Part153.N24_le_bar
#print axioms BstLean.Part153.int_sq2_sq_le
#print axioms BstLean.Part153.int_abs_sq2_sq_sub_one_le
