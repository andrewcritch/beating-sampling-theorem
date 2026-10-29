import BstLean.Part160Lib
import BstLean.Part160Mass4

/-!
# Part 160 (file `Mass`): the lower tail of the residual energy from moments

Role: `delegations/statements/p160-spec.md`, items 2 and 4 (the mass bound).
Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-06-cutoff.tex` (the mass `β_d` of the inputs with a small residual energy). The
paper uses moments of order `320` and a fixed-pair derivative bound. This file uses only a
fourth moment of `σ = √t_A·|r|`, so the cutoff is weaker.

* `lower_tail_of_moments`: for `σ ≥ 0` with `E σ² ≥ L`, `Var σ ≤ V` and a tail bound
  `Pr(|σ − Eσ| ≥ g) ≤ T(g)`: `Pr(σ² < a²) ≤ T(s − a)` when `0 ≤ a < s`, `s² ≤ L − V`.
* `mass_bound_gen`: the mass of `{t_A|r|² < γ_A·sd²}` is at most `T(√γ_A·(s − sd))` when
  `s² ≤ 1 − N₂₂(2 + N₂₂) − (e₁ + e₂)² − 2N/n` (`e₁² ≥ e_b`, `e₂² ≥ ξ/n`).
* `mass_bound4`: with the fourth moment of `Part160Mass4`:
  `n·β_d ≤ (2a + √(4a² + N²))²/(n·(s − sd)⁴)`, `d = sd²`, `Ξ ≤ N γ_A/n`, `Ξ₄ ≤ a γ_A/n`.
* `Esig2_lower`: `t_A·E|r|² ≥ γ_A·(1 − E|ω₂ − 1|) − Ξ − t_A(|b| + |μ − b|)²`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part134 (lam res sig)
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm XiS Xi4 N2 sq2 hid2Mean_cr)

section abstract

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The lower tail of a nonnegative variable from three moments.** -/
theorem lower_tail_of_moments (μ : Measure Ω) [IsProbabilityMeasure μ] {σ : Ω → ℝ}
    (hσ0 : ∀ x, 0 ≤ σ x) (hi1 : Integrable σ μ) (hi2 : Integrable (fun x => σ x ^ 2) μ)
    {L V : ℝ} {T : ℝ → ℝ} (hL : L ≤ ∫ x, σ x ^ 2 ∂μ)
    (hV : ∫ x, (σ x - ∫ y, σ y ∂μ) ^ 2 ∂μ ≤ V)
    (hK : ∀ g : ℝ, 0 < g → μ.real {x | g ≤ |σ x - ∫ y, σ y ∂μ|} ≤ T g)
    {a s : ℝ} (ha : 0 ≤ a) (has : a < s) (hs : s ^ 2 ≤ L - V) :
    μ.real {x | σ x ^ 2 < a ^ 2} ≤ T (s - a) := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∫ y, σ y ∂μ := ⟨_, rfl⟩
  rw [← hM] at hV hK
  have hM0 : 0 ≤ M := by rw [hM]; exact integral_nonneg hσ0
  have hvar : ∫ x, (σ x - M) ^ 2 ∂μ = ∫ x, σ x ^ 2 ∂μ - M ^ 2 := by
    have i2 := hi1.const_mul (2 * M)
    have hA : ∫ x, (σ x ^ 2 - 2 * M * σ x + M ^ 2) ∂μ =
        ∫ x, (σ x ^ 2 - 2 * M * σ x) ∂μ + ∫ _x, M ^ 2 ∂μ :=
      integral_add (hi2.sub i2) (integrable_const _)
    have hB : ∫ x, (σ x ^ 2 - 2 * M * σ x) ∂μ = ∫ x, σ x ^ 2 ∂μ - ∫ x, 2 * M * σ x ∂μ :=
      integral_sub hi2 i2
    have e : (fun x => (σ x - M) ^ 2) = fun x => σ x ^ 2 - 2 * M * σ x + M ^ 2 :=
      funext fun x => by ring
    rw [e, hA, hB, integral_const_mul, ← hM, integral_const, probReal_univ, one_smul]
    ring
  have hM2 : s ^ 2 ≤ M ^ 2 := by linarith
  have hs0 : 0 < s := lt_of_le_of_lt ha has
  have hsM : s ≤ M := by
    by_contra hlt
    have hlt' : M < s := not_le.mp hlt
    have : M ^ 2 < s ^ 2 := pow_lt_pow_left₀ hlt' hM0 (by norm_num)
    linarith
  have hsub : {x | σ x ^ 2 < a ^ 2} ⊆ {x | s - a ≤ |σ x - M|} := by
    intro x hx
    have hx' : σ x ^ 2 < a ^ 2 := hx
    have h1 : σ x < a := lt_of_pow_lt_pow_left₀ 2 ha hx'
    show s - a ≤ |σ x - M|
    rw [abs_sub_comm]
    exact le_trans (by linarith) (le_abs_self _)
  exact (measureReal_mono hsub).trans (hK (s - a) (by linarith))

end abstract

variable {n : ℕ}

/-- `t_A·|h|² = γ_A·ω₂` with `√ω₂ = sq2`. -/
lemma t_normSq_hid2 (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) :
    2 / (mA n : ℝ) * normSq (hid2 A₁ A₂ (sphPt (c + τ • ξ))) =
      2 / (n : ℝ) * sq2 A₁ A₂ c τ ξ ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  rw [BstLean.Part153.sq2_eq_hid2, div_pow, BstLean.Part153.nrm_sq, Real.sq_sqrt hnR.le, hmR]
  field_simp

/-- **A lower bound of the mean residual energy**:
`t_A·E|r|² ≥ γ_A·(1 − E|ω₂ − 1|) − Ξ − t_A·(|b| + |μ − b|)²`. -/
theorem Esig2_lower (hn : 6 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {b : Fin (mA n) → ℝ} (hb : 0 < normSq b) :
    Integrable (fun ξ : Fin n → ℝ =>
      2 / (mA n : ℝ) * normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ))))) (stdGauss (Fin n)) ∧
    2 / (n : ℝ) * (1 - ∫ ξ, |sq2 A₁ A₂ c τ ξ ^ 2 - 1| ∂stdGauss (Fin n)) - XiS A₁ A₂ c τ -
        2 / (mA n : ℝ) * (nrm b + nrm (hid2Mean_cr A₁ A₂ c τ - b)) ^ 2 ≤
      ∫ ξ, 2 / (mA n : ℝ) * normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) ∂stdGauss (Fin n) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmR : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have hm0 : (0 : ℝ) < mA n := by rw [hmR]; positivity
  have ht0 : (0 : ℝ) ≤ 2 / (mA n : ℝ) := by positivity
  obtain ⟨t, htd⟩ : ∃ t : ℝ, t = 2 / (mA n : ℝ) := ⟨_, rfl⟩
  rw [← htd] at ht0 ⊢
  obtain ⟨mu, hmu⟩ : ∃ mu : Fin (mA n) → ℝ, mu = hid2Mean_cr A₁ A₂ c τ := ⟨_, rfl⟩
  rw [← hmu]
  -- the function `f = ⟨b, h⟩`
  obtain ⟨f, hf⟩ : ∃ f : (Fin n → ℝ) → ℝ,
      f = fun ξ => b ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) := ⟨_, rfl⟩
  obtain ⟨hfm, hfb⟩ := BstLean.Part153.dot_hid2_bdd_cr hn1 A₁ A₂ c τ b
  rw [← hf] at hfm
  have hfb' : ∀ ξ, |f ξ| ≤ nrm b * (opN A₂ * opN A₁) := fun ξ => by rw [hf]; exact hfb ξ
  have hfi : Integrable f (stdGauss (Fin n)) := by
    rw [hf]; exact BstLean.Part153.integrable_dot_hid2_cr hn1 A₁ A₂ c τ b
  have hf2 : Integrable (fun ξ => f ξ ^ 2) (stdGauss (Fin n)) :=
    Integrable.of_bound (hfm.pow_const 2).aestronglyMeasurable
      ((nrm b * (opN A₂ * opN A₁)) ^ 2) (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq' (by linarith [(abs_le.mp (hfb' ξ)).1]) (abs_le.mp (hfb' ξ)).2)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∫ ξ, f ξ ∂stdGauss (Fin n) := ⟨_, rfl⟩
  have hvar : ∫ ξ, (f ξ - M) ^ 2 ∂stdGauss (Fin n) =
      ∫ ξ, f ξ ^ 2 ∂stdGauss (Fin n) - M ^ 2 := by
    have i2 := hfi.const_mul (2 * M)
    have hA : ∫ x, (f x ^ 2 - 2 * M * f x + M ^ 2) ∂stdGauss (Fin n) =
        ∫ x, (f x ^ 2 - 2 * M * f x) ∂stdGauss (Fin n) + ∫ _x, M ^ 2 ∂stdGauss (Fin n) :=
      integral_add (hf2.sub i2) (integrable_const _)
    have hB : ∫ x, (f x ^ 2 - 2 * M * f x) ∂stdGauss (Fin n) =
        ∫ x, f x ^ 2 ∂stdGauss (Fin n) - ∫ x, 2 * M * f x ∂stdGauss (Fin n) :=
      integral_sub hf2 i2
    have e : (fun x => (f x - M) ^ 2) = fun x => f x ^ 2 - 2 * M * f x + M ^ 2 :=
      funext fun x => by ring
    rw [e, hA, hB, integral_const_mul, ← hM, integral_const, probReal_univ, one_smul]
    ring
  have hcov : t * ∫ ξ, (f ξ - M) ^ 2 ∂stdGauss (Fin n) ≤ XiS A₁ A₂ c τ * normSq b := by
    have := BstLean.Part153.cov_hid2_le hn A₁ A₂ c hτ b
    rw [hM, hf, htd]; exact this
  have hMe : M = b ⬝ᵥ mu := by
    rw [hM, hf, hmu, BstLean.Part153.integral_dot_hid2_cr hn1]
  -- `M² ≤ |b|²·(|b| + |μ − b|)²`
  have hM2 : M ^ 2 ≤ normSq b * (nrm b + nrm (mu - b)) ^ 2 := by
    have e : M = normSq b + b ⬝ᵥ (mu - b) := by
      rw [hMe, dotProduct_sub, BstLean.Part153.dot_self_cr]; ring
    have h1 := BstLean.Part153.abs_dot_le_nrm b (mu - b)
    have hb2 : normSq b = nrm b ^ 2 := (BstLean.Part153.nrm_sq b).symm
    have hnb := BstLean.Part153.nrm_nonneg b
    have hnd := BstLean.Part153.nrm_nonneg (mu - b)
    have h2 : |M| ≤ nrm b * (nrm b + nrm (mu - b)) := by
      rw [e, hb2]
      calc |nrm b ^ 2 + b ⬝ᵥ (mu - b)| ≤ |nrm b ^ 2| + |b ⬝ᵥ (mu - b)| := abs_add_le _ _
        _ ≤ nrm b ^ 2 + nrm b * nrm (mu - b) := by
            rw [abs_of_nonneg (sq_nonneg _)]; linarith
        _ = _ := by ring
    have h3 := pow_le_pow_left₀ (abs_nonneg M) h2 2
    rwa [sq_abs, mul_pow, ← hb2] at h3
  -- pointwise: `t|r|² = γ ω₂ − t f²/|b|²`
  have hpt : ∀ ξ, t * normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) =
      2 / (n : ℝ) * sq2 A₁ A₂ c τ ξ ^ 2 - t / normSq b * f ξ ^ 2 := by
    intro ξ
    rw [BstLean.Part136.normSq_res hb.ne', mul_sub, htd, t_normSq_hid2 hn1, hf]
    have e : ∑ j, hid2 A₁ A₂ (sphPt (c + τ • ξ)) j * b j =
        b ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) := by
      unfold dotProduct
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e]; ring
  have hsq2m := BstLean.Part153.measurable_sq2 A₁ A₂ c τ
  have hsq2b : ∀ ξ, |sq2 A₁ A₂ c τ ξ| ≤ opN A₂ * opN A₁ / √(n : ℝ) := by
    intro ξ
    rw [BstLean.Part153.sq2_eq_hid2,
      abs_of_nonneg (div_nonneg (BstLean.Part153.nrm_nonneg _) (Real.sqrt_nonneg _))]
    exact div_le_div_of_nonneg_right (BstLean.Part153.nrm_hid2_sph_le_cr hn1 A₁ A₂ _)
      (Real.sqrt_nonneg _)
  have hs2i : Integrable (fun ξ => sq2 A₁ A₂ c τ ξ ^ 2) (stdGauss (Fin n)) :=
    Integrable.of_bound (hsq2m.pow_const 2).aestronglyMeasurable
      ((opN A₂ * opN A₁ / √(n : ℝ)) ^ 2) (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq' (by linarith [(abs_le.mp (hsq2b ξ)).1]) (abs_le.mp (hsq2b ξ)).2)
  have hi : Integrable (fun ξ : Fin n → ℝ =>
      t * normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ))))) (stdGauss (Fin n)) := by
    simp_rw [hpt]
    exact (hs2i.const_mul _).sub (hf2.const_mul _)
  refine ⟨hi, ?_⟩
  simp_rw [hpt]
  rw [integral_sub (hs2i.const_mul _) (hf2.const_mul _), integral_const_mul, integral_const_mul]
  -- `∫ ω₂ ≥ 1 − ∫|ω₂ − 1|`
  have habs : Integrable (fun ξ => |sq2 A₁ A₂ c τ ξ ^ 2 - 1|) (stdGauss (Fin n)) :=
    (hs2i.sub (integrable_const 1)).abs
  have h1 : 1 - ∫ ξ, |sq2 A₁ A₂ c τ ξ ^ 2 - 1| ∂stdGauss (Fin n) ≤
      ∫ ξ, sq2 A₁ A₂ c τ ξ ^ 2 ∂stdGauss (Fin n) := by
    have : ∫ ξ, (1 - |sq2 A₁ A₂ c τ ξ ^ 2 - 1|) ∂stdGauss (Fin n) ≤
        ∫ ξ, sq2 A₁ A₂ c τ ξ ^ 2 ∂stdGauss (Fin n) :=
      integral_mono ((integrable_const 1).sub habs) hs2i fun ξ => by
        have := neg_abs_le (sq2 A₁ A₂ c τ ξ ^ 2 - 1)
        show 1 - |sq2 A₁ A₂ c τ ξ ^ 2 - 1| ≤ sq2 A₁ A₂ c τ ξ ^ 2
        linarith
    rwa [integral_sub (integrable_const 1) habs, integral_const, probReal_univ, one_smul] at this
  -- `(t/|b|²)·∫ f² ≤ Ξ + t(|b| + |μ − b|)²`
  have h2 : t / normSq b * ∫ ξ, f ξ ^ 2 ∂stdGauss (Fin n) ≤
      XiS A₁ A₂ c τ + t * (nrm b + nrm (mu - b)) ^ 2 := by
    have e : ∫ ξ, f ξ ^ 2 ∂stdGauss (Fin n) = ∫ ξ, (f ξ - M) ^ 2 ∂stdGauss (Fin n) + M ^ 2 := by
      rw [hvar]; ring
    rw [e, div_mul_eq_mul_div, div_le_iff₀ hb, mul_add]
    have : t * M ^ 2 ≤ t * (normSq b * (nrm b + nrm (mu - b)) ^ 2) :=
      mul_le_mul_of_nonneg_left hM2 ht0
    nlinarith
  have hγ : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hγ]

/-- **The moments of `σ = √t_A·|r|`**: `σ` and `σ²` are integrable, `E σ² ≥ L`, `Var σ ≤ N γ_A/n`
and `γ_A·s² ≤ L − N γ_A/n`, with `L = γ_A(1 − N22(2 + N22)) − N γ_A/n − γ_A(e₁ + e₂)²`, under the
hypotheses of `mass_bound_gen`. Consequently `γ_A·s² ≤ (E σ)²`. -/
theorem sigD_moments (hn : 6 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {b : Fin (mA n) → ℝ} (hb : 0 < normSq b) {N eb xi N22 e1 e2 s : ℝ}
    (hXi : XiS A₁ A₂ c τ ≤ N * (2 / (n : ℝ)) / n)
    (heb : 2 / (mA n : ℝ) * normSq b ≤ 2 / (n : ℝ) * eb)
    (hxi : 2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - b) ≤ xi * (2 / (n : ℝ)) / n)
    (hN22 : N2 2 A₁ A₂ c τ ≤ N22)
    (he1 : 0 ≤ e1) (he1' : eb ≤ e1 ^ 2) (he2 : 0 ≤ e2) (he2' : xi / n ≤ e2 ^ 2)
    (hs2 : s ^ 2 ≤ 1 - N22 * (2 + N22) - (e1 + e2) ^ 2 - 2 * N / n) :
    Integrable (sigD A₁ A₂ c τ b) (stdGauss (Fin n)) ∧
    Integrable (fun ξ => sigD A₁ A₂ c τ b ξ ^ 2) (stdGauss (Fin n)) ∧
    ∫ ξ, (sigD A₁ A₂ c τ b ξ - ∫ ζ, sigD A₁ A₂ c τ b ζ ∂stdGauss (Fin n)) ^ 2
      ∂stdGauss (Fin n) ≤ N * (2 / (n : ℝ)) / n ∧
    ∃ L : ℝ, L ≤ ∫ ξ, sigD A₁ A₂ c τ b ξ ^ 2 ∂stdGauss (Fin n) ∧
      (√(2 / (n : ℝ)) * s) ^ 2 ≤ L - N * (2 / (n : ℝ)) / n := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hγ : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hmR : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have hm0 : (0 : ℝ) < mA n := by rw [hmR]; positivity
  have ht0 : (0 : ℝ) ≤ 2 / (mA n : ℝ) := by positivity
  obtain ⟨g0, hg0⟩ : ∃ g0 : ℝ, g0 = √(2 / (n : ℝ)) := ⟨_, rfl⟩
  have hg0p : 0 < g0 := by rw [hg0]; exact Real.sqrt_pos.mpr hγ
  have hg02 : g0 ^ 2 = 2 / (n : ℝ) := by rw [hg0]; exact Real.sq_sqrt hγ.le
  obtain ⟨hi, hE⟩ := Esig2_lower hn A₁ A₂ c hτ hb
  have hN2nn := BstLean.Part153.N2_nonneg 2 A₁ A₂ c τ
  have hN22nn : 0 ≤ N22 := hN2nn.trans hN22
  have hω := BstLean.Part153.int_abs_sq2_sq_sub_one_le hn1 A₁ A₂ c τ
  have hω' : ∫ ξ, |sq2 A₁ A₂ c τ ξ ^ 2 - 1| ∂stdGauss (Fin n) ≤ N22 * (2 + N22) :=
    hω.trans (mul_le_mul hN22 (by linarith) (by linarith) hN22nn)
  -- `√t·|b| ≤ √γ·e₁`, `√t·|μ − b| ≤ √γ·e₂`
  obtain ⟨st, hst⟩ : ∃ st : ℝ, st = √(2 / (mA n : ℝ)) := ⟨_, rfl⟩
  have hst0 : 0 ≤ st := by rw [hst]; exact Real.sqrt_nonneg _
  have hst2 : st ^ 2 = 2 / (mA n : ℝ) := by rw [hst]; exact Real.sq_sqrt ht0
  have hnb := BstLean.Part153.nrm_nonneg b
  have hnd := BstLean.Part153.nrm_nonneg (hid2Mean_cr A₁ A₂ c τ - b)
  have hb1 : st * nrm b ≤ g0 * e1 := by
    refine abs_le_of_sq_le_sq' ?_ (mul_nonneg hg0p.le he1) |>.2
    rw [mul_pow, mul_pow, hst2, hg02, BstLean.Part153.nrm_sq]
    exact heb.trans (mul_le_mul_of_nonneg_left he1' hγ.le)
  have hb2 : st * nrm (hid2Mean_cr A₁ A₂ c τ - b) ≤ g0 * e2 := by
    refine abs_le_of_sq_le_sq' ?_ (mul_nonneg hg0p.le he2) |>.2
    rw [mul_pow, mul_pow, hst2, hg02, BstLean.Part153.nrm_sq]
    refine hxi.trans ?_
    have : xi * (2 / (n : ℝ)) / n = 2 / (n : ℝ) * (xi / n) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left he2' hγ.le
  have hb3 : 2 / (mA n : ℝ) * (nrm b + nrm (hid2Mean_cr A₁ A₂ c τ - b)) ^ 2 ≤
      2 / (n : ℝ) * (e1 + e2) ^ 2 := by
    have e : 2 / (mA n : ℝ) * (nrm b + nrm (hid2Mean_cr A₁ A₂ c τ - b)) ^ 2 =
        (st * nrm b + st * nrm (hid2Mean_cr A₁ A₂ c τ - b)) ^ 2 := by
      rw [← hst2]; ring
    have e' : 2 / (n : ℝ) * (e1 + e2) ^ 2 = (g0 * e1 + g0 * e2) ^ 2 := by
      rw [← hg02]; ring
    rw [e, e']
    exact pow_le_pow_left₀ (add_nonneg (mul_nonneg hst0 hnb) (mul_nonneg hst0 hnd))
      (add_le_add hb1 hb2) 2
  -- the moments of `σ`
  obtain ⟨L, hLd⟩ : ∃ L : ℝ, L = 2 / (n : ℝ) * (1 - N22 * (2 + N22)) - N * (2 / (n : ℝ)) / n -
      2 / (n : ℝ) * (e1 + e2) ^ 2 := ⟨_, rfl⟩
  have hσsq : ∀ ξ, sigD A₁ A₂ c τ b ξ ^ 2 =
      2 / (mA n : ℝ) * normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) :=
    fun ξ => sigD_sq A₁ A₂ c τ b ξ
  have hi2 : Integrable (fun ξ => sigD A₁ A₂ c τ b ξ ^ 2) (stdGauss (Fin n)) := by
    simp_rw [hσsq]; exact hi
  have hσm := measurable_sigD hb A₁ A₂ c τ
  have hi1 : Integrable (sigD A₁ A₂ c τ b) (stdGauss (Fin n)) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hi2) hσm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sigD_nonneg A₁ A₂ c τ b ξ)]
    show sigD A₁ A₂ c τ b ξ ≤ 1 + sigD A₁ A₂ c τ b ξ ^ 2
    nlinarith [sq_nonneg (sigD A₁ A₂ c τ b ξ - 1), sigD_nonneg A₁ A₂ c τ b ξ]
  have hL : L ≤ ∫ ξ, sigD A₁ A₂ c τ b ξ ^ 2 ∂stdGauss (Fin n) := by
    simp_rw [hσsq]
    refine le_trans ?_ hE
    rw [hLd]
    have := mul_le_mul_of_nonneg_left hω' hγ.le
    linarith
  have hV : ∫ ξ, (sigD A₁ A₂ c τ b ξ - ∫ ζ, sigD A₁ A₂ c τ b ζ ∂stdGauss (Fin n)) ^ 2
      ∂stdGauss (Fin n) ≤ N * (2 / (n : ℝ)) / n :=
    (sigD_var hn A₁ A₂ c hτ hb).trans hXi
  have hs' : (g0 * s) ^ 2 ≤ L - N * (2 / (n : ℝ)) / n := by
    rw [mul_pow, hg02, hLd]
    have := mul_le_mul_of_nonneg_left hs2 hγ.le
    have e : 2 / (n : ℝ) * (1 - N22 * (2 + N22) - (e1 + e2) ^ 2 - 2 * N / n) =
        2 / (n : ℝ) * (1 - N22 * (2 + N22)) - N * (2 / (n : ℝ)) / n -
          2 / (n : ℝ) * (e1 + e2) ^ 2 - N * (2 / (n : ℝ)) / n := by ring
    linarith
  rw [← hg0]
  exact ⟨hi1, hi2, hV, L, hL, hs'⟩

/-- **The mass bound from a tail bound of `σ = √t_A·|r|`.** Hypotheses: `Ξ ≤ N γ_A/n`,
`e_b ≤ e₁²`, `ξ/n ≤ e₂²`, `N₂₂ ≤ N22`, a tail bound `Pr(|σ − Eσ| ≥ g) ≤ T(g)`, and
`sd < s`, `s² ≤ 1 − N22(2 + N22) − (e₁ + e₂)² − 2N/n`. Then
`Pr(t_A|r|² < γ_A·sd²) ≤ T(√γ_A·(s − sd))`. -/
theorem mass_bound_gen (hn : 6 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {b : Fin (mA n) → ℝ} (hb : 0 < normSq b) {N eb xi N22 e1 e2 sd s : ℝ} {T : ℝ → ℝ}
    (hXi : XiS A₁ A₂ c τ ≤ N * (2 / (n : ℝ)) / n)
    (heb : 2 / (mA n : ℝ) * normSq b ≤ 2 / (n : ℝ) * eb)
    (hxi : 2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - b) ≤ xi * (2 / (n : ℝ)) / n)
    (hN22 : N2 2 A₁ A₂ c τ ≤ N22)
    (he1 : 0 ≤ e1) (he1' : eb ≤ e1 ^ 2) (he2 : 0 ≤ e2) (he2' : xi / n ≤ e2 ^ 2)
    (hsd : 0 ≤ sd) (hs : sd < s)
    (hs2 : s ^ 2 ≤ 1 - N22 * (2 + N22) - (e1 + e2) ^ 2 - 2 * N / n)
    (hT : ∀ g : ℝ, 0 < g → (stdGauss (Fin n)).real
      {ξ | g ≤ |sigD A₁ A₂ c τ b ξ - ∫ ζ, sigD A₁ A₂ c τ b ζ ∂stdGauss (Fin n)|} ≤ T g) :
    (stdGauss (Fin n)).real
        {ξ | 2 / (mA n : ℝ) * normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) <
          2 / (n : ℝ) * sd ^ 2} ≤ T (√(2 / (n : ℝ)) * (s - sd)) := by
  obtain ⟨hi1, hi2, hV, L, hL, hs'⟩ := sigD_moments hn A₁ A₂ c hτ hb hXi heb hxi hN22 he1 he1'
    he2 he2' hs2
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  obtain ⟨g0, hg0⟩ : ∃ g0 : ℝ, g0 = √(2 / (n : ℝ)) := ⟨_, rfl⟩
  have hg0p : 0 < g0 := by rw [hg0]; exact Real.sqrt_pos.mpr hγ
  have hg02 : g0 ^ 2 = 2 / (n : ℝ) := by rw [hg0]; exact Real.sq_sqrt hγ.le
  have hσsq : ∀ ξ, sigD A₁ A₂ c τ b ξ ^ 2 =
      2 / (mA n : ℝ) * normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) :=
    fun ξ => sigD_sq A₁ A₂ c τ b ξ
  rw [← hg0] at hs'
  have key := lower_tail_of_moments (stdGauss (Fin n)) (sigD_nonneg A₁ A₂ c τ b) hi1 hi2 hL hV hT
    (a := g0 * sd) (s := g0 * s) (mul_nonneg hg0p.le hsd) (mul_lt_mul_of_pos_left hs hg0p) hs'
  have hset : {ξ : Fin n → ℝ | 2 / (mA n : ℝ) * normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) <
      2 / (n : ℝ) * sd ^ 2} = {ξ | sigD A₁ A₂ c τ b ξ ^ 2 < (g0 * sd) ^ 2} := by
    ext ξ
    show 2 / (mA n : ℝ) * normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) < 2 / (n : ℝ) * sd ^ 2 ↔
      sigD A₁ A₂ c τ b ξ ^ 2 < (g0 * sd) ^ 2
    rw [hσsq, mul_pow, hg02]
  rw [hset, ← hg0, mul_sub]
  exact key

/-- `(2a + √(4a² + N²))² ≤ K` from a rational bound of the root. -/
lemma sharp_const_le {a N r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (h : 4 * a ^ 2 + N ^ 2 ≤ r ^ 2) :
    (2 * a + √(4 * a ^ 2 + N ^ 2)) ^ 2 ≤ (2 * a + r) ^ 2 := by
  have h1 : √(4 * a ^ 2 + N ^ 2) ≤ r := by
    rw [← Real.sqrt_sq hr]; exact Real.sqrt_le_sqrt h
  exact pow_le_pow_left₀ (by positivity) (by linarith) 2

/-- **The mass bound from the fourth moment** (Part160Mass4): with `Ξ ≤ N γ_A/n` and
`Ξ₄ ≤ a γ_A/n`, cutoff `d = sd²`:
`n·Pr(t_A|r|² < γ_A·sd²) ≤ (2a + √(4a² + N²))²/(n·(s − sd)⁴)`. -/
theorem mass_bound4 (hn : 6 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {b : Fin (mA n) → ℝ} (hb : 0 < normSq b) {N a eb xi N22 e1 e2 sd s : ℝ}
    (hXi : XiS A₁ A₂ c τ ≤ N * (2 / (n : ℝ)) / n)
    (hXi4 : Xi4 A₁ A₂ c τ ≤ a * (2 / (n : ℝ)) / n)
    (heb : 2 / (mA n : ℝ) * normSq b ≤ 2 / (n : ℝ) * eb)
    (hxi : 2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - b) ≤ xi * (2 / (n : ℝ)) / n)
    (hN22 : N2 2 A₁ A₂ c τ ≤ N22)
    (he1 : 0 ≤ e1) (he1' : eb ≤ e1 ^ 2) (he2 : 0 ≤ e2) (he2' : xi / n ≤ e2 ^ 2)
    (hsd : 0 ≤ sd) (hs : sd < s)
    (hs2 : s ^ 2 ≤ 1 - N22 * (2 + N22) - (e1 + e2) ^ 2 - 2 * N / n) :
    (n : ℝ) * (stdGauss (Fin n)).real
        {ξ | 2 / (mA n : ℝ) * normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) <
          2 / (n : ℝ) * sd ^ 2} ≤
      (2 * a + √(4 * a ^ 2 + N ^ 2)) ^ 2 / (n * (s - sd) ^ 4) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hγ : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hd : 0 < s - sd := by linarith
  have h := mass_bound_gen hn A₁ A₂ c hτ hb hXi heb hxi hN22 he1 he1' he2 he2' hsd hs hs2
    (T := fun g => (2 * (a * (2 / (n : ℝ)) / n) +
      √(4 * (a * (2 / (n : ℝ)) / n) ^ 2 + (N * (2 / (n : ℝ)) / n) ^ 2)) ^ 2 / g ^ 4)
    (fun g hg => sigD_markov4_sharp hn A₁ A₂ c hτ hb hXi4 hXi hg)
  have e1' : 4 * (a * (2 / (n : ℝ)) / n) ^ 2 + (N * (2 / (n : ℝ)) / n) ^ 2 =
      (2 / (n : ℝ) / n) ^ 2 * (4 * a ^ 2 + N ^ 2) := by ring
  have e2' : √((2 / (n : ℝ) / n) ^ 2 * (4 * a ^ 2 + N ^ 2)) =
      2 / (n : ℝ) / n * √(4 * a ^ 2 + N ^ 2) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have e3 : (√(2 / (n : ℝ)) * (s - sd)) ^ 4 = (2 / (n : ℝ)) ^ 2 * (s - sd) ^ 4 := by
    have : √(2 / (n : ℝ)) ^ 4 = (2 / (n : ℝ)) ^ 2 := by
      have h2 : √(2 / (n : ℝ)) ^ 2 = 2 / (n : ℝ) := Real.sq_sqrt hγ.le
      calc √(2 / (n : ℝ)) ^ 4 = (√(2 / (n : ℝ)) ^ 2) ^ 2 := by ring
        _ = _ := by rw [h2]
    rw [mul_pow, this]
  beta_reduce at h
  rw [e1', e2', e3] at h
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = √(4 * a ^ 2 + N ^ 2) := ⟨_, rfl⟩
  rw [← hR] at h ⊢
  have e4 : (2 * (a * (2 / (n : ℝ)) / n) + 2 / (n : ℝ) / n * R) ^ 2 /
      ((2 / (n : ℝ)) ^ 2 * (s - sd) ^ 4) = (2 * a + R) ^ 2 / (n * (s - sd) ^ 4) / n := by
    field_simp
  rw [e4] at h
  calc (n : ℝ) * _ ≤ n * ((2 * a + R) ^ 2 / (n * (s - sd) ^ 4) / n) :=
        mul_le_mul_of_nonneg_left h hnR.le
    _ = _ := by field_simp

end BstLean.Part160

open BstLean.Part160 in
#print axioms lower_tail_of_moments
open BstLean.Part160 in
#print axioms Esig2_lower
open BstLean.Part160 in
#print axioms mass_bound_gen
open BstLean.Part160 in
#print axioms mass_bound4
open BstLean.Part160 in
#print axioms sigD_moments
