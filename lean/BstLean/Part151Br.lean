import BstLean.Part151U5
import BstLean.Part152LM

/-!
# Part 151: three bridges from the `A` stage to the hypotheses of Proposition VA

Role: `delegations/statements/p151-spec.md`. Paper sources:
`proofs/option-n/theorem5-04-standin-structure.tex` (Lemma "The residual covariance") and
`theorem5-10-transport.tex` (Lemma V: the event `E_c` and Step 1).

Notation: `b = bh (W, (A₁, A₂))`, `t_A = 2/m_A`, `γ_A = 2/n`, `a₂(ξ) = hU W A₁ A₂ ξ`,
`r(ξ) = res b (a₂ ξ)`, `λ = lamU`, `σ = sigU`, `c_A = A₃ b`, `σ_p = tauOutOf n b`.

* `res_dot_symm`, `dot_res_self`: `⟨r(h), w⟩ = ⟨h, Π_b w⟩`, `⟨b, Π_b w⟩ = 0`.
* **`lemmaCr_gen`**, **`lemmaCr`**: if `t·Cov(a₂) ≤ Mcov` (as a quadratic form), then
  `‖C_r‖_op ≤ Mcov + t·|ā₂ − b|²` (the hypothesis `hMr` of `Part151U3`, `Part151U5`).
* **`lemmaEc`**: `Pr_{A₃}(|A₃ b|² > t_A|b|²·n(1 + δ_c)) ≤ e^{−L}`, `δ_c = 2√(L/n) + 2L/n`.
* `Dv`: `n·t_A|b|²·E(λ − 1)² + n·E(σ − σ_p)²`, a function of `(W, A₁, A₂)` only.
* **`Dc_le_Dv`**: on the complement of the event of `lemmaEc`: `𝔇_c ≤ (1 + δ_c)·Dv`.
* **`energy_le`**: there, if `t_A|b|² ≤ γ_A`: `|c_A|² + nσ_p² ≤ 2(1 + δ_c)`.
* `Dv_eq`: `Dv = n·E|v(x) − v_p|²`, `v = (√t_A|b|λ, σ)`, `v_p = (√t_A|b|, σ_p)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part134 (lam res sig normSq_ne_zero)
open BstLean.Part136 (HidParam)
open BstLean.Part149 (thA tauOutOf normSq_res_le)
open BstLean.Part150 (CMap)

/-! ## Lemma Cr: the residual covariance -/

section Cr

variable {m : ℕ}

/-- `⟨r(h), w⟩ = ⟨h, Π_b w⟩`: the projection on `b^⊥` is symmetric. -/
lemma res_dot_symm (b h w : Fin m → ℝ) :
    ∑ j, res b h j * w j = ∑ j, h j * res b w j := by
  unfold res lam
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, mul_sub, Finset.sum_sub_distrib]
  congr 1
  have e1 : ∑ j, (∑ i, h i * b i) / normSq b * b j * w j =
      (∑ i, h i * b i) / normSq b * ∑ j, w j * b j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j, h j * ((∑ i, w i * b i) / normSq b * b j) =
      (∑ i, w i * b i) / normSq b * ∑ j, h j * b j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]; ring

/-- `⟨b, Π_b w⟩ = 0` for `b ≠ 0`. -/
lemma dot_res_self {b : Fin m → ℝ} (hb : b ≠ 0) (w : Fin m → ℝ) :
    ∑ j, b j * res b w j = 0 := by
  have hb0 := normSq_ne_zero hb
  unfold res lam
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  have e2 : ∑ j, b j * ((∑ i, w i * b i) / normSq b * b j) =
      (∑ i, w i * b i) / normSq b * normSq b := by
    unfold normSq; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have e1 : ∑ j, b j * w j = ∑ i, w i * b i := Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e2, e1]
  field_simp
  ring

variable {Ξ : Type*} [MeasurableSpace Ξ]

/-- **Lemma Cr (the residual covariance), general form.** `(Ξ, μ)` a probability space, `h` a
bounded measurable map with values in `ℝ^m`, `ā = E h`, `b ≠ 0`, `t ≥ 0`. If the covariance of
`h` satisfies `t·E⟨h − ā, w⟩² ≤ Mcov·|w|²` for every `w`, then the residual `r = Π_b h`
satisfies `t·E⟨r, w⟩² ≤ (Mcov + t·|ā − b|²)·|w|²`: that is
`‖C_r‖_op ≤ ‖t·Cov(h)‖_op + t·|ā − b|²`. -/
theorem lemmaCr_gen (μ : Measure Ξ) [IsProbabilityMeasure μ] {h : Ξ → Fin m → ℝ}
    (hh : Measurable h) {H : ℝ} (hH : ∀ ξ, normSq (h ξ) ≤ H) {b : Fin m → ℝ} (hb : b ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) {Mcov : ℝ} (hM0 : 0 ≤ Mcov)
    (hcov : ∀ w : Fin m → ℝ, t * ∫ ξ, (∑ j, (h ξ j - ∫ ζ, h ζ j ∂μ) * w j) ^ 2 ∂μ ≤
      Mcov * ∑ j, w j ^ 2) (w : Fin m → ℝ) :
    t * ∫ ξ, (∑ j, res b (h ξ) j * w j) ^ 2 ∂μ ≤
      (Mcov + t * normSq (fun j => (∫ ζ, h ζ j ∂μ) - b j)) * ∑ j, w j ^ 2 := by
  set abar : Fin m → ℝ := fun j => ∫ ζ, h ζ j ∂μ with habar
  set u : Fin m → ℝ := res b w with hu
  obtain ⟨ξ₀⟩ := μ.nonempty_of_neZero
  have hH0 : 0 ≤ H := (normSq_nonneg _).trans (hH ξ₀)
  -- coordinates are bounded
  have hcoord : ∀ ξ j, |h ξ j| ≤ √H := by
    intro ξ j
    have h1 : h ξ j ^ 2 ≤ normSq (h ξ) := by
      unfold normSq
      exact Finset.single_le_sum (f := fun i => h ξ i ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ j)
    exact Real.abs_le_sqrt (h1.trans (hH ξ))
  have hint : ∀ j, Integrable (fun ξ => h ξ j) μ := fun j =>
    Integrable.of_bound ((measurable_pi_apply j).comp hh).aestronglyMeasurable (√H)
      (Filter.Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact hcoord ξ j)
  -- `g = ⟨h, u⟩`, `f = ⟨h − ā, u⟩ = g − c₀`
  set g : Ξ → ℝ := fun ξ => ∑ j, h ξ j * u j with hg
  set c₀ : ℝ := ∑ j, abar j * u j with hc₀
  have hgm : Measurable g :=
    Finset.measurable_sum _ fun j _ => ((measurable_pi_apply j).comp hh).mul_const _
  set Bg : ℝ := ∑ j, √H * |u j| with hBg
  have hgb : ∀ ξ, |g ξ| ≤ Bg := by
    intro ξ
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hcoord ξ j) (abs_nonneg _)
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hgb ξ₀)
  have hgi : Integrable g μ :=
    Integrable.of_bound hgm.aestronglyMeasurable Bg
      (Filter.Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact hgb ξ)
  have hgc : ∫ ξ, g ξ ∂μ = c₀ := by
    rw [hg, hc₀, integral_finsetSum _ fun j _ => (hint j).mul_const _]
    exact Finset.sum_congr rfl fun j _ => by rw [integral_mul_const]
  have hfi : Integrable (fun ξ => (g ξ - c₀) ^ 2) μ :=
    Integrable.of_bound ((hgm.sub_const _).pow_const 2).aestronglyMeasurable ((Bg + |c₀|) ^ 2)
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (g ξ - c₀)]
        exact pow_le_pow_left₀ (abs_nonneg _)
          ((abs_sub _ _).trans (add_le_add (hgb ξ) le_rfl)) 2)
  -- the variance identity
  have hvar : ∫ ξ, g ξ ^ 2 ∂μ = ∫ ξ, (g ξ - c₀) ^ 2 ∂μ + c₀ ^ 2 := by
    have i3' : Integrable (fun ξ => g ξ - c₀) μ := hgi.sub (integrable_const _)
    have i4' : Integrable (fun ξ => 2 * c₀ * (g ξ - c₀)) μ := i3'.const_mul _
    have hlin : Integrable (fun ξ => 2 * c₀ * (g ξ - c₀) + c₀ ^ 2) μ :=
      i4'.add (integrable_const _)
    have e : (fun ξ => g ξ ^ 2) =
        fun ξ => (g ξ - c₀) ^ 2 + (2 * c₀ * (g ξ - c₀) + c₀ ^ 2) := by
      funext ξ; ring
    have e2 : ∫ ξ, (2 * c₀ * (g ξ - c₀) + c₀ ^ 2) ∂μ = c₀ ^ 2 := by
      have h1 : ∫ ξ, (g ξ - c₀) ∂μ = 0 := by
        have := integral_sub hgi (integrable_const (μ := μ) c₀)
        rw [this, hgc]; simp
      have i3 : Integrable (fun ξ => g ξ - c₀) μ := hgi.sub (integrable_const _)
      have i4 : Integrable (fun ξ => 2 * c₀ * (g ξ - c₀)) μ := i3.const_mul _
      rw [integral_add i4 (integrable_const _), integral_const_mul, h1]
      simp
    rw [e, integral_add hfi hlin, e2]
  -- rewrite both sides
  have eL : (fun ξ => (∑ j, res b (h ξ) j * w j) ^ 2) = fun ξ => g ξ ^ 2 := by
    funext ξ; rw [res_dot_symm b (h ξ) w]
  have eF : (fun ξ => (∑ j, (h ξ j - abar j) * u j) ^ 2) = fun ξ => (g ξ - c₀) ^ 2 := by
    funext ξ
    simp only [hg, hc₀, sub_mul, Finset.sum_sub_distrib]
  rw [eL]
  have hc := hcov u
  rw [eF] at hc
  -- `c₀ = ⟨ā − b, u⟩`
  have hc₀' : c₀ = ∑ j, (abar j - b j) * u j := by
    have h0 := dot_res_self hb w
    simp only [hc₀, sub_mul, Finset.sum_sub_distrib]
    rw [← hu] at h0
    linarith
  have hcs : c₀ ^ 2 ≤ normSq (fun j => abar j - b j) * normSq u := by
    rw [hc₀']
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => abar j - b j) u
  have hun : normSq u ≤ normSq w := normSq_res_le hb w
  have hu0 : 0 ≤ normSq u := normSq_nonneg _
  have hd0 : 0 ≤ normSq (fun j => abar j - b j) := normSq_nonneg _
  have hw : ∑ j, w j ^ 2 = normSq w := rfl
  have hu' : ∑ j, u j ^ 2 = normSq u := rfl
  rw [hu'] at hc
  rw [hvar, hw, mul_add]
  have h1 : Mcov * normSq u ≤ Mcov * normSq w := mul_le_mul_of_nonneg_left hun hM0
  have h2 : t * c₀ ^ 2 ≤ t * normSq (fun j => abar j - b j) * normSq w := by
    calc t * c₀ ^ 2 ≤ t * (normSq (fun j => abar j - b j) * normSq u) :=
          mul_le_mul_of_nonneg_left hcs ht
      _ ≤ t * (normSq (fun j => abar j - b j) * normSq w) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hun hd0) ht
      _ = _ := by ring
  nlinarith

end Cr

section net

variable {n : ℕ} (bh : CMap n) (W : MlpParam (2 * n) (mW n) n)
  (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)

/-- **Lemma Cr for the Agent network**: if `t_A·Cov_ξ(a₂)` is at most `Mcov` as a quadratic
form, then the hypothesis `hMr` (`‖C_r‖_op ≤ Mr`) of `Part151U3`, `Part151U5` holds with
`Mr = Mcov + t_A·|ā₂ − b|²`, `ā₂ = E_ξ a₂`. -/
theorem lemmaCr (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) {Mcov : ℝ} (hM0 : 0 ≤ Mcov)
    (hcov : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, (hU W A₁ A₂ ξ j - ∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) * w j) ^ 2
        ∂stdGauss (Fin n) ≤ Mcov * ∑ j, w j ^ 2) (w : Fin (mA n) → ℝ) :
    2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        (Mcov + 2 / (mA n : ℝ) * normSq (fun j =>
          (∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) - bh (W, (A₁, A₂)) j)) * ∑ j, w j ^ 2 :=
  lemmaCr_gen (stdGauss (Fin n)) (measurable_hU W A₁ A₂) (hU_le W A₁ A₂ hn) hb
    (by positivity) hM0 hcov w

/-! ## The event `E_c` -/

/-- `δ_c = 2√(L/n) + 2L/n`. -/
noncomputable def deltaC (n : ℕ) (L : ℝ) : ℝ := 2 * √(L / (n : ℝ)) + 2 * L / (n : ℝ)

lemma deltaC_nonneg (n : ℕ) {L : ℝ} (hL : 0 ≤ L) : 0 ≤ deltaC n L := by
  unfold deltaC; positivity

/-- **The event `E_c` of Lemma V**: for a Gaussian matrix `M` with `n` rows and entry variance
`v ≥ 0`, any vector `b`, and `L ≥ 0`:
`Pr(|M b|² > v|b|²·n(1 + δ_c)) ≤ e^{−L}`, `δ_c = 2√(L/n) + 2L/n`. -/
theorem lemmaEc_gen {m : ℕ} (hn : 1 ≤ n) {v : ℝ} (hv : 0 ≤ v) (b : Fin m → ℝ) {L : ℝ}
    (hL : 0 ≤ L) :
    (gaussMat n m v).real {M | v * normSq b * n * (1 + deltaC n L) < normSq (M *ᵥ b)} ≤
      Real.exp (-L) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set K : ℝ := v * normSq b with hK
  have hK0 : 0 ≤ K := mul_nonneg hv (normSq_nonneg _)
  have hS : MeasurableSet {y : Fin n → ℝ | K * n * (1 + deltaC n L) < normSq y} :=
    measurableSet_lt measurable_const measurable_normSq
  have e : {M : Matrix (Fin n) (Fin m) ℝ | K * n * (1 + deltaC n L) < normSq (M *ᵥ b)} =
      (fun M : Matrix (Fin n) (Fin m) ℝ => M *ᵥ b) ⁻¹'
        {y | K * n * (1 + deltaC n L) < normSq y} := rfl
  rw [e, ← map_measureReal_apply (measurable_mulVec_right b) hS, gaussMat_mulVec,
    map_measureReal_apply (by fun_prop) hS]
  have hc2 : (√v * √(normSq b)) ^ 2 = K := by
    rw [mul_pow, Real.sq_sqrt hv, Real.sq_sqrt (normSq_nonneg _)]
  have hδ : (n : ℝ) * (1 + deltaC n L) = n + 2 * √((n : ℝ) * L) + 2 * L := by
    unfold deltaC
    have h1 : (n : ℝ) * √(L / n) = √((n : ℝ) * L) := by
      rw [show (n : ℝ) * L = (n : ℝ) ^ 2 * (L / n) by field_simp,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hn0.le]
    have h2 : (n : ℝ) * (2 * L / n) = 2 * L := by field_simp
    calc (n : ℝ) * (1 + (2 * √(L / n) + 2 * L / n))
        = n + 2 * ((n : ℝ) * √(L / n)) + (n : ℝ) * (2 * L / n) := by ring
      _ = _ := by rw [h1, h2]
  have hLM := BstLean.Part152.chiSq_upper_LM (ι := Fin n) hL
  rw [Fintype.card_fin] at hLM
  refine le_trans (measureReal_mono ?_) hLM
  intro ξ hξ
  simp only [mem_preimage, mem_ofPred_eq] at hξ ⊢
  rw [normSq_smul, hc2] at hξ
  have hns : normSq ξ = ∑ i, ξ i ^ 2 := rfl
  rcases hK0.eq_or_lt with h0 | hpos
  · rw [← h0] at hξ; simp at hξ
  · have h3 : (n : ℝ) * (1 + deltaC n L) < normSq ξ := by
      have : K * ((n : ℝ) * (1 + deltaC n L)) < K * normSq ξ := by
        calc K * ((n : ℝ) * (1 + deltaC n L)) = K * n * (1 + deltaC n L) := by ring
          _ < K * normSq ξ := hξ
      exact lt_of_mul_lt_mul_left this hK0
    rw [hδ, hns] at h3
    exact h3.le

/-- **The event `E_c` for the last matrix of `A`**:
`Pr_{A₃}(|A₃ b|² > t_A|b|²·n(1 + δ_c)) ≤ e^{−L}`; no hypothesis on `b`. -/
theorem lemmaEc (hn : 1 ≤ n) {L : ℝ} (hL : 0 ≤ L) :
    (gaussMat n (mA n) (2 / (mA n : ℝ))).real
        {A₃ | 2 / (mA n : ℝ) * normSq (bh (W, (A₁, A₂))) * n * (1 + deltaC n L) <
          normSq (A₃ *ᵥ bh (W, (A₁, A₂)))} ≤ Real.exp (-L) :=
  lemmaEc_gen hn (by positivity) _ hL

/-! ## Lemma V, Step 1, and the energy -/

/-- `Dv = n·t_A|b|²·E_ξ(λ − 1)² + n·E_ξ(σ − σ_p)²`: the coupling cost with `|c_A|²` replaced
by its mean `n·t_A|b|²`. A function of `(W, A₁, A₂)` only. -/
noncomputable def Dv : ℝ :=
  n * (2 / (mA n : ℝ) * normSq (bh (W, (A₁, A₂)))) *
      ∫ ξ, (lamU bh W A₁ A₂ ξ - 1) ^ 2 ∂stdGauss (Fin n) +
    n * ∫ ξ, (sigU bh W A₁ A₂ ξ - tauOutOf n (bh (W, (A₁, A₂)))) ^ 2 ∂stdGauss (Fin n)

lemma Dv_nonneg : 0 ≤ Dv bh W A₁ A₂ := by
  unfold Dv
  have h1 : 0 ≤ ∫ ξ, (lamU bh W A₁ A₂ ξ - 1) ^ 2 ∂stdGauss (Fin n) :=
    integral_nonneg fun _ => sq_nonneg _
  have h2 : 0 ≤ ∫ ξ, (sigU bh W A₁ A₂ ξ - tauOutOf n (bh (W, (A₁, A₂)))) ^ 2
      ∂stdGauss (Fin n) := integral_nonneg fun _ => sq_nonneg _
  have h3 := normSq_nonneg (bh (W, (A₁, A₂)))
  positivity

/-- **Lemma V, Step 1**: where `|c_A|² ≤ t_A|b|²·n(1 + δ)` (the event `E_c`), the coupling
cost is at most `(1 + δ)·Dv`. -/
theorem Dc_le_Dv (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (A₃ : Matrix (Fin n) (Fin (mA n)) ℝ)
    (hc : normSq (A₃ *ᵥ bh (W, (A₁, A₂))) ≤
      2 / (mA n : ℝ) * normSq (bh (W, (A₁, A₂))) * n * (1 + δ)) :
    Dc bh W (A₁, A₂, A₃) ≤ (1 + δ) * Dv bh W A₁ A₂ := by
  have hD := Dc_eq bh W (A₁, A₂, A₃) hn hb
  have e1 : cAv bh W (A₁, A₂, A₃) = A₃ *ᵥ bh (W, (A₁, A₂)) := rfl
  have e2 : lamX bh W (A₁, A₂, A₃) = lamU bh W A₁ A₂ := rfl
  have e3 : sigX bh W (A₁, A₂, A₃) = sigU bh W A₁ A₂ := rfl
  have e4 : sigP bh W (A₁, A₂, A₃) = tauOutOf n (bh (W, (A₁, A₂))) := rfl
  rw [e1, e2, e3, e4] at hD
  rw [hD]
  unfold Dv
  set I1 := ∫ ξ, (lamU bh W A₁ A₂ ξ - 1) ^ 2 ∂stdGauss (Fin n) with hI1
  set I2 := ∫ ξ, (sigU bh W A₁ A₂ ξ - tauOutOf n (bh (W, (A₁, A₂)))) ^ 2 ∂stdGauss (Fin n)
    with hI2
  have h1 : 0 ≤ I1 := integral_nonneg fun _ => sq_nonneg _
  have h2 : 0 ≤ I2 := integral_nonneg fun _ => sq_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have t1 := mul_le_mul_of_nonneg_right hc h1
  have t2 : (n : ℝ) * I2 ≤ (1 + δ) * (n * I2) := by
    have : 0 ≤ (n : ℝ) * I2 := mul_nonneg hn0 h2
    nlinarith
  calc normSq (A₃ *ᵥ bh (W, (A₁, A₂))) * I1 + n * I2
      ≤ 2 / (mA n : ℝ) * normSq (bh (W, (A₁, A₂))) * n * (1 + δ) * I1 + (1 + δ) * (n * I2) :=
        add_le_add t1 t2
    _ = _ := by ring

/-- **The energy on `E_c`**: where `|c_A|² ≤ t_A|b|²·n(1 + δ)` and `t_A|b|² ≤ γ_A = 2/n`
(`e_b ≤ 1`): `|c_A|² + n·σ_p² ≤ 2(1 + δ)`. -/
theorem energy_le (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 ≤ δ) (A₃ : Matrix (Fin n) (Fin (mA n)) ℝ)
    (hc : normSq (A₃ *ᵥ bh (W, (A₁, A₂))) ≤
      2 / (mA n : ℝ) * normSq (bh (W, (A₁, A₂))) * n * (1 + δ))
    (he : 2 / (mA n : ℝ) * normSq (bh (W, (A₁, A₂))) ≤ 2 / (n : ℝ)) :
    normSq (A₃ *ᵥ bh (W, (A₁, A₂))) + n * tauOutOf n (bh (W, (A₁, A₂))) ^ 2 ≤ 2 * (1 + δ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set K : ℝ := 2 / (mA n : ℝ) * normSq (bh (W, (A₁, A₂))) with hK
  have hK0 : 0 ≤ K := by rw [hK]; have := normSq_nonneg (bh (W, (A₁, A₂))); positivity
  have hσ : tauOutOf n (bh (W, (A₁, A₂))) ^ 2 = 2 / (n : ℝ) - K := by
    unfold tauOutOf
    rw [Real.sq_sqrt (le_max_left _ _), max_eq_right (by linarith)]
  rw [hσ]
  have hnK : (n : ℝ) * K ≤ 2 := by
    have := mul_le_mul_of_nonneg_left he hn0.le
    rwa [show (n : ℝ) * (2 / (n : ℝ)) = 2 by field_simp] at this
  have e : (n : ℝ) * (2 / (n : ℝ) - K) = 2 - n * K := by field_simp
  rw [e]
  have h3 : (n : ℝ) * K * δ ≤ 2 * δ := mul_le_mul_of_nonneg_right hnK hδ
  have h4 : K * n * (1 + δ) = n * K + n * K * δ := by ring
  linarith

/-- The document's form of `Dv`: `Dv = n·E_x|v(x) − v_p|²` with
`v(x) = (√t_A·|b|·λ(x), σ(x))`, `v_p = (√t_A·|b|, σ_p)`. -/
theorem Dv_eq (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) :
    Dv bh W A₁ A₂ = n * ∫ ξ,
      ((√(2 / (mA n : ℝ)) * √(normSq (bh (W, (A₁, A₂)))) * lamU bh W A₁ A₂ ξ -
          √(2 / (mA n : ℝ)) * √(normSq (bh (W, (A₁, A₂))))) ^ 2 +
        (sigU bh W A₁ A₂ ξ - tauOutOf n (bh (W, (A₁, A₂)))) ^ 2) ∂stdGauss (Fin n) := by
  have hv : (0 : ℝ) ≤ 2 / (mA n : ℝ) := by positivity
  have hns := normSq_nonneg (bh (W, (A₁, A₂)))
  have e : ∀ ξ : Fin n → ℝ,
      (√(2 / (mA n : ℝ)) * √(normSq (bh (W, (A₁, A₂)))) * lamU bh W A₁ A₂ ξ -
          √(2 / (mA n : ℝ)) * √(normSq (bh (W, (A₁, A₂))))) ^ 2 =
        2 / (mA n : ℝ) * normSq (bh (W, (A₁, A₂))) * (lamU bh W A₁ A₂ ξ - 1) ^ 2 := by
    intro ξ
    have : (√(2 / (mA n : ℝ)) * √(normSq (bh (W, (A₁, A₂))))) ^ 2 =
        2 / (mA n : ℝ) * normSq (bh (W, (A₁, A₂))) := by
      rw [mul_pow, Real.sq_sqrt hv, Real.sq_sqrt hns]
    rw [← this]; ring
  simp_rw [e]
  have ml : Measurable (lamU bh W A₁ A₂) :=
    (BstLean.Part134.measurable_lam _).comp (measurable_hU W A₁ A₂)
  have i1 : Integrable (fun ξ => (lamU bh W A₁ A₂ ξ - 1) ^ 2) (stdGauss (Fin n)) := by
    refine Integrable.of_bound ((ml.sub_const 1).pow_const 2).aestronglyMeasurable
      ((√(frob A₂ * frob A₁ / normSq (bh (W, (A₁, A₂)))) + 1) ^ 2)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (lamU bh W A₁ A₂ ξ - 1)]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    have h1 := Real.abs_le_sqrt (lamU_sq_le bh W A₁ A₂ hn hb ξ)
    calc |lamU bh W A₁ A₂ ξ - 1| ≤ |lamU bh W A₁ A₂ ξ| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ _ := by rw [abs_one]; linarith
  have ms := measurable_sigU bh W A₁ A₂
  have i2 : Integrable (fun ξ => (sigU bh W A₁ A₂ ξ - tauOutOf n (bh (W, (A₁, A₂)))) ^ 2)
      (stdGauss (Fin n)) := by
    refine Integrable.of_bound ((ms.sub_const _).pow_const 2).aestronglyMeasurable
      ((√(2 / (mA n : ℝ) * (frob A₂ * frob A₁)) + |tauOutOf n (bh (W, (A₁, A₂)))|) ^ 2)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      ← sq_abs (sigU bh W A₁ A₂ ξ - tauOutOf n (bh (W, (A₁, A₂))))]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    have h1 := Real.abs_le_sqrt
      (sigX_sq_le bh W (A₁, A₂, (0 : Matrix (Fin n) (Fin (mA n)) ℝ)) hn hb ξ)
    calc |sigU bh W A₁ A₂ ξ - tauOutOf n (bh (W, (A₁, A₂)))|
        ≤ |sigU bh W A₁ A₂ ξ| + |tauOutOf n (bh (W, (A₁, A₂)))| := abs_sub _ _
      _ ≤ _ := add_le_add h1 le_rfl
  rw [integral_add (i1.const_mul _) i2, integral_const_mul]
  unfold Dv
  ring

end net

end BstLean.Part151
