import BstLean.Part134Lam

/-!
# Part 136, item 1: the deterministic reduction for the stand-in factor `λ₁`

Role: `delegations/statements/p136-spec.md`. Everything here is for one fixed feature map
`h : U → ℝ^m` on a probability space `(U, μ)` (for the World network: `U = ℝ^N`, `μ` uniform on the
sphere, `h` the last hidden vector with `(M₁, M₂)` fixed).

* `hbar μ h`: the mean feature vector `h̄ = E_u h(u)`.
* `cov_frame`: if the Gram kernel `G(u, u′) = ⟨h(u), h(u′)⟩` is close in `L²(μ ⊗ μ)` to
  `a + c·⟨ℓ(u), ℓ(u′)⟩ + c₂·⟨ℓ₂(u), ℓ₂(u′)⟩` (distance `Δ`), and the families `ℓ`, `ℓ₂` have the
  frame bounds `τ`, `τ₂`, then the feature covariance has the operator bound
  `E_u ⟨h(u) − h̄, w⟩² ≤ (c·τ + c₂·τ₂ + Δ)·|w|²`.
* `det_frame`: with a bound `δ` of the diagonal `‖G(u, u) − d‖₂` also: `h̄ ≠ 0` and
  `E_u ⟨e(u), w⟩² ≤ ((c·τ + c₂·τ₂ + Δ)/s + Δ²/ε₂² + δ²/ε₁²)·|w|²` for the unit residual
  directions `e(u)` of Part 134 with `b = h̄`, for every `s ≤ d − ε₁ − (a + ε₂)²/(a − Δ)`, `s > 0`.
  This is the hypothesis `hL` of `s1_var` and `s1_mse` of Part 134.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part136

open MeasureTheory ProbabilityTheory
open BstLean.Part105 (BM bm_cauchy_schwarz)
open BstLean.Part130 BstLean.Part134

variable {U : Type*} [MeasurableSpace U] {m : ℕ}

/-- The mean feature vector `h̄ = E_u h(u)`. -/
noncomputable def hbar (μ : Measure U) (h : U → Fin m → ℝ) : Fin m → ℝ := fun j => ∫ u, h u j ∂μ

lemma bm_fst {F : U → ℝ} (hF : BM F) : BM (fun p : U × U => F p.1) := hF.comp measurable_fst

lemma bm_snd {F : U → ℝ} (hF : BM F) : BM (fun p : U × U => F p.2) := hF.comp measurable_snd

/-- `|r|² = |h|² − ⟨h, b⟩²/|b|²` for the residual `r = h − λ b` of Part 134. -/
lemma normSq_res {b : Fin m → ℝ} (hb : normSq b ≠ 0) (h : Fin m → ℝ) :
    normSq (res b h) = normSq h - (∑ j, h j * b j) ^ 2 / normSq b := by
  have hY : ∑ j, b j ^ 2 ≠ 0 := hb
  unfold res lam normSq
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have e : ∀ j, (h j - (∑ j, h j * b j) / (∑ j, b j ^ 2) * b j) ^ 2 =
      h j ^ 2 - 2 * ((∑ j, h j * b j) / (∑ j, b j ^ 2)) * (h j * b j) +
        ((∑ j, h j * b j) / (∑ j, b j ^ 2)) ^ 2 * b j ^ 2 := fun j => by ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  field_simp
  ring

/-- `⟨r, w⟩ = ⟨h, w − (⟨b, w⟩/|b|²) b⟩`. -/
lemma res_dot (b h w : Fin m → ℝ) :
    ∑ j, res b h j * w j =
      ∑ j, h j * (w j - (∑ j, b j * w j) / normSq b * b j) := by
  unfold res lam
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : ∀ j, (h j - (∑ j, h j * b j) / normSq b * b j) * w j =
      h j * w j - (∑ j, h j * b j) / normSq b * (b j * w j) := fun j => by ring
  have e2 : ∀ j, h j * (w j - (∑ j, b j * w j) / normSq b * b j) =
      h j * w j - (∑ j, b j * w j) / normSq b * (h j * b j) := fun j => by ring
  simp_rw [e1, e2]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

section det

variable (μ : Measure U) [IsProbabilityMeasure μ]

/-- `kernel_sum` of Part 134 on the product measure. -/
lemma kernel_sum_prod {κ : Type} [Fintype κ] {ξ : U → κ → ℝ} (hξ : ∀ k, BM (fun u => ξ u k))
    {α β : U → ℝ} (hα : BM α) (hβ : BM β) :
    ∫ p, (∑ k, ξ p.1 k * ξ p.2 k) * (α p.1 * β p.2) ∂(μ.prod μ) =
      ∑ k, (∫ u, α u * ξ u k ∂μ) * (∫ u, β u * ξ u k ∂μ) := by
  have b : BM (fun p : U × U => (∑ k, ξ p.1 k * ξ p.2 k) * (α p.1 * β p.2)) :=
    (bm_sum Finset.univ fun k _ => (bm_fst (hξ k)).mul (bm_snd (hξ k))).mul
      ((bm_fst hα).mul (bm_snd hβ))
  rw [integral_prod _ (b.integrable _)]
  exact kernel_sum μ hξ hα hβ

/-- Chebyshev for a bounded measurable function. -/
lemma cheb {f : U → ℝ} (hf : BM f) {ε : ℝ} (hε : 0 < ε) :
    μ.real {u | ε < |f u|} ≤ (∫ u, f u ^ 2 ∂μ) / ε ^ 2 := by
  have h1 := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := fun u => f u ^ 2)
    (Filter.Eventually.of_forall fun u => sq_nonneg _) (hf.sq.integrable μ) (ε ^ 2)
  have h2 : μ.real {u | ε < |f u|} ≤ μ.real {u | ε ^ 2 ≤ f u ^ 2} := by
    refine measureReal_mono (fun u hu => ?_) (measure_ne_top _ _)
    simp only [Set.mem_ofPred_eq] at hu ⊢
    rw [← sq_abs (f u)]
    exact pow_le_pow_left₀ hε.le hu.le 2
  have hε2 : 0 < ε ^ 2 := by positivity
  rw [le_div_iff₀ hε2]
  nlinarith

/-- **The operator bound of the feature covariance.** If the Gram kernel
`G(u, u′) = ⟨h(u), h(u′)⟩` has `‖G − a − c·⟨ℓ, ℓ′⟩ − c₂·⟨ℓ₂, ℓ₂′⟩‖_{L²(μ ⊗ μ)} ≤ Δ` and the
families `ℓ`, `ℓ₂` have the frame bounds `τ`, `τ₂`, then
`E_u ⟨h(u) − h̄, w⟩² ≤ (c·τ + c₂·τ₂ + Δ)·|w|²` for every `w`. -/
theorem cov_frame {h : U → Fin m → ℝ} (hh : ∀ j, BM (fun u => h u j))
    {κ κ₂ : Type} [Fintype κ] [Fintype κ₂]
    {ℓ : U → κ → ℝ} (hℓ : ∀ i, BM (fun u => ℓ u i))
    {ℓ₂ : U → κ₂ → ℝ} (hℓ₂ : ∀ i, BM (fun u => ℓ₂ u i))
    {τ τ₂ : ℝ} (hτ0 : 0 ≤ τ) (hτ₂0 : 0 ≤ τ₂)
    (hτ : ∀ v : κ → ℝ, ∫ u, (∑ i, ℓ u i * v i) ^ 2 ∂μ ≤ τ * ∑ i, v i ^ 2)
    (hτ₂ : ∀ v : κ₂ → ℝ, ∫ u, (∑ i, ℓ₂ u i * v i) ^ 2 ∂μ ≤ τ₂ * ∑ i, v i ^ 2)
    {a c c₂ Δ : ℝ} (hc : 0 ≤ c) (hc₂ : 0 ≤ c₂) (hΔ : 0 ≤ Δ)
    (hD : ∫ p, (∑ k, h p.1 k * h p.2 k - a - c * ∑ i, ℓ p.1 i * ℓ p.2 i -
      c₂ * ∑ i, ℓ₂ p.1 i * ℓ₂ p.2 i) ^ 2 ∂(μ.prod μ) ≤ Δ ^ 2)
    (w : Fin m → ℝ) :
    ∫ u, (∑ j, (h u j - hbar μ h j) * w j) ^ 2 ∂μ ≤
      (c * τ + c₂ * τ₂ + Δ) * ∑ j, w j ^ 2 := by
  have hbj : ∀ j, hbar μ h j = ∫ u, h u j ∂μ := fun j => rfl
  set g : U → ℝ := fun u => ∑ j, (h u j - hbar μ h j) * w j with hg
  have bgj : ∀ j, BM (fun u => (h u j - hbar μ h j) * w j) := fun j =>
    ((hh j).sub (BM.const (hbar μ h j))).mul (BM.const (w j))
  have bg : BM g := bm_sum Finset.univ fun j _ => bgj j
  have g0 : ∫ u, g u ∂μ = 0 := by
    simp only [hg]
    rw [integral_finsetSum _ fun j _ => (bgj j).integrable μ]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_mul_const, integral_sub ((hh j).integrable μ) (integrable_const _), hbj j]
    simp
  set Q := ∫ u, g u ^ 2 ∂μ with hQ
  have Q0 : 0 ≤ Q := integral_nonneg fun u => sq_nonneg _
  set v : Fin m → ℝ := fun j => ∫ u, g u * h u j ∂μ with hv
  have hW0 : 0 ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  -- `Q = ⟨v, w⟩`
  have e1 : Q = ∑ j, v j * w j := by
    have hgu : ∀ u, g u = ∑ j, h u j * w j - ∑ j, hbar μ h j * w j := by
      intro u
      simp only [hg, sub_mul, Finset.sum_sub_distrib]
    have e : ∀ u, g u ^ 2 = ∑ j, (g u * h u j) * w j - (∑ j, hbar μ h j * w j) * g u := by
      intro u
      have : g u ^ 2 = g u * (∑ j, h u j * w j - ∑ j, hbar μ h j * w j) := by
        rw [← hgu u, sq]
      rw [this, mul_sub, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by ring
      · ring
    have i1 : ∀ j ∈ Finset.univ, Integrable (fun u => (g u * h u j) * w j) μ := fun j _ =>
      ((bg.mul (hh j)).mul (BM.const (w j))).integrable μ
    rw [hQ]
    simp_rw [e]
    rw [integral_sub (integrable_finsetSum _ i1) ((bg.integrable μ).const_mul _),
      integral_finsetSum _ i1, integral_const_mul, g0, mul_zero, sub_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [integral_mul_const]
  -- `|v|²` as a kernel integral
  have e2 : ∑ j, v j ^ 2 =
      ∫ p, (∑ k, h p.1 k * h p.2 k) * (g p.1 * g p.2) ∂(μ.prod μ) := by
    rw [kernel_sum_prod μ hh bg bg]
    exact Finset.sum_congr rfl fun j _ => by rw [sq]
  set D : U × U → ℝ :=
    fun p => ∑ k, h p.1 k * h p.2 k - a - c * ∑ i, ℓ p.1 i * ℓ p.2 i -
      c₂ * ∑ i, ℓ₂ p.1 i * ℓ₂ p.2 i with hDdef
  have bG : BM (fun p : U × U => ∑ k, h p.1 k * h p.2 k) :=
    bm_sum Finset.univ fun k _ => (bm_fst (hh k)).mul (bm_snd (hh k))
  have bL : BM (fun p : U × U => ∑ i, ℓ p.1 i * ℓ p.2 i) :=
    bm_sum Finset.univ fun i _ => (bm_fst (hℓ i)).mul (bm_snd (hℓ i))
  have bL₂ : BM (fun p : U × U => ∑ i, ℓ₂ p.1 i * ℓ₂ p.2 i) :=
    bm_sum Finset.univ fun i _ => (bm_fst (hℓ₂ i)).mul (bm_snd (hℓ₂ i))
  have bD : BM D := ((bG.sub (BM.const a)).sub ((BM.const c).mul bL)).sub ((BM.const c₂).mul bL₂)
  have bgg : BM (fun p : U × U => g p.1 * g p.2) := (bm_fst bg).mul (bm_snd bg)
  have e3 : ∫ p, (∑ k, h p.1 k * h p.2 k) * (g p.1 * g p.2) ∂(μ.prod μ) =
      c * ∑ i, (∫ u, g u * ℓ u i ∂μ) ^ 2 + c₂ * ∑ i, (∫ u, g u * ℓ₂ u i ∂μ) ^ 2 +
        ∫ p, (g p.1 * g p.2) * D p ∂(μ.prod μ) := by
    have e : ∀ p : U × U, (∑ k, h p.1 k * h p.2 k) * (g p.1 * g p.2) =
        ((a * (g p.1 * g p.2) + c * ((∑ i, ℓ p.1 i * ℓ p.2 i) * (g p.1 * g p.2))) +
          c₂ * ((∑ i, ℓ₂ p.1 i * ℓ₂ p.2 i) * (g p.1 * g p.2))) +
          (g p.1 * g p.2) * D p := by
      intro p
      simp only [hDdef]
      ring
    have j1 : Integrable (fun p : U × U => a * (g p.1 * g p.2)) (μ.prod μ) :=
      ((BM.const a).mul bgg).integrable _
    have j2 : Integrable (fun p : U × U => c * ((∑ i, ℓ p.1 i * ℓ p.2 i) * (g p.1 * g p.2)))
        (μ.prod μ) := ((BM.const c).mul (bL.mul bgg)).integrable _
    have j3 : Integrable (fun p : U × U => (g p.1 * g p.2) * D p) (μ.prod μ) :=
      (bgg.mul bD).integrable _
    have j2' : Integrable (fun p : U × U =>
        c₂ * ((∑ i, ℓ₂ p.1 i * ℓ₂ p.2 i) * (g p.1 * g p.2))) (μ.prod μ) :=
      ((BM.const c₂).mul (bL₂.mul bgg)).integrable _
    have j12 : Integrable (fun p : U × U => a * (g p.1 * g p.2) +
        c * ((∑ i, ℓ p.1 i * ℓ p.2 i) * (g p.1 * g p.2))) (μ.prod μ) := j1.add j2
    have j123 : Integrable (fun p : U × U => a * (g p.1 * g p.2) +
        c * ((∑ i, ℓ p.1 i * ℓ p.2 i) * (g p.1 * g p.2)) +
        c₂ * ((∑ i, ℓ₂ p.1 i * ℓ₂ p.2 i) * (g p.1 * g p.2))) (μ.prod μ) := j12.add j2'
    simp_rw [e]
    rw [integral_add j123 j3, integral_add j12 j2', integral_add j1 j2, integral_const_mul,
      integral_const_mul, integral_const_mul,
      integral_prod_mul (fun u => g u) (fun u => g u), g0, kernel_sum_prod μ hℓ bg bg,
      kernel_sum_prod μ hℓ₂ bg bg]
    have e1' : ∑ i, (∫ u, g u * ℓ u i ∂μ) * (∫ u, g u * ℓ u i ∂μ) =
        ∑ i, (∫ u, g u * ℓ u i ∂μ) ^ 2 := Finset.sum_congr rfl fun i _ => by rw [sq]
    have e2' : ∑ i, (∫ u, g u * ℓ₂ u i ∂μ) * (∫ u, g u * ℓ₂ u i ∂μ) =
        ∑ i, (∫ u, g u * ℓ₂ u i ∂μ) ^ 2 := Finset.sum_congr rfl fun i _ => by rw [sq]
    rw [e1', e2']
    ring
  have e4 : ∑ i, (∫ u, g u * ℓ u i ∂μ) ^ 2 ≤ τ * Q := frame_bound μ hℓ bg hτ0 hτ
  have e4' : ∑ i, (∫ u, g u * ℓ₂ u i ∂μ) ^ 2 ≤ τ₂ * Q := frame_bound μ hℓ₂ bg hτ₂0 hτ₂
  have e5 : ∫ p, (g p.1 * g p.2) * D p ∂(μ.prod μ) ≤ Q * Δ := by
    have cs := bm_cauchy_schwarz (μ.prod μ) bgg bD
    have e : ∫ p : U × U, (g p.1 * g p.2) ^ 2 ∂(μ.prod μ) = Q * Q := by
      simp_rw [mul_pow]
      rw [integral_prod_mul (fun u => g u ^ 2) (fun u => g u ^ 2)]
    rw [e] at cs
    have hD' : ∫ p, D p ^ 2 ∂(μ.prod μ) ≤ Δ ^ 2 := hD
    have h2 : (∫ p, (g p.1 * g p.2) * D p ∂(μ.prod μ)) ^ 2 ≤ (Q * Δ) ^ 2 := by
      refine cs.trans ?_
      have := mul_le_mul_of_nonneg_left hD' (mul_nonneg Q0 Q0)
      nlinarith
    exact le_of_abs_le (abs_le_of_sq_le_sq h2 (mul_nonneg Q0 hΔ))
  have e6 : ∑ j, v j ^ 2 ≤ (c * τ + c₂ * τ₂ + Δ) * Q := by
    rw [e2, e3]
    have := mul_le_mul_of_nonneg_left e4 hc
    have := mul_le_mul_of_nonneg_left e4' hc₂
    nlinarith
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w
  rw [← e1] at cs
  rcases Q0.eq_or_lt with h0 | hpos
  · rw [← h0]
    have : 0 ≤ c * τ + c₂ * τ₂ + Δ := by positivity
    positivity
  · have h3 : Q * Q ≤ ((c * τ + c₂ * τ₂ + Δ) * ∑ j, w j ^ 2) * Q := by
      have := mul_le_mul_of_nonneg_right e6 hW0
      nlinarith
    exact le_of_mul_le_mul_right h3 hpos

/-- **The deterministic reduction** (item 1). Hypotheses: the Gram kernel `G = ⟨h, h′⟩` is within
`Δ` of `a + c·⟨ℓ, ℓ′⟩ + c₂·⟨ℓ₂, ℓ₂′⟩` in `L²(μ ⊗ μ)`, the diagonal `G(u, u)` is within `δ` of `d`
in `L²(μ)`, the families `ℓ`, `ℓ₂` are centred with frame bounds `τ`, `τ₂`. Conclusion: `h̄ ≠ 0`,
and the unit residual directions `e(u)` (Part 134, `b = h̄`) have the frame bound
`(c·τ + c₂·τ₂ + Δ)/s + Δ²/ε₂² + δ²/ε₁²` for every `0 < s ≤ d − ε₁ − (a + ε₂)²/(a − Δ)`. -/
theorem det_frame {h : U → Fin m → ℝ} (hh : ∀ j, BM (fun u => h u j))
    {κ κ₂ : Type} [Fintype κ] [Fintype κ₂]
    {ℓ : U → κ → ℝ} (hℓ : ∀ i, BM (fun u => ℓ u i))
    {ℓ₂ : U → κ₂ → ℝ} (hℓ₂ : ∀ i, BM (fun u => ℓ₂ u i))
    (hℓ0 : ∀ i, ∫ u, ℓ u i ∂μ = 0) (hℓ₂0 : ∀ i, ∫ u, ℓ₂ u i ∂μ = 0)
    {τ τ₂ : ℝ} (hτ0 : 0 ≤ τ) (hτ₂0 : 0 ≤ τ₂)
    (hτ : ∀ v : κ → ℝ, ∫ u, (∑ i, ℓ u i * v i) ^ 2 ∂μ ≤ τ * ∑ i, v i ^ 2)
    (hτ₂ : ∀ v : κ₂ → ℝ, ∫ u, (∑ i, ℓ₂ u i * v i) ^ 2 ∂μ ≤ τ₂ * ∑ i, v i ^ 2)
    {a c c₂ Δ d δ ε₁ ε₂ s : ℝ} (hc : 0 ≤ c) (hc₂ : 0 ≤ c₂) (hΔ : 0 ≤ Δ) (hε₁ : 0 < ε₁)
    (hε₂ : 0 < ε₂) (haΔ : Δ < a)
    (hD : ∫ p, (∑ k, h p.1 k * h p.2 k - a - c * ∑ i, ℓ p.1 i * ℓ p.2 i -
      c₂ * ∑ i, ℓ₂ p.1 i * ℓ₂ p.2 i) ^ 2 ∂(μ.prod μ) ≤ Δ ^ 2)
    (hd : ∫ u, (normSq (h u) - d) ^ 2 ∂μ ≤ δ ^ 2)
    (hs : 0 < s) (hsle : s ≤ d - ε₁ - (a + ε₂) ^ 2 / (a - Δ)) :
    hbar μ h ≠ 0 ∧ ∀ w : Fin m → ℝ,
      ∫ u, (∑ j, eDir (hbar μ h) (h u) j * w j) ^ 2 ∂μ ≤
        ((c * τ + c₂ * τ₂ + Δ) / s + Δ ^ 2 / ε₂ ^ 2 + δ ^ 2 / ε₁ ^ 2) * ∑ j, w j ^ 2 := by
  have hbj : ∀ j, hbar μ h j = ∫ u, h u j ∂μ := fun j => rfl
  have hmeas : Measurable h := measurable_pi_iff.mpr fun j => (hh j).meas
  set D : U × U → ℝ :=
    fun p => ∑ k, h p.1 k * h p.2 k - a - c * ∑ i, ℓ p.1 i * ℓ p.2 i -
      c₂ * ∑ i, ℓ₂ p.1 i * ℓ₂ p.2 i with hDdef
  have bG : BM (fun p : U × U => ∑ k, h p.1 k * h p.2 k) :=
    bm_sum Finset.univ fun k _ => (bm_fst (hh k)).mul (bm_snd (hh k))
  have bL : BM (fun p : U × U => ∑ i, ℓ p.1 i * ℓ p.2 i) :=
    bm_sum Finset.univ fun i _ => (bm_fst (hℓ i)).mul (bm_snd (hℓ i))
  have bL₂ : BM (fun p : U × U => ∑ i, ℓ₂ p.1 i * ℓ₂ p.2 i) :=
    bm_sum Finset.univ fun i _ => (bm_fst (hℓ₂ i)).mul (bm_snd (hℓ₂ i))
  have bD : BM D := ((bG.sub (BM.const a)).sub ((BM.const c).mul bL)).sub ((BM.const c₂).mul bL₂)
  have hD' : ∫ p, D p ^ 2 ∂(μ.prod μ) ≤ Δ ^ 2 := hD
  set X : U → ℝ := fun u => ∑ j, h u j * hbar μ h j with hX
  have bX : BM X := bm_sum Finset.univ fun j _ => (hh j).mul (BM.const _)
  -- `X(u) − a` is the integral of the kernel error over the second input
  have eX : ∀ u, X u - a = ∫ u', D (u, u') ∂μ := by
    intro u
    have i1 : Integrable (fun u' => ∑ k, h u k * h u' k) μ :=
      integrable_finsetSum _ fun k _ => ((hh k).integrable μ).const_mul _
    have i2 : Integrable (fun u' => c * ∑ i, ℓ u i * ℓ u' i) μ :=
      (integrable_finsetSum _ fun i _ => ((hℓ i).integrable μ).const_mul _).const_mul _
    have v1 : ∫ u', ∑ k, h u k * h u' k ∂μ = X u := by
      rw [integral_finsetSum _ fun k _ => ((hh k).integrable μ).const_mul _]
      simp only [integral_const_mul, hX, hbj]
    have i3 : Integrable (fun u' => c₂ * ∑ i, ℓ₂ u i * ℓ₂ u' i) μ :=
      (integrable_finsetSum _ fun i _ => ((hℓ₂ i).integrable μ).const_mul _).const_mul _
    have v2 : ∫ u', c * ∑ i, ℓ u i * ℓ u' i ∂μ = 0 := by
      rw [integral_const_mul, integral_finsetSum _ fun i _ => ((hℓ i).integrable μ).const_mul _]
      simp only [integral_const_mul, hℓ0, mul_zero, Finset.sum_const_zero]
    have v3 : ∫ u', c₂ * ∑ i, ℓ₂ u i * ℓ₂ u' i ∂μ = 0 := by
      rw [integral_const_mul,
        integral_finsetSum _ fun i _ => ((hℓ₂ i).integrable μ).const_mul _]
      simp only [integral_const_mul, hℓ₂0, mul_zero, Finset.sum_const_zero]
    have i1a : Integrable (fun u' => ∑ k, h u k * h u' k - a) μ := i1.sub (integrable_const a)
    have i12 : Integrable (fun u' => ∑ k, h u k * h u' k - a - c * ∑ i, ℓ u i * ℓ u' i) μ :=
      i1a.sub i2
    simp only [hDdef]
    rw [integral_sub i12 i3, integral_sub i1a i2, integral_sub i1 (integrable_const a),
      v1, v2, v3]
    simp
  have hXa : ∫ u, (X u - a) ^ 2 ∂μ ≤ Δ ^ 2 := by
    have pt : ∀ u, (∫ u', D (u, u') ∂μ) ^ 2 ≤ ∫ u', D (u, u') ^ 2 ∂μ := by
      intro u
      have bDu : BM (fun u' => D (u, u')) := bD.comp (measurable_const.prodMk measurable_id)
      have := bm_cauchy_schwarz μ bDu (BM.const 1)
      simpa using this
    calc ∫ u, (X u - a) ^ 2 ∂μ = ∫ u, (∫ u', D (u, u') ∂μ) ^ 2 ∂μ := by simp_rw [eX]
      _ ≤ ∫ u, ∫ u', D (u, u') ^ 2 ∂μ ∂μ :=
          integral_mono ((bD.integral_right μ).sq.integrable μ)
            ((bD.sq.integral_right μ).integrable μ) pt
      _ = ∫ p, D p ^ 2 ∂(μ.prod μ) := (integral_prod _ (bD.sq.integrable _)).symm
      _ ≤ Δ ^ 2 := hD'
  -- `Y = |h̄|²`
  set Y := normSq (hbar μ h) with hY
  have eY : Y - a = ∫ u, (X u - a) ∂μ := by
    rw [integral_sub (bX.integrable μ) (integrable_const a)]
    have : ∫ u, X u ∂μ = Y := by
      simp only [hX]
      rw [integral_finsetSum _ fun j _ => ((hh j).integrable μ).mul_const _]
      simp only [integral_mul_const, ← hbj, hY, normSq]
      exact Finset.sum_congr rfl fun j _ => by rw [sq]
    rw [this]
    simp
  have hYa : |Y - a| ≤ Δ := by
    rw [eY]
    refine abs_le_of_sq_le_sq ?_ hΔ
    have := bm_cauchy_schwarz μ (bX.sub (BM.const a)) (BM.const 1)
    have h1 : (∫ u, (X u - a) ∂μ) ^ 2 ≤ ∫ u, (X u - a) ^ 2 ∂μ := by simpa using this
    exact h1.trans hXa
  have ha0 : 0 < a := lt_of_le_of_lt hΔ haΔ
  have haΔ' : 0 < a - Δ := by linarith
  have hYge : a - Δ ≤ Y := by linarith [(abs_le.mp hYa).1]
  have hYpos : 0 < Y := lt_of_lt_of_le haΔ' hYge
  have hY0 : normSq (hbar μ h) ≠ 0 := hYpos.ne'
  have hbne : hbar μ h ≠ 0 := by
    intro h0
    apply hY0
    rw [h0]
    simp [normSq]
  refine ⟨hbne, fun w => ?_⟩
  -- the bad set of inputs
  have bn : BM (fun u => normSq (h u)) := by
    change BM (fun u => ∑ j, h u j ^ 2)
    exact bm_sum Finset.univ fun j _ => (hh j).sq
  set T : Set U := {u | ε₂ < |X u - a|} ∪ {u | ε₁ < |normSq (h u) - d|} with hT
  have mT : MeasurableSet T :=
    (measurableSet_lt measurable_const (bX.meas.sub measurable_const).abs).union
      (measurableSet_lt measurable_const (bn.meas.sub measurable_const).abs)
  have hμT : μ.real T ≤ Δ ^ 2 / ε₂ ^ 2 + δ ^ 2 / ε₁ ^ 2 := by
    refine (measureReal_union_le _ _).trans (add_le_add ?_ ?_)
    · exact (cheb μ (bX.sub (BM.const a)) hε₂).trans
        (div_le_div_of_nonneg_right hXa (by positivity))
    · exact (cheb μ (bn.sub (BM.const d)) hε₁).trans
        (div_le_div_of_nonneg_right hd (by positivity))
  have hr : ∀ u, u ∉ T → s ≤ normSq (res (hbar μ h) (h u)) := by
    intro u hu
    simp only [hT, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hu
    obtain ⟨h1, h2⟩ := hu
    rw [normSq_res hY0]
    have hXu := abs_le.mp h1
    have hX2 : X u ^ 2 ≤ (a + ε₂) ^ 2 := by
      apply sq_le_sq' <;> linarith
    have hq : X u ^ 2 / Y ≤ (a + ε₂) ^ 2 / (a - Δ) :=
      div_le_div₀ (sq_nonneg _) hX2 haΔ' hYge
    have hnu := abs_le.mp h2
    have : (∑ j, h u j * hbar μ h j) ^ 2 / normSq (hbar μ h) = X u ^ 2 / Y := rfl
    rw [this]
    linarith
  -- the projected test vector
  set β := (∑ j, hbar μ h j * w j) / normSq (hbar μ h) with hβ
  set w' : Fin m → ℝ := fun j => w j - β * hbar μ h j with hw'
  have hsumb : ∑ j, hbar μ h j * hbar μ h j = Y := by
    simp only [hY, normSq]
    exact Finset.sum_congr rfl fun j _ => by rw [sq]
  have hβY : β * Y = ∑ j, hbar μ h j * w j := by
    rw [hβ]
    exact div_mul_cancel₀ _ hYpos.ne'
  have hw'0 : ∑ j, hbar μ h j * w' j = 0 := by
    have e : ∀ j, hbar μ h j * w' j =
        hbar μ h j * w j - β * (hbar μ h j * hbar μ h j) := fun j => by
      simp only [hw']; ring
    simp_rw [e]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumb, hβY]
    ring
  have hw'n : ∑ j, w' j ^ 2 ≤ ∑ j, w j ^ 2 := by
    have e : ∀ j, w' j ^ 2 = w j ^ 2 - 2 * β * (hbar μ h j * w j) +
        β ^ 2 * (hbar μ h j * hbar μ h j) := fun j => by
      simp only [hw']; ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hsumb, ← hβY]
    nlinarith [mul_nonneg (sq_nonneg β) hYpos.le]
  have er : ∀ u, ∑ j, res (hbar μ h) (h u) j * w j =
      ∑ j, (h u j - hbar μ h j) * w' j := by
    intro u
    rw [res_dot]
    have e : ∀ j, (h u j - hbar μ h j) * w' j = h u j * w' j - hbar μ h j * w' j :=
      fun j => by ring
    simp_rw [e]
    rw [Finset.sum_sub_distrib, hw'0, sub_zero]
  have hA := cov_frame μ hh hℓ hℓ₂ hτ0 hτ₂0 hτ hτ₂ hc hc₂ hΔ hD w'
  have hW0 : 0 ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  -- the pointwise bound of the integrand
  have pt : ∀ u, (∑ j, eDir (hbar μ h) (h u) j * w j) ^ 2 ≤
      s⁻¹ * (∑ j, (h u j - hbar μ h j) * w' j) ^ 2 +
        T.indicator (fun _ => ∑ j, w j ^ 2) u := by
    intro u
    by_cases hu : u ∈ T
    · rw [Set.indicator_of_mem hu]
      have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun j => eDir (hbar μ h) (h u) j) w
      have h1 : ∑ j, eDir (hbar μ h) (h u) j ^ 2 ≤ 1 := by
        rcases eDir_unit_or_zero (hbar μ h) (h u) with h1 | h1
        · exact h1.le
        · rw [h1]; simp
      have h3 : 0 ≤ s⁻¹ * (∑ j, (h u j - hbar μ h j) * w' j) ^ 2 := by positivity
      nlinarith
    · rw [Set.indicator_of_notMem hu, add_zero]
      have hru := hr u hu
      have hnr : 0 < normSq (res (hbar μ h) (h u)) := lt_of_lt_of_le hs hru
      have e : ∑ j, eDir (hbar μ h) (h u) j * w j =
          (Real.sqrt (normSq (res (hbar μ h) (h u))))⁻¹ *
            ∑ j, res (hbar μ h) (h u) j * w j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [eDir, Pi.smul_apply, smul_eq_mul]
        ring
      rw [e, mul_pow, inv_pow, Real.sq_sqrt hnr.le, er u]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hs hru) (sq_nonneg _)
  have hm : Measurable (fun u => (∑ j, eDir (hbar μ h) (h u) j * w j) ^ 2) :=
    (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp ((measurable_eDir (hbar μ h)).comp hmeas)).mul_const _
      ).pow_const 2
  have ptb : ∀ u, (∑ j, eDir (hbar μ h) (h u) j * w j) ^ 2 ≤ ∑ j, w j ^ 2 := by
    intro u
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => eDir (hbar μ h) (h u) j) w
    have h1 : ∑ j, eDir (hbar μ h) (h u) j ^ 2 ≤ 1 := by
      rcases eDir_unit_or_zero (hbar μ h) (h u) with h1 | h1
      · exact h1.le
      · rw [h1]; simp
    nlinarith
  have i1 : Integrable (fun u => (∑ j, eDir (hbar μ h) (h u) j * w j) ^ 2) μ :=
    Integrable.of_bound hm.aestronglyMeasurable (∑ j, w j ^ 2)
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact ptb u)
  have bA : BM (fun u => (∑ j, (h u j - hbar μ h j) * w' j) ^ 2) :=
    (bm_sum Finset.univ fun j _ =>
      ((hh j).sub (BM.const (hbar μ h j))).mul (BM.const (w' j))).sq
  have i2 : Integrable (fun u => s⁻¹ * (∑ j, (h u j - hbar μ h j) * w' j) ^ 2) μ :=
    (bA.integrable μ).const_mul _
  have i3 : Integrable (T.indicator (fun _ : U => ∑ j, w j ^ 2)) μ :=
    (integrable_const _).indicator mT
  calc ∫ u, (∑ j, eDir (hbar μ h) (h u) j * w j) ^ 2 ∂μ
      ≤ ∫ u, (s⁻¹ * (∑ j, (h u j - hbar μ h j) * w' j) ^ 2 +
          T.indicator (fun _ => ∑ j, w j ^ 2) u) ∂μ := integral_mono i1 (i2.add i3) pt
    _ = s⁻¹ * ∫ u, (∑ j, (h u j - hbar μ h j) * w' j) ^ 2 ∂μ +
          μ.real T * ∑ j, w j ^ 2 := by
        rw [integral_add i2 i3, integral_const_mul, integral_indicator mT, setIntegral_const,
          smul_eq_mul]
    _ ≤ s⁻¹ * ((c * τ + c₂ * τ₂ + Δ) * ∑ j, w j ^ 2) +
          (Δ ^ 2 / ε₂ ^ 2 + δ ^ 2 / ε₁ ^ 2) * ∑ j, w j ^ 2 := by
        have hcτ : 0 ≤ c * τ + c₂ * τ₂ + Δ := by positivity
        refine add_le_add (mul_le_mul_of_nonneg_left (hA.trans ?_) (inv_nonneg.mpr hs.le))
          (mul_le_mul_of_nonneg_right hμT hW0)
        exact mul_le_mul_of_nonneg_left hw'n hcτ
    _ = ((c * τ + c₂ * τ₂ + Δ) / s + Δ ^ 2 / ε₂ ^ 2 + δ ^ 2 / ε₁ ^ 2) * ∑ j, w j ^ 2 := by
        rw [div_eq_mul_inv]
        ring

end det

end BstLean.Part136
