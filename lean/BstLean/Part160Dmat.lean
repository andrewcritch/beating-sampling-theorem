import BstLean.Part160Defs

/-!
# Part 160 (file `Dmat`): the Poincaré matrix bound `t_A Cov_x(h) ≼ D`

Role: `delegations/statements/p160-spec.md`, item 4. Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `proofs/option-n/theorem7-04-frame-numerator.tex`, Lemma `t7:p04:dual`, formula
`t7:p04:poincare`, first inequality: `t_A Cov_x(h) ≼ D`, `D = E_ξ B_ξ B_ξᵀ`,
`B_ξ = √(t_A w(ξ))·J_x Π_x`, `w = τ₀²/|y|²`. In Lean it is a statement about quadratic forms;
`Bᵀ v` is the row vector `v ᵥ* jacT A₁ A₂ x` (`jacT = 𝒥(x) Π_x` of Part 153).

* `Dquad A₁ A₂ c τ v = t·τ²·∫ |v ᵥ* 𝒥(x)Π_x|²/|y|² dξ = vᵀ D v`.
* `dot_sph_local`: the local Lipschitz constant of `x ↦ ⟨v, h(x)⟩` on the unit sphere is the
  length of the exact tangential gradient `|v ᵥ* 𝒥(x)Π_x|`.
* `gradSq_dot_le`: `|∇_ξ ⟨v, h(x(ξ))⟩|² ≤ τ²·|v ᵥ* 𝒥(x)Π_x|²/|y|²`.
* **`cov_hid2_le_D`**: `t·Var_ξ⟨v, h(x)⟩ ≤ Dquad v` (every `A₁`, `A₂`, `c`, `τ > 0`, `n ≥ 6`).
* `Dquad_le_XiS`: `Dquad v ≤ Ξ·|v|²` (so `cov_hid2_le` of Part 153 is a corollary:
  `cov_hid2_le_of_D`).
* `cov_at_of_Dquad`: `COV_at D c N` from `Dquad v ≤ N·(γ_A/n)·|v|²` for every `v`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part157
open BstLean.Part148 (EuLip)
open BstLean.Part151 (jac JacAt lemmaJ_shift)
open BstLean.Part153

section loc

variable {n m₁ m₂ : ℕ}

/-- `|v ᵥ* M| ≤ opN M·|v|`. -/
lemma nrm_vecMul_le {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (v : Fin p → ℝ) :
    nrm (v ᵥ* M) ≤ opN M * nrm v := by
  have h := bil_le_opN_mul M v (v ᵥ* M)
  have e : v ⬝ᵥ M *ᵥ (v ᵥ* M) = nrm (v ᵥ* M) * nrm (v ᵥ* M) := by
    rw [Matrix.dotProduct_mulVec, dot_self_cr, ← nrm_sq]; ring
  have e1 : √(∑ i, v i ^ 2) = nrm v := rfl
  have e2 : √(∑ j, (v ᵥ* M) j ^ 2) = nrm (v ᵥ* M) := rfl
  rw [e, e1, e2] at h
  have h0 := nrm_nonneg (v ᵥ* M)
  by_cases hz : nrm (v ᵥ* M) = 0
  · rw [hz]; exact mul_nonneg (opN_nonneg _) (nrm_nonneg _)
  · have hpos : 0 < nrm (v ᵥ* M) := lt_of_le_of_ne h0 (Ne.symm hz)
    have : nrm (v ᵥ* M) * nrm (v ᵥ* M) ≤ (opN M * nrm v) * nrm (v ᵥ* M) := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_right this hpos

/-- The local estimate on the unit sphere with the exact tangential gradient, at `x` on the ray
of a point `y = ρx` where the Jacobian formula holds. -/
lemma dot_sph_local_aux {A₁ : Matrix (Fin m₁) (Fin n) ℝ} {A₂ : Matrix (Fin m₂) (Fin m₁) ℝ}
    {x : Fin n → ℝ} {ρ : ℝ} (hρ0 : 0 < ρ) (hx1 : normSq x = 1) (hJ : JacAt A₁ A₂ (ρ • x))
    (v : Fin m₂ → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ ∀ x' : Fin n → ℝ, normSq x' = 1 → nrm (x' - x) < r →
      |v ⬝ᵥ hid2 A₁ A₂ x' - v ⬝ᵥ hid2 A₁ A₂ x| ≤
        (nrm (v ᵥ* jacT A₁ A₂ x) + δ) * nrm (x' - x) := by
  have hv0 := nrm_nonneg v
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁ : ℝ, δ₁ = δ / (2 * (nrm v + 1)) := ⟨_, rfl⟩
  have hδ₁0 : 0 < δ₁ := by rw [hδ₁]; positivity
  have hvδ : nrm v * δ₁ ≤ δ / 2 := by
    rw [hδ₁, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨r₁, hr₁, hA⟩ := jacAt_local hJ hδ₁0
  rw [jac_smul _ _ hρ0] at hA
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = |v ⬝ᵥ jac A₁ A₂ x *ᵥ x| / 2 := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine ⟨min (r₁ / ρ) (δ / (2 * C + 1)), lt_min (div_pos hr₁ hρ0) (by positivity),
    fun x' hx'1 hd => ?_⟩
  have hd0 := nrm_nonneg (x' - x)
  have hd1 : nrm (x' - x) < r₁ / ρ := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : nrm (x' - x) < δ / (2 * C + 1) := lt_of_lt_of_le hd (min_le_right _ _)
  have hCd : C * nrm (x' - x) ≤ δ / 2 := by
    have h5 : nrm (x' - x) * (2 * C + 1) < δ := (lt_div_iff₀ (by positivity)).mp hd2
    nlinarith
  have ez : ρ • x' - ρ • x = ρ • (x' - x) := by rw [smul_sub]
  have hz : nrm (ρ • x' - ρ • x) < r₁ := by
    rw [ez, nrm_smul, abs_of_pos hρ0]
    calc ρ * nrm (x' - x) < ρ * (r₁ / ρ) := mul_lt_mul_of_pos_left hd1 hρ0
      _ = r₁ := by field_simp
  have h1 := hA (ρ • x') hz
  have e1 : hid2 A₁ A₂ (ρ • x') - hid2 A₁ A₂ (ρ • x) - jac A₁ A₂ x *ᵥ (ρ • x' - ρ • x) =
      ρ • (hid2 A₁ A₂ x' - hid2 A₁ A₂ x - jac A₁ A₂ x *ᵥ (x' - x)) := by
    rw [hid2_smul _ _ hρ0.le, hid2_smul _ _ hρ0.le, ez, Matrix.mulVec_smul, smul_sub, smul_sub]
  have h2 : nrm (hid2 A₁ A₂ x' - hid2 A₁ A₂ x - jac A₁ A₂ x *ᵥ (x' - x)) ≤
      δ₁ * nrm (x' - x) := by
    rw [e1, ez, nrm_smul, nrm_smul, abs_of_pos hρ0] at h1
    have h6 : ρ * nrm (hid2 A₁ A₂ x' - hid2 A₁ A₂ x - jac A₁ A₂ x *ᵥ (x' - x)) ≤
        ρ * (δ₁ * nrm (x' - x)) := by
      rw [show ρ * (δ₁ * nrm (x' - x)) = δ₁ * (ρ * nrm (x' - x)) by ring]
      exact h1
    exact le_of_mul_le_mul_left h6 hρ0
  have hdot : x ⬝ᵥ (x' - x) = -(nrm (x' - x) ^ 2) / 2 := by
    have e2 : nrm (x' - x) ^ 2 = normSq (x' - x) := nrm_sq _
    have e3 : normSq (x' - x) = normSq x' - 2 * 1 * (x' ⬝ᵥ x) + 1 ^ 2 * normSq x := by
      have := normSq_sub_smul x' x 1
      rwa [one_smul] at this
    have e4 : x ⬝ᵥ x = normSq x := dot_self_cr x
    rw [dotProduct_sub, e4, e2, e3, hx1, hx'1, dotProduct_comm x' x]
    ring
  have hJdec : jac A₁ A₂ x *ᵥ (x' - x) =
      jacT A₁ A₂ x *ᵥ (x' - x) + (x ⬝ᵥ (x' - x)) • (jac A₁ A₂ x *ᵥ x) := by
    unfold jacT
    rw [← Matrix.mulVec_mulVec, projT_mulVec_sj,
      Matrix.mulVec_sub (jac A₁ A₂ x) (x' - x) ((x ⬝ᵥ (x' - x)) • x), Matrix.mulVec_smul,
      sub_add_cancel]
  have habs : |-(nrm (x' - x) ^ 2) / 2| = nrm (x' - x) ^ 2 / 2 := by
    rw [neg_div, abs_neg, abs_of_nonneg (by positivity)]
  -- the decomposition of the scalar increment
  have edec : v ⬝ᵥ hid2 A₁ A₂ x' - v ⬝ᵥ hid2 A₁ A₂ x =
      v ⬝ᵥ (hid2 A₁ A₂ x' - hid2 A₁ A₂ x - jac A₁ A₂ x *ᵥ (x' - x)) +
        ((v ᵥ* jacT A₁ A₂ x) ⬝ᵥ (x' - x) +
          (x ⬝ᵥ (x' - x)) * (v ⬝ᵥ jac A₁ A₂ x *ᵥ x)) := by
    rw [← Matrix.dotProduct_mulVec, ← smul_eq_mul, ← dotProduct_smul, ← dotProduct_add, ← hJdec,
      ← dotProduct_add, sub_add_cancel, dotProduct_sub]
  have t1 : |v ⬝ᵥ (hid2 A₁ A₂ x' - hid2 A₁ A₂ x - jac A₁ A₂ x *ᵥ (x' - x))| ≤
      δ / 2 * nrm (x' - x) := by
    refine (abs_dot_le_nrm _ _).trans ?_
    calc nrm v * nrm (hid2 A₁ A₂ x' - hid2 A₁ A₂ x - jac A₁ A₂ x *ᵥ (x' - x))
        ≤ nrm v * (δ₁ * nrm (x' - x)) := mul_le_mul_of_nonneg_left h2 hv0
      _ = nrm v * δ₁ * nrm (x' - x) := by ring
      _ ≤ δ / 2 * nrm (x' - x) := mul_le_mul_of_nonneg_right hvδ hd0
  have t2 := abs_dot_le_nrm (v ᵥ* jacT A₁ A₂ x) (x' - x)
  have t3 : |(x ⬝ᵥ (x' - x)) * (v ⬝ᵥ jac A₁ A₂ x *ᵥ x)| ≤ δ / 2 * nrm (x' - x) := by
    rw [abs_mul, hdot, habs]
    calc nrm (x' - x) ^ 2 / 2 * |v ⬝ᵥ jac A₁ A₂ x *ᵥ x| = C * nrm (x' - x) * nrm (x' - x) := by
          rw [hC]; ring
      _ ≤ δ / 2 * nrm (x' - x) := mul_le_mul_of_nonneg_right hCd hd0
  rw [edec]
  calc _ ≤ |v ⬝ᵥ (hid2 A₁ A₂ x' - hid2 A₁ A₂ x - jac A₁ A₂ x *ᵥ (x' - x))| +
        (|(v ᵥ* jacT A₁ A₂ x) ⬝ᵥ (x' - x)| +
          |(x ⬝ᵥ (x' - x)) * (v ⬝ᵥ jac A₁ A₂ x *ᵥ x)|) :=
        (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    _ ≤ δ / 2 * nrm (x' - x) + (nrm (v ᵥ* jacT A₁ A₂ x) * nrm (x' - x) +
          δ / 2 * nrm (x' - x)) := add_le_add t1 (add_le_add t2 t3)
    _ = _ := by ring

/-- **The local Lipschitz constant of `x ↦ ⟨v, h(x)⟩` on the unit sphere is the length of the
exact tangential gradient**: at `y ≠ 0` where the Jacobian formula holds, for unit vectors `x'`
near `x = y/|y|`: `|⟨v, h(x')⟩ − ⟨v, h(x)⟩| ≤ (|v ᵥ* 𝒥(x)Π_x| + δ)·|x' − x|`. -/
theorem dot_sph_local {A₁ : Matrix (Fin m₁) (Fin n) ℝ} {A₂ : Matrix (Fin m₂) (Fin m₁) ℝ}
    {y : Fin n → ℝ} (hy : normSq y ≠ 0) (hJ : JacAt A₁ A₂ y) (v : Fin m₂ → ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ ∀ x' : Fin n → ℝ, normSq x' = 1 → nrm (x' - sphPt y) < r →
      |v ⬝ᵥ hid2 A₁ A₂ x' - v ⬝ᵥ hid2 A₁ A₂ (sphPt y)| ≤
        (nrm (v ᵥ* jacT A₁ A₂ (sphPt y)) + δ) * nrm (x' - sphPt y) := by
  have hs0 : 0 < normSq y := lt_of_le_of_ne (normSq_nonneg y) (Ne.symm hy)
  have hρ0 : 0 < √(normSq y) := Real.sqrt_pos.mpr hs0
  have hyx : √(normSq y) • sphPt y = y := by
    rw [sphPt_eq' hy, smul_smul, mul_one_div_cancel hρ0.ne', one_smul]
  have hx1 : normSq (sphPt y) = 1 := by
    rw [sphPt_eq' hy, normSq_smul, one_div, inv_pow, Real.sq_sqrt hs0.le]
    exact inv_mul_cancel₀ hy
  have hJ' : JacAt A₁ A₂ (√(normSq y) • sphPt y) := by rw [hyx]; exact hJ
  exact dot_sph_local_aux hρ0 hx1 hJ' v hδ

end loc

section S

variable {n m : ℕ}

/-- `v^T D v`: the quadratic form of the Poincaré matrix `D = E_ξ B_ξ B_ξᵀ`,
`B_ξ = √(t w(ξ))·𝒥(x)Π_x`, `w = τ²/|y|²`, `t = 2/m`:
`Dquad v = t·τ²·E_ξ[|v ᵥ* 𝒥(x)Π_x|²/|y|²]`. -/
noncomputable def Dquad (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (v : Fin m → ℝ) : ℝ :=
  2 / (m : ℝ) * τ ^ 2 * ∫ ξ, normSq (v ᵥ* jacT A₁ A₂ (sphPt (c + τ • ξ))) *
    (normSq (c + τ • ξ))⁻¹ ∂stdGauss (Fin n)

/-- **The exact gradient bound**: at a point `ξ` with `y ≠ 0` where the Jacobian formula holds
at `y`: `|∇_ξ ⟨v, h(x)⟩|² ≤ τ²·|v ᵥ* 𝒥(x)Π_x|²/|y|²`. -/
theorem gradSq_dot_le (hn : 1 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (v : Fin m → ℝ)
    (ξ : Fin n → ℝ) (hy : normSq (c + τ • ξ) ≠ 0) (hJ : JacAt A₁ A₂ (c + τ • ξ)) :
    ∑ i, (fderiv ℝ (fun ξ : Fin n → ℝ =>
        v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ))) ξ (Pi.single i 1)) ^ 2 ≤
      τ ^ 2 * (normSq (v ᵥ* jacT A₁ A₂ (sphPt (c + τ • ξ))) * (normSq (c + τ • ξ))⁻¹) := by
  have hs0 : 0 < normSq (c + τ • ξ) := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hy)
  have hρ0 : 0 < nrm (c + τ • ξ) := Real.sqrt_pos.mpr hs0
  have ha0 : 0 ≤ nrm (v ᵥ* jacT A₁ A₂ (sphPt (c + τ • ξ))) := nrm_nonneg _
  have hb0 : 0 ≤ τ / nrm (c + τ • ξ) := div_nonneg hτ.le hρ0.le
  have hℓ : τ ^ 2 * (normSq (v ᵥ* jacT A₁ A₂ (sphPt (c + τ • ξ))) * (normSq (c + τ • ξ))⁻¹) =
      (1 * nrm (v ᵥ* jacT A₁ A₂ (sphPt (c + τ • ξ))) * (τ / nrm (c + τ • ξ))) ^ 2 := by
    rw [mul_pow, mul_pow, div_pow, nrm_sq, nrm_sq]
    ring
  rw [hℓ]
  refine gradSq_le_of_local fun δ hδ => ?_
  obtain ⟨δ', hδ', hprod⟩ := prod_eps zero_le_one ha0 hb0 hδ
  obtain ⟨r, hr, hloc⟩ := dot_sph_local hy hJ v hδ'
  have hκ0 : 0 < τ / nrm (c + τ • ξ) + δ' := by positivity
  have hcN : Continuous (fun ξ' : Fin n → ℝ => √(∑ i, (ξ' i - ξ i) ^ 2)) := by fun_prop
  have hN0 : √(∑ i, (ξ i - ξ i) ^ 2) < r / (τ / nrm (c + τ • ξ) + δ') := by
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, Real.sqrt_zero]
    positivity
  have hsmall : ∀ᶠ ξ' in 𝓝 ξ,
      √(∑ i, (ξ' i - ξ i) ^ 2) < r / (τ / nrm (c + τ • ξ) + δ') :=
    hcN.continuousAt.tendsto.eventually (gt_mem_nhds hN0)
  filter_upwards [sph_local c hτ ξ hy hδ', hsmall] with ξ' h1 h2
  have eN : √(∑ i, (ξ' i - ξ i) ^ 2) = nrm (ξ' - ξ) := rfl
  rw [eN] at h2 ⊢
  have hN := nrm_nonneg (ξ' - ξ)
  have hdr : nrm (sphPt (c + τ • ξ') - sphPt (c + τ • ξ)) < r := by
    refine lt_of_le_of_lt h1 ?_
    have := mul_lt_mul_of_pos_left h2 hκ0
    rwa [mul_div_cancel₀ _ hκ0.ne'] at this
  have h3 := hloc (sphPt (c + τ • ξ')) (normSq_sphPt hn _) hdr
  have h4 : |v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ')) - v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ))| ≤
      (nrm (v ᵥ* jacT A₁ A₂ (sphPt (c + τ • ξ))) + δ') *
        ((τ / nrm (c + τ • ξ) + δ') * nrm (ξ' - ξ)) :=
    h3.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
  calc |v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ')) - v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ))|
      ≤ 1 * (nrm (v ᵥ* jacT A₁ A₂ (sphPt (c + τ • ξ))) + δ') *
        (τ / nrm (c + τ • ξ) + δ') * nrm (ξ' - ξ) := by
        rw [one_mul, mul_assoc]; exact h4
    _ ≤ (1 * nrm (v ᵥ* jacT A₁ A₂ (sphPt (c + τ • ξ))) * (τ / nrm (c + τ • ξ)) + δ) *
        nrm (ξ' - ξ) := mul_le_mul_of_nonneg_right hprod hN

lemma measurable_vecMul_jacT (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (v : Fin m → ℝ) :
    Measurable (fun ξ : Fin n → ℝ => normSq (v ᵥ* jacT A₁ A₂ (sphPt (c + τ • ξ)))) := by
  have hJ : Measurable (fun ξ : Fin n → ℝ => jacT A₁ A₂ (sphPt (c + τ • ξ))) :=
    (measurable_jacT A₁ A₂).comp
      (measurable_sphPt.comp (measurable_const.add (measurable_const_smul τ)))
  have hc : Continuous (fun M : Matrix (Fin m) (Fin n) ℝ => normSq (v ᵥ* M)) :=
    continuous_normSq.comp (Continuous.matrix_vecMul continuous_const continuous_id)
  exact hc.measurable.comp hJ

/-- The integrand of `Dquad` is at most the integrand of `Ξ` times `|v|²`. -/
lemma Dquad_integrand_le (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (v : Fin m → ℝ) (ξ : Fin n → ℝ) :
    normSq (v ᵥ* jacT A₁ A₂ (sphPt (c + τ • ξ))) * (normSq (c + τ • ξ))⁻¹ ≤
      normSq v * (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹) := by
  have h := nrm_vecMul_le (jacT A₁ A₂ (sphPt (c + τ • ξ))) v
  have h2 := pow_le_pow_left₀ (nrm_nonneg _) h 2
  rw [nrm_sq, mul_pow, nrm_sq] at h2
  have h0 : 0 ≤ (normSq (c + τ • ξ))⁻¹ := inv_nonneg.mpr (normSq_nonneg _)
  calc _ ≤ opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * normSq v * (normSq (c + τ • ξ))⁻¹ :=
        mul_le_mul_of_nonneg_right h2 h0
    _ = _ := by ring

/-- The integrand of `Dquad` is integrable (`n ≥ 4`). -/
theorem integrable_Dquad (hn : 4 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (v : Fin m → ℝ) :
    Integrable (fun ξ : Fin n → ℝ => normSq (v ᵥ* jacT A₁ A₂ (sphPt (c + τ • ξ))) *
      (normSq (c + τ • ξ))⁻¹) (stdGauss (Fin n)) := by
  refine Integrable.mono' ((integrable_XiS hn A₁ A₂ c hτ).const_mul (normSq v))
    ((measurable_vecMul_jacT A₁ A₂ c τ v).mul
      (cont_ns c τ).measurable.inv).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (normSq_nonneg _)
    (inv_nonneg.mpr (normSq_nonneg _)))]
  exact Dquad_integrand_le A₁ A₂ c τ v ξ

/-- **`vᵀ D v ≤ Ξ·|v|²`** (`‖D‖_op ≤ Ξ`). -/
theorem Dquad_le_XiS (hn : 4 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (v : Fin m → ℝ) :
    Dquad A₁ A₂ c τ v ≤ XiS A₁ A₂ c τ * normSq v := by
  unfold Dquad XiS
  have h := integral_mono (integrable_Dquad hn A₁ A₂ c hτ v)
    ((integrable_XiS hn A₁ A₂ c hτ).const_mul (normSq v))
    (fun ξ => Dquad_integrand_le A₁ A₂ c τ v ξ)
  rw [integral_const_mul] at h
  have ht : (0 : ℝ) ≤ 2 / (m : ℝ) * τ ^ 2 := by positivity
  calc _ ≤ 2 / (m : ℝ) * τ ^ 2 * (normSq v * ∫ ξ, opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
        (normSq (c + τ • ξ))⁻¹ ∂stdGauss (Fin n)) := mul_le_mul_of_nonneg_left h ht
    _ = _ := by ring

/-- **The Poincaré matrix bound `t Cov_x(h) ≼ D`** (Lemma `t7:p04:dual`, formula
`t7:p04:poincare`, first inequality), as quadratic forms: for every pair of matrices `A₁`, `A₂`,
every `c`, `τ > 0`, `n ≥ 6` and every `v`: `t·Var_ξ⟨v, h(x)⟩ ≤ vᵀ D v = Dquad v`. No probability
event is used. -/
theorem cov_hid2_le_D (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (v : Fin m → ℝ) :
    2 / (m : ℝ) * ∫ ξ, (v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) -
      ∫ ξ', v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
      Dquad A₁ A₂ c τ v := by
  have ht0 : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  have hK0 : 0 ≤ nrm v * (opN A₂ * opN A₁) :=
    mul_nonneg (nrm_nonneg _) (mul_nonneg (opN_nonneg _) (opN_nonneg _))
  have hΦ : EuLip (fun z : Fin n → ℝ => v ⬝ᵥ hid2 A₁ A₂ z) (nrm v * (opN A₂ * opN A₁)) := by
    intro z z'
    have e : v ⬝ᵥ hid2 A₁ A₂ z - v ⬝ᵥ hid2 A₁ A₂ z' =
        v ⬝ᵥ (hid2 A₁ A₂ z - hid2 A₁ A₂ z') := by rw [dotProduct_sub]
    rw [e]
    refine (abs_dot_le_nrm _ _).trans ?_
    have e2 : √(∑ i, (z i - z' i) ^ 2) = nrm (z - z') := rfl
    rw [e2, mul_assoc]
    exact mul_le_mul_of_nonneg_left (nrm_hid2_sub_le A₁ A₂ z z') (nrm_nonneg _)
  have hne := ae_normSq_ne (n := n) (by omega) c hτ.ne'
  have hF := integrable_Dquad (by omega : 4 ≤ n) A₁ A₂ c hτ v
  have hgrad : ∀ᵐ ξ ∂stdGauss (Fin n),
      ∑ i, (fderiv ℝ (fun ξ : Fin n → ℝ =>
        (fun z : Fin n → ℝ => v ⬝ᵥ hid2 A₁ A₂ z) (sphPt (c + τ • ξ))) ξ
          (Pi.single i 1)) ^ 2 ≤
      τ ^ 2 * (normSq (v ᵥ* jacT A₁ A₂ (sphPt (c + τ • ξ))) * (normSq (c + τ • ξ))⁻¹) := by
    filter_upwards [hne, lemmaJ_shift A₁ A₂ c hτ.ne'] with ξ h1 h2
    exact gradSq_dot_le (by omega) A₁ A₂ c hτ v ξ h1 h2
  obtain ⟨-, hv⟩ := lemmaS_grad c hτ hK0 hΦ
    (Γ := fun ξ => τ ^ 2 * (normSq (v ᵥ* jacT A₁ A₂ (sphPt (c + τ • ξ))) *
      (normSq (c + τ • ξ))⁻¹))
    (hF.const_mul _) hgrad (invMoment_two_le hn c hτ).1 hne
  rw [integral_const_mul] at hv
  unfold Dquad
  calc _ ≤ 2 / (m : ℝ) * (τ ^ 2 * ∫ ξ, normSq (v ᵥ* jacT A₁ A₂ (sphPt (c + τ • ξ))) *
        (normSq (c + τ • ξ))⁻¹ ∂stdGauss (Fin n)) := mul_le_mul_of_nonneg_left hv ht0
    _ = _ := by ring

/-- `cov_hid2_le` of Part 153 as a corollary: `t·Var_ξ⟨v, h(x)⟩ ≤ Ξ·|v|²`. -/
theorem cov_hid2_le_of_D (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (v : Fin m → ℝ) :
    2 / (m : ℝ) * ∫ ξ, (v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) -
      ∫ ξ', v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
      XiS A₁ A₂ c τ * normSq v :=
  (cov_hid2_le_D hn A₁ A₂ c hτ v).trans (Dquad_le_XiS (by omega) A₁ A₂ c hτ v)

end S

variable {n : ℕ}

/-- **(COV) from the Poincaré matrix**: if `vᵀ D v ≤ N·(γ_A/n)·|v|²` for every `v` (that is
`n‖D‖_op/γ_A ≤ N`) at the retained value `c`, with `τ₀ > 0`, then `COV_at D c N`. -/
theorem cov_at_of_Dquad (hn : 6 ≤ n) (D : Design n) (c : Ret n) (hτ : 0 < D.tau0 c) {N : ℝ}
    (hD : ∀ v : Fin (mA n) → ℝ, Dquad c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) v ≤
      N * (2 / (n : ℝ)) / n * normSq v) :
    COV_at D c N := by
  intro w
  have hn1 : 1 ≤ n := by omega
  have h1 := cov_hid2_le_D hn c.2.1.1.1 c.2.1.1.2 c.1.2 hτ w
  have e : ∀ ξ, ∑ j, (hStand D c ξ j - muStand D c j) * w j =
      w ⬝ᵥ hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ)) -
        ∫ ξ', w ⬝ᵥ hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ')) ∂stdGauss (Fin n) := by
    intro ξ
    rw [integral_dot_hid2_cr hn1]
    unfold dotProduct
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    show (hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ)) j -
      hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) j) * w j = _
    ring
  simp_rw [e]
  exact h1.trans (hD w)

end BstLean.Part160

open BstLean.Part160 in
#print axioms dot_sph_local
open BstLean.Part160 in
#print axioms gradSq_dot_le
open BstLean.Part160 in
#print axioms integrable_Dquad
open BstLean.Part160 in
#print axioms Dquad_le_XiS
open BstLean.Part160 in
#print axioms cov_hid2_le_D
open BstLean.Part160 in
#print axioms cov_hid2_le_of_D
open BstLean.Part160 in
#print axioms cov_at_of_Dquad
