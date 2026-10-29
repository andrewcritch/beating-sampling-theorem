import BstLean.Part153SJ
import BstLean.Part153Cr

/-!
# Part 153 SL: Lemma S, second assertion, for a locally Lipschitz `φ` on the orthant

Paper source: `proofs/option-n/theorem5-04-standin-structure.tex`, Lemma S, second assertion:
for every `(A₁, A₂)` and every real function `φ` that is locally Lipschitz on the closed
nonnegative orthant `𝒪` (with `lip φ` taken inside `𝒪`),
`Var_x φ(q(x)) ≤ t·τ²·E_ξ[lip φ(q(x))²·‖𝒥(x)Π_x‖_op²/|y|²]`; `φ` need not be bounded.

Every result holds for EVERY pair of matrices `A₁`, `A₂` (no probability over them).
Notation: `y = c + τξ`, `x = sphPt y = y/|y|`, `t = 2/m`, `q(ξ) = √t • hid2 A₁ A₂ x`.
The function `ℓ` is a pointwise Lipschitz constant of `φ` inside the orthant (an upper bound of
`lip φ`).

* `orthant_sl m`: the closed nonnegative orthant of `ℝ^m`.
* `comp_local_sl`: the gradient bound of a composition, from two local Lipschitz constants.
* `hid2_shift_local_sl`: `ξ ↦ h₂(x)` has the local Lipschitz constant `‖𝒥(x)Π_x‖_op·τ/|y|`.
* `gradSq_loc_le_sl`: `|∇_ξ φ(q)|² ≤ t·τ²·ℓ(q)²·‖𝒥(x)Π_x‖_op²/|y|²`.
* **`lemmaS_loc_sl`**: Lemma S, second assertion.
* `lemmaS_loc_meas_sl`: the same, with the hypothesis `Measurable ℓ`.
* **`lemmaS_loc_unif_sl`**: if `ℓ ≤ L_φ` on the orthant then `Var ≤ L_φ²·Ξ`.
* `lemmaS_jac_sl`: the special case of a globally Lipschitz `φ` (`lemmaS_jac` of Part 153 SJ).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part148 (EuLip)
open BstLean.Part151 (jac JacAt lemmaJ_shift)

section SL

variable {n m : ℕ}

/-- The closed nonnegative orthant of `ℝ^m`. -/
def orthant_sl (m : ℕ) : Set (Fin m → ℝ) := {z | ∀ j, 0 ≤ z j}

/-- The range of `s • h₂`, `s ≥ 0`, is inside the orthant. -/
lemma smul_hid2_mem_orthant_sl (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    {s : ℝ} (hs : 0 ≤ s) (z : Fin n → ℝ) : s • hid2 A₁ A₂ z ∈ orthant_sl m := by
  intro j
  show 0 ≤ s * relu _
  exact mul_nonneg hs (relu_nonneg _)

/-- The cut-off with `ε = 1` is the identity on the unit sphere. -/
lemma cut_one_unit_sl {x : Fin n → ℝ} (hx : normSq x = 1) : cut 1 x = x := by
  unfold cut
  rw [hx, Real.sqrt_one, max_self, div_one, one_smul]

lemma nrm_cut_le_sl (z : Fin n → ℝ) : nrm (cut 1 z) ≤ 1 :=
  Real.sqrt_le_one.mpr (cut_normSq_le one_pos z)

/-- The cut-off with `ε = 1` is `1`-Lipschitz. -/
lemma nrm_cut_sub_le_sl (z z' : Fin n → ℝ) : nrm (cut 1 z - cut 1 z') ≤ nrm (z - z') := by
  have h := cut_dist one_pos z z'
  rw [one_pow, div_one] at h
  exact Real.sqrt_le_sqrt h

lemma eventually_nrm_lt_sl (ξ : Fin n → ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ ξ' in 𝓝 ξ, nrm (ξ' - ξ) < ρ := by
  have hcN : Continuous (fun ξ' : Fin n → ℝ => √(∑ i, (ξ' i - ξ i) ^ 2)) := by fun_prop
  have hN0 : √(∑ i, (ξ i - ξ i) ^ 2) < ρ := by
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, Real.sqrt_zero]
    exact hρ
  exact hcN.continuousAt.tendsto.eventually (gt_mem_nhds hN0)

/-- **The gradient bound of a composition from two local Lipschitz constants.** If `G` has the
local Lipschitz constant `κ` at `ξ`, and `φ` has the local Lipschitz constant `L0` at `G ξ` along
the range of `G`, then `|∇(φ ∘ G)(ξ)|² ≤ (L0·κ)²`. -/
lemma comp_local_sl {G : (Fin n → ℝ) → Fin m → ℝ} {φ : (Fin m → ℝ) → ℝ} {ξ : Fin n → ℝ}
    {L0 κ : ℝ} (hL0 : 0 ≤ L0) (hκ : 0 ≤ κ)
    (hG : ∀ δ : ℝ, 0 < δ → ∀ᶠ ξ' in 𝓝 ξ, nrm (G ξ' - G ξ) ≤ (κ + δ) * nrm (ξ' - ξ))
    (hφ : ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ ∀ ξ' : Fin n → ℝ, nrm (G ξ' - G ξ) < r →
      |φ (G ξ') - φ (G ξ)| ≤ (L0 + δ) * nrm (G ξ' - G ξ)) :
    ∑ i, (fderiv ℝ (fun ξ => φ (G ξ)) ξ (Pi.single i 1)) ^ 2 ≤ (L0 * κ) ^ 2 := by
  refine gradSq_le_of_local fun δ hδ => ?_
  obtain ⟨δ', hδ', hprod⟩ := prod_eps (P := 1) zero_le_one hL0 hκ hδ
  obtain ⟨r, hr, hloc⟩ := hφ δ' hδ'
  have hκ0 : 0 < κ + δ' := by positivity
  filter_upwards [hG δ' hδ', eventually_nrm_lt_sl ξ (div_pos hr hκ0)] with ξ' h1 h2
  have hN := nrm_nonneg (ξ' - ξ)
  have hdr : nrm (G ξ' - G ξ) < r := by
    refine lt_of_le_of_lt h1 ?_
    have := mul_lt_mul_of_pos_left h2 hκ0
    rwa [mul_div_cancel₀ _ hκ0.ne'] at this
  have h3 := hloc ξ' hdr
  show |φ (G ξ') - φ (G ξ)| ≤ (L0 * κ + δ) * nrm (ξ' - ξ)
  calc |φ (G ξ') - φ (G ξ)| ≤ (L0 + δ') * nrm (G ξ' - G ξ) := h3
    _ ≤ (L0 + δ') * ((κ + δ') * nrm (ξ' - ξ)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 * (L0 + δ') * (κ + δ') * nrm (ξ' - ξ) := by ring
    _ ≤ (1 * L0 * κ + δ) * nrm (ξ' - ξ) := mul_le_mul_of_nonneg_right hprod hN
    _ = (L0 * κ + δ) * nrm (ξ' - ξ) := by ring

/-- **The local Lipschitz constant of `ξ ↦ h₂(x)`**, `x = y/|y|`, `y = c + τξ`: at a point with
`y ≠ 0` where the Jacobian formula holds at `y`, the constant is `‖𝒥(x)Π_x‖_op·τ/|y|`. -/
theorem hid2_shift_local_sl (hn : 1 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (ξ : Fin n → ℝ)
    (hy : normSq (c + τ • ξ) ≠ 0) (hJ : JacAt A₁ A₂ (c + τ • ξ)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ξ' in 𝓝 ξ,
      nrm (hid2 A₁ A₂ (sphPt (c + τ • ξ')) - hid2 A₁ A₂ (sphPt (c + τ • ξ))) ≤
        (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) * (τ / nrm (c + τ • ξ)) + δ) * nrm (ξ' - ξ) := by
  have hs0 : 0 < normSq (c + τ • ξ) := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hy)
  have hρ0 : 0 < nrm (c + τ • ξ) := Real.sqrt_pos.mpr hs0
  have ha0 : 0 ≤ opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) := opN_nonneg _
  have hb0 : 0 ≤ τ / nrm (c + τ • ξ) := div_nonneg hτ.le hρ0.le
  obtain ⟨δ', hδ', hprod⟩ := prod_eps (P := 1) zero_le_one ha0 hb0 hδ
  obtain ⟨r, hr, hloc⟩ := hid2_sph_local hy hJ hδ'
  have hκ0 : 0 < τ / nrm (c + τ • ξ) + δ' := by positivity
  filter_upwards [sph_local c hτ ξ hy hδ', eventually_nrm_lt_sl ξ (div_pos hr hκ0)] with ξ' h1 h2
  have hN := nrm_nonneg (ξ' - ξ)
  have hdr : nrm (sphPt (c + τ • ξ') - sphPt (c + τ • ξ)) < r := by
    refine lt_of_le_of_lt h1 ?_
    have := mul_lt_mul_of_pos_left h2 hκ0
    rwa [mul_div_cancel₀ _ hκ0.ne'] at this
  have h3 := hloc (sphPt (c + τ • ξ')) (normSq_sphPt hn _) hdr
  calc nrm (hid2 A₁ A₂ (sphPt (c + τ • ξ')) - hid2 A₁ A₂ (sphPt (c + τ • ξ)))
      ≤ (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) + δ') *
        ((τ / nrm (c + τ • ξ) + δ') * nrm (ξ' - ξ)) :=
        h3.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
    _ = 1 * (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) + δ') * (τ / nrm (c + τ • ξ) + δ') *
        nrm (ξ' - ξ) := by ring
    _ ≤ (1 * opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) * (τ / nrm (c + τ • ξ)) + δ) *
        nrm (ξ' - ξ) := mul_le_mul_of_nonneg_right hprod hN
    _ = (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) * (τ / nrm (c + τ • ξ)) + δ) *
        nrm (ξ' - ξ) := by ring

/-- **The gradient bound of Lemma S, second assertion, with a pointwise Lipschitz constant**: at
a point `ξ` with `y ≠ 0` where the Jacobian formula holds at `y`:
`|∇_ξ φ(q)|² ≤ t·τ²·ℓ(q)²·‖𝒥(x)Π_x‖_op²/|y|²`. -/
theorem gradSq_loc_le_sl (hn : 1 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {φ ℓ : (Fin m → ℝ) → ℝ}
    (h2 : ∀ z ∈ orthant_sl m, ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ ∀ z' ∈ orthant_sl m,
      nrm (z' - z) < r → |φ z' - φ z| ≤ (ℓ z + δ) * nrm (z' - z))
    (hℓ0 : ∀ z ∈ orthant_sl m, 0 ≤ ℓ z) (ξ : Fin n → ℝ)
    (hy : normSq (c + τ • ξ) ≠ 0) (hJ : JacAt A₁ A₂ (c + τ • ξ)) :
    ∑ i, (fderiv ℝ (fun ξ : Fin n → ℝ =>
        φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ)))) ξ (Pi.single i 1)) ^ 2 ≤
      2 / (m : ℝ) * τ ^ 2 * (ℓ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
        (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹)) := by
  have hs0 : 0 < normSq (c + τ • ξ) := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hy)
  have hρ0 : 0 < nrm (c + τ • ξ) := Real.sqrt_pos.mpr hs0
  have ht0 : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  have hst0 : 0 ≤ √(2 / (m : ℝ)) := Real.sqrt_nonneg _
  have ha0 : 0 ≤ opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) := opN_nonneg _
  have hb0 : 0 ≤ τ / nrm (c + τ • ξ) := div_nonneg hτ.le hρ0.le
  have hmem : ∀ ξ' : Fin n → ℝ,
      √(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ')) ∈ orthant_sl m := fun ξ' =>
    smul_hid2_mem_orthant_sl A₁ A₂ hst0 _
  have hℓ : 2 / (m : ℝ) * τ ^ 2 * (ℓ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
        (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹)) =
      (ℓ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) *
        (√(2 / (m : ℝ)) * (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) *
          (τ / nrm (c + τ • ξ))))) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, div_pow, Real.sq_sqrt ht0, nrm_sq]
    ring
  rw [hℓ]
  refine comp_local_sl
    (G := fun ξ : Fin n → ℝ => √(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ)))
    (hℓ0 _ (hmem ξ)) (mul_nonneg hst0 (mul_nonneg ha0 hb0)) ?_ ?_
  · intro δ hδ
    have hδ' : 0 < δ / (√(2 / (m : ℝ)) + 1) := by positivity
    filter_upwards [hid2_shift_local_sl hn A₁ A₂ c hτ ξ hy hJ hδ'] with ξ' h
    show nrm (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ')) -
      √(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) ≤ _
    rw [← smul_sub, nrm_smul, abs_of_nonneg hst0]
    have hsmall : √(2 / (m : ℝ)) * (δ / (√(2 / (m : ℝ)) + 1)) ≤ δ := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith
    calc √(2 / (m : ℝ)) *
          nrm (hid2 A₁ A₂ (sphPt (c + τ • ξ')) - hid2 A₁ A₂ (sphPt (c + τ • ξ)))
        ≤ √(2 / (m : ℝ)) * ((opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) * (τ / nrm (c + τ • ξ)) +
            δ / (√(2 / (m : ℝ)) + 1)) * nrm (ξ' - ξ)) := mul_le_mul_of_nonneg_left h hst0
      _ = (√(2 / (m : ℝ)) * (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) * (τ / nrm (c + τ • ξ))) +
            √(2 / (m : ℝ)) * (δ / (√(2 / (m : ℝ)) + 1))) * nrm (ξ' - ξ) := by ring
      _ ≤ (√(2 / (m : ℝ)) * (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) * (τ / nrm (c + τ • ξ))) +
            δ) * nrm (ξ' - ξ) :=
          mul_le_mul_of_nonneg_right (by linarith) (nrm_nonneg _)
  · intro δ hδ
    obtain ⟨r, hr, h⟩ := h2 _ (hmem ξ) δ hδ
    exact ⟨r, hr, fun ξ' hd => h _ (hmem ξ') hd⟩

/-- **Lemma S, second assertion, for a locally Lipschitz `φ` on the orthant.** For every pair of
matrices `A₁`, `A₂`, every `c`, `τ > 0`, `n ≥ 6`, and functions `φ`, `ℓ` with
(h1) `φ` is Lipschitz on the bounded parts of the orthant,
(h2) `ℓ z` is a local Lipschitz constant of `φ` at `z` inside the orthant, `ℓ ≥ 0` there,
(h3) `ξ ↦ ℓ(q ξ)` is measurable and `ℓ` is bounded above on the bounded parts of the orthant:
the integrand of the right side is integrable, the centred square is integrable, and
`Var_ξ φ(q) ≤ t·τ²·E_ξ[ℓ(q)²·‖𝒥(x)Π_x‖_op²/|y|²]`. `φ` need not be bounded. -/
theorem lemmaS_loc_sl (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {φ ℓ : (Fin m → ℝ) → ℝ}
    (h1 : ∀ R : ℝ, ∃ L : ℝ, 0 ≤ L ∧ ∀ u ∈ orthant_sl m, ∀ v ∈ orthant_sl m,
      nrm u ≤ R → nrm v ≤ R → |φ u - φ v| ≤ L * nrm (u - v))
    (h2 : ∀ z ∈ orthant_sl m, ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ ∀ z' ∈ orthant_sl m,
      nrm (z' - z) < r → |φ z' - φ z| ≤ (ℓ z + δ) * nrm (z' - z))
    (hℓ0 : ∀ z ∈ orthant_sl m, 0 ≤ ℓ z)
    (hℓm : Measurable (fun ξ : Fin n → ℝ =>
      ℓ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ)))))
    (hℓb : ∀ R : ℝ, ∃ L : ℝ, ∀ z ∈ orthant_sl m, nrm z ≤ R → ℓ z ≤ L) :
    Integrable (fun ξ : Fin n → ℝ => ℓ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
      (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹)) (stdGauss (Fin n)) ∧
    Integrable (fun ξ : Fin n → ℝ => (φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) -
      ∫ ξ', φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ'))) ∂stdGauss (Fin n)) ^ 2)
      (stdGauss (Fin n)) ∧
    ∫ ξ, (φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) -
      ∫ ξ', φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ'))) ∂stdGauss (Fin n)) ^ 2
        ∂stdGauss (Fin n) ≤
      2 / (m : ℝ) * τ ^ 2 *
        ∫ ξ, ℓ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
          (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹)
          ∂stdGauss (Fin n) := by
  have hn1 : 1 ≤ n := by omega
  have hst0 : 0 ≤ √(2 / (m : ℝ)) := Real.sqrt_nonneg _
  have hop0 : 0 ≤ opN A₂ * opN A₁ := mul_nonneg (opN_nonneg _) (opN_nonneg _)
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, R0 = √(2 / (m : ℝ)) * (opN A₂ * opN A₁) := ⟨_, rfl⟩
  obtain ⟨L, hL0, hLip⟩ := h1 R0
  obtain ⟨Lb, hLb⟩ := hℓb R0
  have hmemz : ∀ z : Fin n → ℝ, √(2 / (m : ℝ)) • hid2 A₁ A₂ z ∈ orthant_sl m := fun z =>
    smul_hid2_mem_orthant_sl A₁ A₂ hst0 z
  -- the range of `q` on the unit ball is inside the ball of radius `R0`
  have hqR : ∀ z : Fin n → ℝ, nrm z ≤ 1 → nrm (√(2 / (m : ℝ)) • hid2 A₁ A₂ z) ≤ R0 := by
    intro z hz
    rw [nrm_smul, abs_of_nonneg hst0, hR0]
    refine mul_le_mul_of_nonneg_left ((nrm_hid2_le_cr A₁ A₂ z).trans ?_) hst0
    have := mul_le_mul_of_nonneg_left hz hop0
    linarith
  -- the globally Lipschitz function `Φ`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin n → ℝ) → ℝ,
      Φ = fun z => φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (cut 1 z)) := ⟨_, rfl⟩
  have hK0 : 0 ≤ L * √(2 / (m : ℝ)) * (opN A₂ * opN A₁) :=
    mul_nonneg (mul_nonneg hL0 hst0) hop0
  have hΦlip : EuLip Φ (L * √(2 / (m : ℝ)) * (opN A₂ * opN A₁)) := by
    intro z z'
    rw [hΦ]
    show |φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (cut 1 z)) -
      φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (cut 1 z'))| ≤
      L * √(2 / (m : ℝ)) * (opN A₂ * opN A₁) * nrm (z - z')
    refine (hLip _ (hmemz _) _ (hmemz _) (hqR _ (nrm_cut_le_sl z))
      (hqR _ (nrm_cut_le_sl z'))).trans ?_
    rw [← smul_sub, nrm_smul, abs_of_nonneg hst0]
    calc L * (√(2 / (m : ℝ)) * nrm (hid2 A₁ A₂ (cut 1 z) - hid2 A₁ A₂ (cut 1 z')))
        ≤ L * (√(2 / (m : ℝ)) * (opN A₂ * opN A₁ * nrm (z - z'))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            ((nrm_hid2_sub_le A₁ A₂ _ _).trans
              (mul_le_mul_of_nonneg_left (nrm_cut_sub_le_sl z z') hop0)) hst0) hL0
      _ = L * √(2 / (m : ℝ)) * (opN A₂ * opN A₁) * nrm (z - z') := by ring
  have hΦeq : ∀ ξ : Fin n → ℝ, Φ (sphPt (c + τ • ξ)) =
      φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) := by
    intro ξ
    rw [hΦ]
    show φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (cut 1 (sphPt (c + τ • ξ)))) = _
    rw [cut_one_unit_sl (normSq_sphPt hn1 _)]
  have hne := ae_normSq_ne (n := n) hn1 c hτ.ne'
  have hqb : ∀ ξ : Fin n → ℝ, nrm (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) ≤ R0 :=
    fun ξ => hqR _ (le_of_eq (nrm_of_normSq_one_cr (normSq_sphPt hn1 _)))
  have hF := integrable_XiS (by omega : 4 ≤ n) A₁ A₂ c hτ
  -- the integrand of the right side
  have hΓ0 : Integrable (fun ξ : Fin n → ℝ =>
      ℓ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
      (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹))
      (stdGauss (Fin n)) := by
    refine Integrable.mono' (hF.const_mul (Lb ^ 2))
      ((hℓm.pow_const 2).mul (((measurable_opN_jacT_sj A₁ A₂ c τ).pow_const 2).mul
        (cont_ns c τ).measurable.inv)).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
    have h0 : 0 ≤ opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹ :=
      mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (normSq_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) h0)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hℓ0 _ (hmemz _))
      (hLb _ (hmemz _) (hqb ξ)) 2) h0
  have hgrad : ∀ᵐ ξ ∂stdGauss (Fin n),
      ∑ i, (fderiv ℝ (fun ξ : Fin n → ℝ => Φ (sphPt (c + τ • ξ))) ξ (Pi.single i 1)) ^ 2 ≤
      2 / (m : ℝ) * τ ^ 2 * (ℓ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
        (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹)) := by
    have hfe : (fun ξ : Fin n → ℝ => Φ (sphPt (c + τ • ξ))) = fun ξ =>
        φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) := funext hΦeq
    rw [hfe]
    filter_upwards [hne, lemmaJ_shift A₁ A₂ c hτ.ne'] with ξ h1' h2'
    exact gradSq_loc_le_sl hn1 A₁ A₂ c hτ h2 hℓ0 ξ h1' h2'
  obtain ⟨hi, hv⟩ := lemmaS_grad c hτ hK0 hΦlip
    (Γ := fun ξ => 2 / (m : ℝ) * τ ^ 2 *
      (ℓ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
        (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹)))
    (hΓ0.const_mul _) hgrad (invMoment_two_le hn c hτ).1 hne
  simp only [hΦeq] at hi hv
  rw [integral_const_mul] at hv
  exact ⟨hΓ0, hi, hv⟩

/-- Lemma S, second assertion, with the hypothesis that `ℓ` is measurable. -/
theorem lemmaS_loc_meas_sl (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {φ ℓ : (Fin m → ℝ) → ℝ}
    (h1 : ∀ R : ℝ, ∃ L : ℝ, 0 ≤ L ∧ ∀ u ∈ orthant_sl m, ∀ v ∈ orthant_sl m,
      nrm u ≤ R → nrm v ≤ R → |φ u - φ v| ≤ L * nrm (u - v))
    (h2 : ∀ z ∈ orthant_sl m, ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ ∀ z' ∈ orthant_sl m,
      nrm (z' - z) < r → |φ z' - φ z| ≤ (ℓ z + δ) * nrm (z' - z))
    (hℓ0 : ∀ z ∈ orthant_sl m, 0 ≤ ℓ z) (hℓm : Measurable ℓ)
    (hℓb : ∀ R : ℝ, ∃ L : ℝ, ∀ z ∈ orthant_sl m, nrm z ≤ R → ℓ z ≤ L) :
    Integrable (fun ξ : Fin n → ℝ => ℓ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
      (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹)) (stdGauss (Fin n)) ∧
    Integrable (fun ξ : Fin n → ℝ => (φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) -
      ∫ ξ', φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ'))) ∂stdGauss (Fin n)) ^ 2)
      (stdGauss (Fin n)) ∧
    ∫ ξ, (φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) -
      ∫ ξ', φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ'))) ∂stdGauss (Fin n)) ^ 2
        ∂stdGauss (Fin n) ≤
      2 / (m : ℝ) * τ ^ 2 *
        ∫ ξ, ℓ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
          (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹)
          ∂stdGauss (Fin n) :=
  lemmaS_loc_sl hn A₁ A₂ c hτ h1 h2 hℓ0
    (hℓm.comp ((measurable_const_smul (√(2 / (m : ℝ)))).comp
      (measurable_hid2_sph_cr A₁ A₂ c τ))) hℓb

/-- **Lemma S, second assertion, with a uniform bound of the pointwise constant**: if
`ℓ ≤ L_φ` on the orthant, then `Var_ξ φ(q) ≤ L_φ²·Ξ`. -/
theorem lemmaS_loc_unif_sl (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {φ ℓ : (Fin m → ℝ) → ℝ} {Lφ : ℝ}
    (h1 : ∀ R : ℝ, ∃ L : ℝ, 0 ≤ L ∧ ∀ u ∈ orthant_sl m, ∀ v ∈ orthant_sl m,
      nrm u ≤ R → nrm v ≤ R → |φ u - φ v| ≤ L * nrm (u - v))
    (h2 : ∀ z ∈ orthant_sl m, ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ ∀ z' ∈ orthant_sl m,
      nrm (z' - z) < r → |φ z' - φ z| ≤ (ℓ z + δ) * nrm (z' - z))
    (hℓ0 : ∀ z ∈ orthant_sl m, 0 ≤ ℓ z)
    (hℓm : Measurable (fun ξ : Fin n → ℝ =>
      ℓ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ)))))
    (hℓL : ∀ z ∈ orthant_sl m, ℓ z ≤ Lφ) :
    Integrable (fun ξ : Fin n → ℝ => (φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) -
      ∫ ξ', φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ'))) ∂stdGauss (Fin n)) ^ 2)
      (stdGauss (Fin n)) ∧
    ∫ ξ, (φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) -
      ∫ ξ', φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ'))) ∂stdGauss (Fin n)) ^ 2
        ∂stdGauss (Fin n) ≤ Lφ ^ 2 * XiS A₁ A₂ c τ := by
  obtain ⟨hΓ, hi, hv⟩ := lemmaS_loc_sl hn A₁ A₂ c hτ h1 h2 hℓ0 hℓm
    (fun _ => ⟨Lφ, fun z hz _ => hℓL z hz⟩)
  have hst0 : 0 ≤ √(2 / (m : ℝ)) := Real.sqrt_nonneg _
  have hF := integrable_XiS (by omega : 4 ≤ n) A₁ A₂ c hτ
  have hmono : ∫ ξ, ℓ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
      (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹) ∂stdGauss (Fin n) ≤
      ∫ ξ, Lφ ^ 2 * (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹)
        ∂stdGauss (Fin n) :=
    integral_mono hΓ (hF.const_mul _) fun ξ =>
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀
        (hℓ0 _ (smul_hid2_mem_orthant_sl A₁ A₂ hst0 _))
        (hℓL _ (smul_hid2_mem_orthant_sl A₁ A₂ hst0 _)) 2)
        (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (normSq_nonneg _)))
  rw [integral_const_mul] at hmono
  refine ⟨hi, hv.trans ?_⟩
  unfold XiS
  calc 2 / (m : ℝ) * τ ^ 2 *
        ∫ ξ, ℓ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
          (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹)
          ∂stdGauss (Fin n)
      ≤ 2 / (m : ℝ) * τ ^ 2 * (Lφ ^ 2 *
        ∫ ξ, opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹
          ∂stdGauss (Fin n)) := mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = Lφ ^ 2 * (2 / (m : ℝ) * τ ^ 2 *
        ∫ ξ, opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹
          ∂stdGauss (Fin n)) := by ring

/-- **Check: the special case of a globally Lipschitz `φ`** (the statement of `lemmaS_jac`),
derived from `lemmaS_loc_unif_sl` with the constant function `ℓ = L_φ`. -/
theorem lemmaS_jac_sl (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {φ : (Fin m → ℝ) → ℝ} {Lφ : ℝ} (hL : 0 ≤ Lφ) (hφ : EuLip φ Lφ) :
    ∫ ξ, (φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) -
      ∫ ξ', φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ'))) ∂stdGauss (Fin n)) ^ 2
        ∂stdGauss (Fin n) ≤ Lφ ^ 2 * XiS A₁ A₂ c τ := by
  refine (lemmaS_loc_unif_sl hn A₁ A₂ c hτ (φ := φ) (ℓ := fun _ => Lφ) (Lφ := Lφ)
    (fun _ => ⟨Lφ, hL, fun u _ v _ _ _ => hφ u v⟩) ?_ (fun _ _ => hL) measurable_const
    (fun _ _ => le_refl _)).2
  intro z _ δ hδ
  refine ⟨1, one_pos, fun z' _ _ => (hφ z' z).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

end SL

end BstLean.Part153

open BstLean.Part153 in
#print axioms hid2_shift_local_sl
open BstLean.Part153 in
#print axioms gradSq_loc_le_sl
open BstLean.Part153 in
#print axioms lemmaS_loc_sl
open BstLean.Part153 in
#print axioms lemmaS_loc_meas_sl
open BstLean.Part153 in
#print axioms lemmaS_loc_unif_sl
open BstLean.Part153 in
#print axioms lemmaS_jac_sl
