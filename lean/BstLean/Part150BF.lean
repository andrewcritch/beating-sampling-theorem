import BstLean.Part150Int

/-!
# Part 150, item 2: Lemma B-F (the binomial replacement of Gaussian means of ReLU, order `1/J`)

Role: `delegations/statements/p150-spec.md`, item 2. Paper source: `onW45-opus-prover.md` §2,
Lemma B-F; `onW45c-cx.md` §2.

`Z_J = (ξ_1 + … + ξ_J)/√J` with independent signs; `binMean J f = E f(Z_J)`;
`psiS s a = E relu(a + sZ)`, `Z` standard Gaussian (Part 137).

* `c1F c J = (1/π)·[c·√(π/2) + √(2π)/6 + (44/9)(√(2π)/90)/J + e^{−J/2}/√J]`: the paper's `c_1(J)`
  with the Region A constant `c` in the place of `κ_4`.
* `c2F c J = (2/π)·[c + √(2π)·(56807/(6750π³))/√J + e^{−J/2}/J]`: the paper's `c_2(J)` with `c` in the
  place of `κ_4` and `56807/(6750π³)` in the place of `7ζ(3)/π³`.
* **`lemmaBF1_gen`**, **`lemmaBF2_gen`**: for every constant `c ≥ 0` with `RegA c`, every real `a`,
  `s ≥ 0`, `J ≥ 1`:
  `|E relu(a + sZ_J) − E relu(a + sZ)| ≤ c1F c J · s/J`,
  `|E relu(a + sZ_J)² − E relu(a + sZ)²| ≤ c2F c J · s²/J`.
* **`lemmaBF1`**, **`lemmaBF2`**: the same with `c = √e/12` (no other hypothesis).
* `psiS_lip_s_phi`: `|ψ_s(x) − ψ_{s'}(x)| ≤ |s − s'|/√(2π)` (`φ(0) = 1/√(2π)`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open BstLean.Part130 BstLean.Part137 BstLean.Part141

/-- The constant of the first moment (the paper's `c_1(J)` with `c` in the place of `κ_4`). -/
noncomputable def c1F (c : ℝ) (J : ℕ) : ℝ :=
  1 / π * (c * √(π / 2) + √(2 * π) / 6 + 44 / 9 * (√(2 * π) / 90) / J +
    rexp (-((J : ℝ) / 2)) / √(J : ℝ))

/-- The constant of the second moment (the paper's `c_2(J)` with `c` in the place of `κ_4` and
`56807/(6750π³)` in the place of `7ζ(3)/π³`). -/
noncomputable def c2F (c : ℝ) (J : ℕ) : ℝ :=
  2 / π * (c + √(2 * π) * (56807 / (6750 * π ^ 3)) / √(J : ℝ) + rexp (-((J : ℝ) / 2)) / J)

/-- **Lemma B-F (i)**, for a Region A constant `c`. -/
theorem lemmaBF1_gen {c : ℝ} (hc0 : 0 ≤ c) (hc : RegA c) {J : ℕ} (hJ : 1 ≤ J) (a : ℝ) {s : ℝ}
    (hs : 0 ≤ s) :
    |binMean J (fun z => relu (a + s * z)) - psiS s a| ≤ c1F c J * s / J := by
  obtain ⟨hM, hMe⟩ := int_M2 c hJ
  have h := relu_rep J a hs hM (fun t ht => dChar_le_Mmaj hc0 hc hJ 2 ht)
  have hp : (0 : ℝ) < π := Real.pi_pos
  refine h.trans ?_
  have : s * (1 / π * ∫ t in Ioi 0, Mmaj c J 2 t) ≤ s * (1 / π * ((c * √(π / 2) + √(2 * π) / 6 +
      44 / 9 * (√(2 * π) / 90) / J + rexp (-((J : ℝ) / 2)) / √(J : ℝ)) / J)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMe (by positivity)) hs
  refine this.trans (le_of_eq ?_)
  unfold c1F; ring

/-- **Lemma B-F (ii)**, for a Region A constant `c`. -/
theorem lemmaBF2_gen {c : ℝ} (hc0 : 0 ≤ c) (hc : RegA c) {J : ℕ} (hJ : 1 ≤ J) (a : ℝ) {s : ℝ}
    (hs : 0 ≤ s) :
    |binMean J (fun z => relu (a + s * z) ^ 2) - ∫ z, relu (a + s * z) ^ 2 ∂gaussianReal 0 1| ≤
      c2F c J * s ^ 2 / J := by
  obtain ⟨hM, hMe⟩ := int_M3 c hJ
  have h := reluSq_rep hJ a hs hM (fun t ht => dChar_le_Mmaj hc0 hc hJ 3 ht)
  have hp : (0 : ℝ) < π := Real.pi_pos
  refine h.trans ?_
  have : s ^ 2 * (2 / π * ∫ t in Ioi 0, Mmaj c J 3 t) ≤ s ^ 2 * (2 / π * ((c +
      √(2 * π) * (56807 / (6750 * π ^ 3)) / √(J : ℝ) + rexp (-((J : ℝ) / 2)) / J) / J)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMe (by positivity)) (sq_nonneg s)
  refine this.trans (le_of_eq ?_)
  unfold c2F; ring

/-- **Lemma B-F (i)** with the Region A constant `√e/12`. -/
theorem lemmaBF1 {J : ℕ} (hJ : 1 ≤ J) (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    |binMean J (fun z => relu (a + s * z)) - psiS s a| ≤ c1F (rexp (1 / 2) / 12) J * s / J :=
  lemmaBF1_gen (by positivity) regA_sqrt_e hJ a hs

/-- **Lemma B-F (ii)** with the Region A constant `√e/12`. -/
theorem lemmaBF2 {J : ℕ} (hJ : 1 ≤ J) (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    |binMean J (fun z => relu (a + s * z) ^ 2) - ∫ z, relu (a + s * z) ^ 2 ∂gaussianReal 0 1| ≤
      c2F (rexp (1 / 2) / 12) J * s ^ 2 / J :=
  lemmaBF2_gen (by positivity) regA_sqrt_e hJ a hs

lemma psiS_eq_abs (s x : ℝ) : psiS s x = (x + ∫ z, |x + s * z| ∂gaussianReal 0 1) / 2 := by
  unfold psiS
  have h1 : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by simpa using integrable_pow_gauss 1
  have e : (fun z : ℝ => relu (x + s * z)) = fun z => 2⁻¹ * ((x + s * z) + |x + s * z|) := by
    funext z; rw [relu_eq_abs]; ring
  have hxz : Integrable (fun z : ℝ => x + s * z) (gaussianReal 0 1) :=
    (integrable_const x).add (h1.const_mul s)
  have hxv : ∫ z : ℝ, x + s * z ∂gaussianReal 0 1 = x := by
    rw [integral_add (integrable_const x) (h1.const_mul s), integral_const_mul,
      integral_id_gaussianReal]
    simp
  rw [e, integral_const_mul, integral_add hxz hxz.abs, hxv]
  ring

/-- `ψ_s(x)` is `φ(0)`-Lipschitz in `s`, `φ(0) = 1/√(2π)`. -/
theorem psiS_lip_s_phi (s s' x : ℝ) : |psiS s x - psiS s' x| ≤ 1 / √(2 * π) * |s - s'| := by
  have hp : (0 : ℝ) < π := Real.pi_pos
  have h1 : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by simpa using integrable_pow_gauss 1
  have hi : ∀ r : ℝ, Integrable (fun z : ℝ => |x + r * z|) (gaussianReal 0 1) := fun r =>
    ((integrable_const x).add (h1.const_mul r)).abs
  have h := abs_int_sub_le (μ := gaussianReal 0 1) (hi s) (hi s')
    (integrable_abs_gauss.const_mul (|s - s'|)) (fun z => by
      refine (abs_abs_sub_abs_le_abs_sub _ _).trans (le_of_eq ?_)
      rw [← abs_mul]; congr 1; ring)
  rw [integral_const_mul, gauss_abs] at h
  have h2 : √(2 / π) = 2 / √(2 * π) := by
    rw [show (2 : ℝ) / π = 2 ^ 2 / (2 * π) by field_simp, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq (by norm_num)]
  rw [psiS_eq_abs, psiS_eq_abs]
  have e : (x + ∫ z, |x + s * z| ∂gaussianReal 0 1) / 2 -
      (x + ∫ z, |x + s' * z| ∂gaussianReal 0 1) / 2 =
      ((∫ z, |x + s * z| ∂gaussianReal 0 1) - ∫ z, |x + s' * z| ∂gaussianReal 0 1) / 2 := by ring
  rw [e, abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num), div_le_iff₀ (by norm_num)]
  refine h.trans (le_of_eq ?_)
  rw [h2]; ring

end BstLean.Part150
