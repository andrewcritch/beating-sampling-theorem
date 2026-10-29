import BstLean.Part169Pass

/-!
# Part 169 (file `Rule`): the finite-rule error of the passes (paper `t7:p08:rule`)

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, formula `t7:p08:rule`:
`n|Δ_f^rule| ≤ n^{3/2}α_J ς`, `n|Δ_ω^rule| ≤ n²β_J ς²` (the paper then uses
`ς ≤ σ₀√(1 − s²)`). Here `α_J = c1F/J`, `β_J = c2F/J` are the constants of Part 150's
Lemma B-F (`lemmaBF1`, `lemmaBF2`), with the Region A constant `√e/12`.

* `fGauss c s`, `wGauss c s`: the passes with the exact Gaussian second-layer rule:
  `Σ_j ψ_ς((A₂ā)_j) b_j/(√n|b|)` and `Σ_j E ReLU((A₂ā)_j + ςZ)²/n`.
* `sum_abs_le`: `Σ_j |b_j| ≤ √m·|b|`.
* **`rule_f`**: `|f̃(s) − f_G(s)| ≤ √n·c1F·ς/J_z` (so `n|Δ_f^rule| ≤ n^{3/2}c1F ς/J_z`).
* **`rule_w`**: `|ω̃(s) − ω_G(s)| ≤ n·c2F·ς²/J_z` (so `n|Δ_ω^rule| ≤ n² c2F ς²/J_z`).
-/

namespace BstLean.Part169

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part157
open BstLean.Part150 (binMean c1F c2F lemmaBF1 lemmaBF2)
open BstLean.Part137 (psiS)

variable {n : ℕ}

/-- The location pass with the exact Gaussian second-layer rule. -/
noncomputable def fGauss (c : Ret n) (s : ℝ) : ℝ :=
  (∑ j, psiS (√(vsig2 c s)) ((A2 c).mulVec (a1Bar c s) j) * bR c j) /
    (√(n : ℝ) * √(normSq (bR c)))

/-- The energy pass with the exact Gaussian second-layer rule. -/
noncomputable def wGauss (c : Ret n) (s : ℝ) : ℝ :=
  (∑ j, ∫ z, relu ((A2 c).mulVec (a1Bar c s) j + √(vsig2 c s) * z) ^ 2 ∂gaussianReal 0 1) /
    (n : ℝ)

lemma Jz_pos (hn : 2 ≤ n) : 1 ≤ Jz n := by
  unfold Jz
  have h1 : (2 : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    calc (2 : ℝ) ≤ n := hn'
      _ = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (n : ℝ) ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h2 : 2 ≤ ⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have := Nat.le_ceil ((n : ℝ) ^ ((3 : ℝ) / 2))
    exact_mod_cast h1.trans this
  omega

/-- `Σ_j |b_j| ≤ √m·|b|` (Cauchy–Schwarz). -/
lemma sum_abs_le {m : ℕ} (b : Fin m → ℝ) : ∑ j, |b j| ≤ √(m : ℝ) * √(normSq b) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun j => |b j|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sq_abs] at h
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  exact Real.le_sqrt_of_sq_le h

lemma c1F_nonneg (J : ℕ) : 0 ≤ c1F (rexp (1 / 2) / 12) J := by
  unfold c1F; have := Real.pi_pos; positivity

lemma c2F_nonneg (J : ℕ) : 0 ≤ c2F (rexp (1 / 2) / 12) J := by
  unfold c2F; have := Real.pi_pos; positivity

/-- **The location rule error** (paper `t7:p08:rule`, first bound). -/
theorem rule_f (hn : 2 ≤ n) (c : Ret n) (s : ℝ) :
    |fPass c s - fGauss c s| ≤
      √(n : ℝ) * (c1F (rexp (1 / 2) / 12) (Jz n) * √(vsig2 c s) / Jz n) := by
  set E := c1F (rexp (1 / 2) / 12) (Jz n) * √(vsig2 c s) / Jz n with hE
  have hE0 : 0 ≤ E := by rw [hE]; have := c1F_nonneg (Jz n); positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hj : ∀ j, |betaP c s j - psiS (√(vsig2 c s)) ((A2 c).mulVec (a1Bar c s) j)| ≤ E :=
    fun j => lemmaBF1 (Jz_pos hn) _ (Real.sqrt_nonneg _)
  by_cases hb : normSq (bR c) = 0
  · unfold fPass fGauss; rw [hb]; simp; positivity
  have hb0 : 0 < √(normSq (bR c)) := Real.sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hb))
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hnR
  have e : fPass c s - fGauss c s = (∑ j, (betaP c s j -
      psiS (√(vsig2 c s)) ((A2 c).mulVec (a1Bar c s) j)) * bR c j) /
      (√(n : ℝ) * √(normSq (bR c))) := by
    unfold fPass fGauss; rw [← sub_div, ← Finset.sum_sub_distrib]
    congr 1; refine Finset.sum_congr rfl fun j _ => by ring
  rw [e, abs_div, abs_of_pos (mul_pos hsn hb0), div_le_iff₀ (mul_pos hsn hb0)]
  have h1 : |∑ j, (betaP c s j - psiS (√(vsig2 c s)) ((A2 c).mulVec (a1Bar c s) j)) * bR c j|
      ≤ ∑ j, E * |bR c j| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hj j) (abs_nonneg _)
  rw [← Finset.mul_sum] at h1
  have h2 := sum_abs_le (bR c)
  have hm : √((mA n : ℕ) : ℝ) = (n : ℝ) := by
    unfold mA; push_cast; exact Real.sqrt_sq hnR.le
  rw [hm] at h2
  have hsq : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hnR.le
  calc _ ≤ E * ∑ j, |bR c j| := h1
    _ ≤ E * (n * √(normSq (bR c))) := mul_le_mul_of_nonneg_left h2 hE0
    _ = √(n : ℝ) * E * (√(n : ℝ) * √(normSq (bR c))) := by
        rw [show √(n : ℝ) * E * (√(n : ℝ) * √(normSq (bR c))) =
          E * ((√(n : ℝ) * √(n : ℝ)) * √(normSq (bR c))) by ring, hsq]

/-- **The energy rule error** (paper `t7:p08:rule`, second bound). -/
theorem rule_w (hn : 2 ≤ n) (c : Ret n) (s : ℝ) :
    |wPass c s - wGauss c s| ≤ n * (c2F (rexp (1 / 2) / 12) (Jz n) * vsig2 c s / Jz n) := by
  set E := c2F (rexp (1 / 2) / 12) (Jz n) * vsig2 c s / Jz n with hE
  have hv : 0 ≤ vsig2 c s := le_max_left _ _
  have hE0 : 0 ≤ E := by rw [hE]; have := c2F_nonneg (Jz n); positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hj : ∀ j, |beta2P c s j - ∫ z, relu ((A2 c).mulVec (a1Bar c s) j + √(vsig2 c s) * z) ^ 2
      ∂gaussianReal 0 1| ≤ E := by
    intro j
    have h := lemmaBF2 (Jz_pos hn) ((A2 c).mulVec (a1Bar c s) j) (Real.sqrt_nonneg (vsig2 c s))
    rwa [Real.sq_sqrt hv] at h
  have e : wPass c s - wGauss c s = (∑ j, (beta2P c s j - ∫ z, relu ((A2 c).mulVec (a1Bar c s) j +
      √(vsig2 c s) * z) ^ 2 ∂gaussianReal 0 1)) / (n : ℝ) := by
    unfold wPass wGauss; rw [← sub_div, ← Finset.sum_sub_distrib]
  rw [e, abs_div, abs_of_pos hnR, div_le_iff₀ hnR]
  have h1 := (Finset.abs_sum_le_sum_abs (fun j => beta2P c s j - ∫ z, relu ((A2 c).mulVec
    (a1Bar c s) j + √(vsig2 c s) * z) ^ 2 ∂gaussianReal 0 1) Finset.univ).trans
    (Finset.sum_le_sum fun j _ => hj j)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) * n := by unfold mA; push_cast; ring
  rw [hm] at h1
  calc _ ≤ (n : ℝ) * n * E := h1
    _ = n * E * n := by ring

end BstLean.Part169
