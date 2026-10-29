import BstLean.Part169Lip
import BstLean.Part169Rule
import BstLean.Part169Mom

/-!
# Part 169 (file `Asm`): the location and energy errors from the exact-rule errors

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, "On their intersection, Minkowski, `t7:p08:rule` and
`t7:p08:grid` give `‖nΔ_f‖_{L⁸} ≤ a_f = A_f + B_f' + r_f + g_f`" (and the same for `ω`).

The split at a kept index `a` with latitude `s` and node `s_g`:
`f̄(s) − f̃(s_g) = [f̄(s) − f̄(s_g)] + [f̄(s_g) − f_G(s_g)] + [f_G(s_g) − f̃(s_g)]`
(grid, exact-rule error `Δ_f^exact = Δ^fl + Δ^b`, finite rule). The grid and rule terms are
bounded pointwise (`grid_f`, `rule_f`, with `ς(s_g)² ≤ σ₀²`); the exact-rule term keeps an
`L⁸` hypothesis (its bound `A_f + B_f'` is the probabilistic part of Part 08).

* `int_pow8_add_const`: `∫_K X⁸ ≤ A⁸` and `|Y| ≤ |X| + C` on `K` give `∫_K Y⁸ ≤ (A + C)⁸`.
* `exF`, `exW`: the exact-rule errors `n(f̄(s_g) − f_G(s_g))`, `n(ω̄(s_g) − ω_G(s_g))`.
* **`hF8_of_exact`**, **`hW8_of_exact`**: the `L⁸` bounds `a_f`, `a_ω` of `MomIn` from the
  `L⁸` bounds of the exact-rule errors, with `a_f = A + g_f + r_f`,
  `g_f = n·ΛΔ/(2√n√q)`, `r_f = n√n·c1F σ₀/J_z`, and `a_ω = A + g_ω + r_ω`,
  `g_ω = n·2Λ²(Δ/2)/(n√q)`, `r_ω = n·n c2F σ₀²/J_z`.
-/

namespace BstLean.Part169

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (latC Ix muI)
open BstLean.Part150 (c1F c2F)

variable {n : ℕ}

/-- **Minkowski in `L⁸` with a constant**: `∫_K X⁸ ≤ A⁸`, `|Y| ≤ |X| + C` on `K`, `μ(K) ≤ 1`
give `∫_K Y⁸ ≤ (A + C)⁸`. -/
theorem int_pow8_add_const {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {K : Set α} (hK : MeasurableSet K) (hK1 : μ.real K ≤ 1) {X Y : α → ℝ} (mY : Measurable Y)
    (iX : IntegrableOn (fun a => X a ^ 8) K μ) {A C : ℝ} (hA : 0 < A) (hC : 0 < C)
    (hX : ∫ a in K, X a ^ 8 ∂μ ≤ A ^ 8) (hY : ∀ a ∈ K, |Y a| ≤ |X a| + C) :
    IntegrableOn (fun a => Y a ^ 8) K μ ∧ ∫ a in K, Y a ^ 8 ∂μ ≤ (A + C) ^ 8 := by
  have hAC : 0 < A + C := add_pos hA hC
  set l := A / (A + C) with hl
  have hl0 : 0 < l := div_pos hA hAC
  have hl1 : 0 < 1 - l := by rw [hl, sub_pos, div_lt_one hAC]; linarith
  have e1 : 1 - l = C / (A + C) := by rw [hl]; field_simp; ring
  -- `(x + C)⁸ ≤ (A + C)⁷(x⁸/A⁷ + C)` for `x ≥ 0`
  have hpt0 : ∀ x : ℝ, 0 ≤ x → (x + C) ^ 8 ≤ (A + C) ^ 7 * (x ^ 8 / A ^ 7 + C) := by
    intro x hx
    have hc := (convexOn_pow (𝕜 := ℝ) 8).2 (Set.mem_Ici.mpr (div_nonneg hx hl0.le))
      (Set.mem_Ici.mpr (div_nonneg hC.le hl1.le)) hl0.le hl1.le (by ring)
    simp only [smul_eq_mul] at hc
    have e2 : l * (x / l) + (1 - l) * (C / (1 - l)) = x + C := by field_simp
    rw [e2] at hc
    refine hc.trans (le_of_eq ?_)
    rw [e1, hl]
    field_simp
  have hpt : ∀ a ∈ K, Y a ^ 8 ≤ (A + C) ^ 7 * (X a ^ 8 / A ^ 7 + C) := by
    intro a ha
    have h1 : Y a ^ 8 ≤ (|X a| + C) ^ 8 := by
      rw [← Even.pow_abs (by decide) (Y a)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hY a ha) 8
    refine h1.trans ?_
    have := hpt0 |X a| (abs_nonneg _)
    rwa [Even.pow_abs (by decide)] at this
  have i3 : IntegrableOn (fun a => (A + C) ^ 7 * (X a ^ 8 / A ^ 7 + C)) K μ :=
    ((iX.div_const _).add (integrable_const _)).const_mul _
  have iY : IntegrableOn (fun a => Y a ^ 8) K μ := by
    refine Integrable.mono' i3 (mY.pow_const 8).aestronglyMeasurable ((ae_restrict_iff' hK).mpr
      (Filter.Eventually.of_forall fun a ha => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt a ha
  refine ⟨iY, (setIntegral_mono_on iY i3 hK hpt).trans ?_⟩
  rw [integral_const_mul, integral_add (iX.div_const _) (integrable_const _), integral_div,
    integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
  have h1 : (∫ a in K, X a ^ 8 ∂μ) / A ^ 7 ≤ A := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h2 : μ.real K * C ≤ C := by nlinarith
  have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity : (0:ℝ) ≤ (A + C) ^ 7)
  nlinarith

/-- The node latitude of the index `a`. -/
noncomputable def sgR (c : Ret n) (a : Ix n) : ℝ := nodeS c (gIdx c (latC (paperDesignP n) c a))

/-- The exact-rule location error `n(f̄(s_g) − f_G(s_g))` at the node of `a`. -/
noncomputable def exF (c : Ret n) (a : Ix n) : ℝ := (n : ℝ) * (fbarS c (sgR c a) - fGauss c (sgR c a))

/-- The exact-rule energy error `n(ω̄(s_g) − ω_G(s_g))` at the node of `a`. -/
noncomputable def exW (c : Ret n) (a : Ix n) : ℝ := (n : ℝ) * (wbarS c (sgR c a) - wGauss c (sgR c a))

/-- **`‖n(f̄ − f̃)‖_{L⁸(K)} ≤ A + g_f + r_f`** from the `L⁸` bound `A` of the exact-rule error,
on the operator events (`OpB`), the upper `ς` bound at the nodes, and the bulk bound
`s² ≤ 1 − q` on `[L, H]`. -/
theorem hF8_of_exact (hn : 2 ≤ n) (c : Ret n) {O₁ O₂ q σ0 A : ℝ} (h1 : OpB (A1 c) O₁)
    (h2 : OpB (A2 c) O₂) (hO₁ : 0 < O₁) (hO₂ : 0 < O₂) (hq : 0 < q) (hσ : 0 < σ0)
    (hLH : nodeL c < nodeH c) (hbulk : ∀ s, nodeL c ≤ s → s ≤ nodeH c → s ^ 2 ≤ 1 - q)
    (hvs : ∀ a ∈ KR c, vsig2 c (sgR c a) ≤ σ0 ^ 2) (hA : 0 < A)
    (iX : IntegrableOn (fun a => exF c a ^ 8) (KR c) (muI n))
    (hX : ∫ a in KR c, exF c a ^ 8 ∂muI n ≤ A ^ 8) :
    IntegrableOn (fun a => ((n : ℝ) * (fbR c a - ftR c a)) ^ 8) (KR c) (muI n) ∧
      ∫ a in KR c, ((n : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI n ≤
        (A + ((n : ℝ) * (O₂ * O₁ * (nodeD c / 2) / (√(n : ℝ) * √q)) +
          n * (√(n : ℝ) * (c1F (rexp (1 / 2) / 12) (Jz n) * σ0 / Jz n)))) ^ 8 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hJ : (0 : ℝ) < Jz n := by exact_mod_cast (Jz_pos hn)
  have hD : 0 < nodeD c := div_pos (by linarith) (by exact_mod_cast (show 0 < Js n by
    unfold Js; omega))
  have hc1 : 0 < c1F (rexp (1 / 2) / 12) (Jz n) := by
    unfold c1F; have := Real.pi_pos; positivity
  have mY : Measurable (fun a => (n : ℝ) * (fbR c a - ftR c a)) :=
    ((measurable_fbR c).sub (measurable_ftR c)).const_mul _
  refine int_pow8_add_const (measurableSet_KR c) measureReal_le_one mY iX hA (by positivity) hX ?_
  intro a ha
  have hg := grid_f hn1 c h1 h2 hO₁.le hO₂.le hq hLH hbulk ha
  have hr := rule_f hn c (sgR c a)
  have hrs : √(vsig2 c (sgR c a)) ≤ σ0 := by
    rw [Real.sqrt_le_left hσ.le]; exact hvs a ha
  have hr' : |fPass c (sgR c a) - fGauss c (sgR c a)| ≤
      √(n : ℝ) * (c1F (rexp (1 / 2) / 12) (Jz n) * σ0 / Jz n) := by
    refine hr.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrs hc1.le) hJ.le
  have e : (n : ℝ) * (fbR c a - ftR c a) = (n : ℝ) * (fbR c a - fbarS c (sgR c a)) + exF c a -
      (n : ℝ) * (fPass c (sgR c a) - fGauss c (sgR c a)) := by
    unfold exF ftR sgR; ring
  rw [e]
  have t1 : |(n : ℝ) * (fbR c a - fbarS c (sgR c a))| ≤
      (n : ℝ) * (O₂ * O₁ * (nodeD c / 2) / (√(n : ℝ) * √q)) := by
    rw [abs_mul, abs_of_pos hnR]; exact mul_le_mul_of_nonneg_left hg hnR.le
  have t3 : |(n : ℝ) * (fPass c (sgR c a) - fGauss c (sgR c a))| ≤
      (n : ℝ) * (√(n : ℝ) * (c1F (rexp (1 / 2) / 12) (Jz n) * σ0 / Jz n)) := by
    rw [abs_mul, abs_of_pos hnR]; exact mul_le_mul_of_nonneg_left hr' hnR.le
  calc _ ≤ |(n : ℝ) * (fbR c a - fbarS c (sgR c a))| + |exF c a| +
        |(n : ℝ) * (fPass c (sgR c a) - fGauss c (sgR c a))| := by
        have h3 := abs_sub ((n : ℝ) * (fbR c a - fbarS c (sgR c a)) + exF c a)
          ((n : ℝ) * (fPass c (sgR c a) - fGauss c (sgR c a)))
        have h4 := abs_add_le ((n : ℝ) * (fbR c a - fbarS c (sgR c a))) (exF c a)
        linarith
    _ ≤ _ := by linarith

/-- **`‖n(ω̄ − ω̃)‖_{L⁸(K)} ≤ A + g_ω + r_ω`** from the `L⁸` bound `A` of the exact-rule error. -/
theorem hW8_of_exact (hn : 2 ≤ n) (c : Ret n) {O₁ O₂ q σ0 A : ℝ} (h1 : OpB (A1 c) O₁)
    (h2 : OpB (A2 c) O₂) (hO₁ : 0 < O₁) (hO₂ : 0 < O₂) (hq : 0 < q) (hσ : 0 < σ0)
    (hLH : nodeL c < nodeH c) (hbulk : ∀ s, nodeL c ≤ s → s ≤ nodeH c → s ^ 2 ≤ 1 - q)
    (hvs : ∀ a ∈ KR c, vsig2 c (sgR c a) ≤ σ0 ^ 2) (hA : 0 < A)
    (iX : IntegrableOn (fun a => exW c a ^ 8) (KR c) (muI n))
    (hX : ∫ a in KR c, exW c a ^ 8 ∂muI n ≤ A ^ 8) :
    IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 8) (KR c) (muI n) ∧
      ∫ a in KR c, ((n : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI n ≤
        (A + ((n : ℝ) * (2 * (O₂ * O₁) ^ 2 * (nodeD c / 2) / (n * √q)) +
          n * (n * (c2F (rexp (1 / 2) / 12) (Jz n) * σ0 ^ 2 / Jz n)))) ^ 8 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hJ : (0 : ℝ) < Jz n := by exact_mod_cast (Jz_pos hn)
  have hD : 0 < nodeD c := div_pos (by linarith) (by exact_mod_cast (show 0 < Js n by
    unfold Js; omega))
  have hc2 : 0 < c2F (rexp (1 / 2) / 12) (Jz n) := by
    unfold c2F; have := Real.pi_pos; positivity
  have mY : Measurable (fun a => (n : ℝ) * (wbR c a - wtR c a)) :=
    ((measurable_wbR c).sub (measurable_wtR c)).const_mul _
  refine int_pow8_add_const (measurableSet_KR c) measureReal_le_one mY iX hA (by positivity) hX ?_
  intro a ha
  have hg := grid_w hn1 c h1 h2 hO₁.le hO₂.le hq hLH hbulk ha
  have hr := rule_w hn c (sgR c a)
  have hr' : |wPass c (sgR c a) - wGauss c (sgR c a)| ≤
      n * (c2F (rexp (1 / 2) / 12) (Jz n) * σ0 ^ 2 / Jz n) := by
    refine hr.trans (mul_le_mul_of_nonneg_left ?_ hnR.le)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hvs a ha) hc2.le) hJ.le
  have e : (n : ℝ) * (wbR c a - wtR c a) = (n : ℝ) * (wbR c a - wbarS c (sgR c a)) + exW c a -
      (n : ℝ) * (wPass c (sgR c a) - wGauss c (sgR c a)) := by
    unfold exW wtR sgR; ring
  rw [e]
  have t1 : |(n : ℝ) * (wbR c a - wbarS c (sgR c a))| ≤
      (n : ℝ) * (2 * (O₂ * O₁) ^ 2 * (nodeD c / 2) / (n * √q)) := by
    rw [abs_mul, abs_of_pos hnR]; exact mul_le_mul_of_nonneg_left hg hnR.le
  have t3 : |(n : ℝ) * (wPass c (sgR c a) - wGauss c (sgR c a))| ≤
      (n : ℝ) * (n * (c2F (rexp (1 / 2) / 12) (Jz n) * σ0 ^ 2 / Jz n)) := by
    rw [abs_mul, abs_of_pos hnR]; exact mul_le_mul_of_nonneg_left hr' hnR.le
  have h3 := abs_sub ((n : ℝ) * (wbR c a - wbarS c (sgR c a)) + exW c a)
    ((n : ℝ) * (wPass c (sgR c a) - wGauss c (sgR c a)))
  have h4 := abs_add_le ((n : ℝ) * (wbR c a - wbarS c (sgR c a))) (exW c a)
  linarith

end BstLean.Part169
