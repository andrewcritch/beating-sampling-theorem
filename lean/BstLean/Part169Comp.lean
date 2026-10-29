import BstLean.Part169Scale

/-!
# Part 169 (file `Comp`): the bias price of Part 08 from the moment inputs

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, formulas `t7:p08:scale`, `t7:p08:mass`, `t7:p08:price`.

* `PB`: the paper's price
  `P_B = (c_f a_f² + B_S²/(8(1 − ε)))/n + 2μ_exc`, `c_f = χ/(2(2 − ε)d)`,
  `B_S = (a_ω + 2H_f a_f + a_f²/n + C_v)/d`,
  `μ_exc = ((a_ω + 2H_f a_f)/(0.99dnT))⁶ + (a_f²/(0.01dn²T))⁴`, `T = ε − v_max/d`.
  At `ε = 0.02`: `8(1 − ε) = 7.84` and `c_f = χ/(3.96 d)`, as in the paper.
* **`bias_price_paper`**: on a measurable set `K` of mass at most one, with
  `λ̄ = f̄/√e`, `λ̃ = f̃/√e`, `S̄ = γ(ω̄ − f̄² − V)`, `S̃ = γ·max(1/5, ω̃ − f̃²)`:
  `∫_K H²(N(λ̄c_A, S̄I), N(λ̃c_A, S̃I)) ≤ P_B`, from `S̄ ≥ γd` (`d ≥ 1/5`),
  `|c_A|² ≤ γenχ`, `|V| ≤ v_max`, and the moments
  `‖nΔ_ω‖_8 ≤ a_ω`, `‖nΔ_f‖_8 ≤ a_f`, `‖f̄‖_4, ‖f̄‖_24 ≤ H_f`, `‖nV‖_2 ≤ C_v` on `K`.
-/

namespace BstLean.Part169

open MeasureTheory Real
open BstLean.Part161 (hellG2)

/-- **The paper's bias price** `P_B` (formula `t7:p08:price` with `t7:p08:scale`,
`t7:p08:mass`). -/
noncomputable def PB (n : ℕ) (χ d ε vmax aw af Hf Cv : ℝ) : ℝ :=
  (χ / (2 * (2 - ε) * d) * af ^ 2 + ((aw + 2 * Hf * af + af ^ 2 / n + Cv) / d) ^ 2 /
      (8 * (1 - ε))) / n +
    2 * (((aw + 2 * Hf * af) / (99 / 100 * d * n * (ε - vmax / d))) ^ 6 +
      (af ^ 2 / (1 / 100 * d * n ^ 2 * (ε - vmax / d))) ^ 4)

/-- **The bias price from the moment inputs** (Part 08, `t7:p08:price`). -/
theorem bias_price_paper {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {K : Set α} (hK : MeasurableSet K) (hK1 : μ.real K ≤ 1) (n : ℕ) (hn : 0 < n)
    {γ e χ d ε vmax aw af Hf Cv cA2 : ℝ} (hγ : 0 < γ) (he : 0 < e) (hd : 1 / 5 ≤ d)
    (hc0 : 0 ≤ cA2) (hc : cA2 ≤ γ * e * n * χ) (hε1 : ε < 1) (hT : 0 < ε - vmax / d)
    (haw : 0 < aw) (haf : 0 < af) (hHf : 0 < Hf) (hCv : 0 < Cv)
    {fb ft wb wt V : α → ℝ} (mfb : Measurable fb) (mft : Measurable ft) (mwb : Measurable wb)
    (mwt : Measurable wt) (mV : Measurable V)
    (hSbd : ∀ a ∈ K, γ * d ≤ γ * (wb a - fb a ^ 2 - V a))
    (hVm : ∀ a ∈ K, |V a| ≤ vmax)
    (iW2 : IntegrableOn (fun a => ((n : ℝ) * (wb a - wt a)) ^ 2) K μ)
    (iW6 : IntegrableOn (fun a => ((n : ℝ) * (wb a - wt a)) ^ 6) K μ)
    (iW8 : IntegrableOn (fun a => ((n : ℝ) * (wb a - wt a)) ^ 8) K μ)
    (iF2 : IntegrableOn (fun a => ((n : ℝ) * (fb a - ft a)) ^ 2) K μ)
    (iF4 : IntegrableOn (fun a => ((n : ℝ) * (fb a - ft a)) ^ 4) K μ)
    (iF8 : IntegrableOn (fun a => ((n : ℝ) * (fb a - ft a)) ^ 8) K μ)
    (if4 : IntegrableOn (fun a => fb a ^ 4) K μ)
    (if24 : IntegrableOn (fun a => fb a ^ 24) K μ)
    (ifF2 : IntegrableOn (fun a => fb a ^ 2 * ((n : ℝ) * (fb a - ft a)) ^ 2) K μ)
    (ifF6 : IntegrableOn (fun a => fb a ^ 6 * ((n : ℝ) * (fb a - ft a)) ^ 6) K μ)
    (iV : IntegrableOn (fun a => ((n : ℝ) * V a) ^ 2) K μ)
    (hW8 : ∫ a in K, ((n : ℝ) * (wb a - wt a)) ^ 8 ∂μ ≤ aw ^ 8)
    (hF8 : ∫ a in K, ((n : ℝ) * (fb a - ft a)) ^ 8 ∂μ ≤ af ^ 8)
    (hf4 : ∫ a in K, fb a ^ 4 ∂μ ≤ Hf ^ 4)
    (hf24 : ∫ a in K, fb a ^ 24 ∂μ ≤ Hf ^ 24)
    (hV : ∫ a in K, ((n : ℝ) * V a) ^ 2 ∂μ ≤ Cv ^ 2) :
    ∫ a in K, hellG2 n ((fb a / √e - ft a / √e) ^ 2 * cA2) (γ * (wb a - fb a ^ 2 - V a))
        (γ * max (1 / 5) (wt a - ft a ^ 2)) ∂μ ≤ PB n χ d ε vmax aw af Hf Cv := by
  have hse : 0 < √e := Real.sqrt_pos.mpr he
  have hsq : ∀ a, √e * (fb a / √e - ft a / √e) = fb a - ft a := by
    intro a; field_simp
  have eF2 : (fun a => ((n : ℝ) * (√e * (fb a / √e - ft a / √e))) ^ 2) =
      fun a => ((n : ℝ) * (fb a - ft a)) ^ 2 := by funext a; rw [hsq]
  have eF8 : (fun a => ((n : ℝ) * (√e * (fb a / √e - ft a / √e))) ^ 8) =
      fun a => ((n : ℝ) * (fb a - ft a)) ^ 8 := by funext a; rw [hsq]
  obtain ⟨iS, hS⟩ := scale_L2 hK hK1 n hn hγ hd haw haf hHf hCv mfb mft mwb mwt mV hSbd iW2 iW8
    iF4 iF8 if4 ifF2 iV hW8 hF8 hf4 hV
  have hm := scale_mass hK hK1 n hn hγ hd haw haf hHf hT mfb mft mwb mwt hSbd hVm iW6 iW8 iF8
    if24 ifF6 hW8 hF8 hf24
  have mSb : Measurable (fun a => γ * (wb a - fb a ^ 2 - V a)) :=
    ((mwb.sub (mfb.pow_const 2)).sub mV).const_mul γ
  have mSt : Measurable (fun a => γ * max (1 / 5) (wt a - ft a ^ 2)) :=
    (measurable_const.max (mwt.sub (mft.pow_const 2))).const_mul γ
  have hSt : ∀ a ∈ K, 0 < γ * max (1 / 5) (wt a - ft a ^ 2) :=
    fun a _ => mul_pos hγ (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hP := bias_price_L8 μ hK hK1 n hn (lb := fun a => fb a / √e) (lt := fun a => ft a / √e)
    mSb mSt hγ he (by linarith : (0:ℝ) < d) hc0 hc hε1 haf hSbd hSt (eF2 ▸ iF2) (eF8 ▸ iF8) iS
    (by rw [eF8]; exact hF8) hS hm
  exact hP

end BstLean.Part169
