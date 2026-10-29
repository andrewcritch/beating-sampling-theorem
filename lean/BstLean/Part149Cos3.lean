import BstLean.Part149Kern
import BstLean.Part145C7
import BstLean.Part137Hat2
import BstLean.Part112Chaos

/-!
# Part 149, helper `Cos3`: the cosine of two points of the cheap stand-in, to the second order

Role: `delegations/statements/p149-spec.md`.

`w = (ξ, γ, γ′)` are three independent standard Gaussian vectors of `ℝⁿ`; `y = β·ξ + τ·γ`,
`y′ = β·ξ + τ·γ′`, `ρ² = β² + τ²`, `q = β²/ρ²`; the cosine is `⟨sphPt y, sphPt y′⟩`.

* `elin3`: the linear part `E = ⟨y, y′⟩/(nρ²) − q·(|y|² + |y′|²)/(2nρ²)` of the cosine error.
* `cos_ptR`, `rem_L2_core`, `lin_rem_unit_L2`: the pointwise bound, the `L²` bound and the Gaussian
  matrix form of the remainder `cos − cosv − E` (the variants of `cos_ptC`, `cos_L2_core`,
  `lin_cos_unit_L2c` of `Part145C2` without the term `|E|`).
* **`cheapRem_L2`**: `‖cos − q − E‖₂ ≤ jCosC n`.
* `elin3_int`, `phi3`, `phi3_eq`, `measurable_phi3`: the means of `E` over `γ′` and over
  `(γ, γ′)`, in closed form.
* **`elin3_cond_L2`**: `‖∫ E dγ′ − φ(ξ)‖₂ = √(q(1 − q)²(1 − q/2)/n)` (stated with `≤`).
* **`cheapCos3_L2`**: `‖∫ (cos − q) dγ′ − φ(ξ)‖₂ ≤ √(q(1 − q)²(1 − q/2)/n) + jCosC n`.
* `m4c`, **`cheapCos_M4`**: `‖(cos − q)²‖₂ ≤ m4c n q`; **`m4c_le_q`**, **`m4c_le`**:
  `m4c n q ≤ 5.283/n` for `n ≥ 4096` and `0 ≤ q ≤ 1`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 BstLean.Part145
open BstLean.Part137 (gauss_normSq gauss_normSq_sq)
open BstLean.Part112 (dw int_dw integral_dw integral_dw_mul memLp_dw)

/-- The linear part of the cosine error. -/
noncomputable def elin3 {n : ℕ} (β τ : ℝ) (w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  dotp (β • w.1 + τ • w.2.1) (β • w.1 + τ • w.2.2) / ((n : ℝ) * (β ^ 2 + τ ^ 2)) -
    β ^ 2 / (β ^ 2 + τ ^ 2) * ((normSq (β • w.1 + τ • w.2.1) + normSq (β • w.1 + τ • w.2.2)) /
      (2 * ((n : ℝ) * (β ^ 2 + τ ^ 2))))

/-! ## The pointwise bound of the remainder -/

/-- The sum of the seven terms of the identity after the linear part. -/
lemma ptR_fin {Tt E τ V u D q m X2 : ℝ} (hτ : |τ| ≤ 1) (hD0 : 0 ≤ D)
    (hDm2 : D ≤ m ^ 2) (hV0 : 0 ≤ V) (hVx : V ≤ X2) (hqm : |q| ≤ m)
    (hDu : D * |u| ≤ m ^ 3 / 8 + 3 / 2 * m ^ 4)
    (hTq : |Tt| * |q| ^ 3 ≤ 1 / 2 * ((|E| + D) * q ^ 2) + 6 * q ^ 4)
    (main : Tt = E + τ * V - E * u + E * D - 2 * τ * D * u + 3 / 2 * τ * D ^ 2 +
        (E + τ * D) * q ^ 2 + Tt * q ^ 3) :
    |Tt - E| ≤ |τ| * X2 + |E| * |u| + 5 / 2 * (|E| * m ^ 2) + 1 / 4 * m ^ 3 +
      12 * m ^ 4 := by
  have hE0 := abs_nonneg E
  have hτ0 := abs_nonneg τ
  have hq2 : q ^ 2 ≤ m ^ 2 := by
    rw [← sq_abs q]
    exact pow_le_pow_left₀ (abs_nonneg _) hqm 2
  have hq4 : |q| ^ 4 = q ^ 4 := by
    calc |q| ^ 4 = (|q| ^ 2) ^ 2 := by ring
      _ = (q ^ 2) ^ 2 := by rw [sq_abs]
      _ = q ^ 4 := by ring
  have hq4m : q ^ 4 ≤ m ^ 4 := by
    rw [← hq4]
    exact pow_le_pow_left₀ (abs_nonneg _) hqm 4
  have hDD : D ^ 2 ≤ m ^ 4 := by
    have := mul_le_mul hDm2 hDm2 hD0 (sq_nonneg m)
    have e : m ^ 2 * m ^ 2 = m ^ 4 := by ring
    have e' : D * D = D ^ 2 := by ring
    linarith
  have hcτ : |E + τ * D| ≤ |E| + D := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hD0]
    have := mul_le_of_le_one_left hD0 hτ
    linarith
  have b2 : |τ * V| ≤ |τ| * X2 := by
    rw [abs_mul, abs_of_nonneg hV0]
    exact mul_le_mul_of_nonneg_left hVx hτ0
  have b3 : |E * u| ≤ |E| * |u| := (abs_mul _ _).le
  have b4 : |E * D| ≤ |E| * m ^ 2 := by
    rw [abs_mul, abs_of_nonneg hD0]
    exact mul_le_mul_of_nonneg_left hDm2 hE0
  have b5 : |2 * τ * D * u| ≤ m ^ 3 / 4 + 3 * m ^ 4 := by
    have e : |2 * τ * D * u| = 2 * (|τ| * (D * |u|)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_nonneg hD0]
      ring
    have := mul_le_of_le_one_left (mul_nonneg hD0 (abs_nonneg u)) hτ
    rw [e]
    linarith
  have b6 : |3 / 2 * τ * D ^ 2| ≤ 3 / 2 * m ^ 4 := by
    have e : |3 / 2 * τ * D ^ 2| = 3 / 2 * (|τ| * D ^ 2) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg D),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      ring
    have := mul_le_of_le_one_left (sq_nonneg D) hτ
    rw [e]
    linarith
  have hEm : (|E| + D) * q ^ 2 ≤ (|E| + m ^ 2) * m ^ 2 :=
    mul_le_mul (by linarith) hq2 (sq_nonneg q) (add_nonneg hE0 (sq_nonneg m))
  have eEm : (|E| + m ^ 2) * m ^ 2 = |E| * m ^ 2 + m ^ 4 := by ring
  have b7 : |(E + τ * D) * q ^ 2| ≤ |E| * m ^ 2 + m ^ 4 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg q)]
    have h1 : |E + τ * D| * q ^ 2 ≤ (|E| + D) * q ^ 2 :=
      mul_le_mul_of_nonneg_right hcτ (sq_nonneg q)
    linarith
  have b8 : |Tt * q ^ 3| ≤ 1 / 2 * (|E| * m ^ 2) + 13 / 2 * m ^ 4 := by
    rw [abs_mul, abs_pow]
    linarith
  obtain ⟨l2, u2⟩ := abs_le.mp b2
  obtain ⟨l3, u3⟩ := abs_le.mp b3
  obtain ⟨l4, u4⟩ := abs_le.mp b4
  obtain ⟨l5, u5⟩ := abs_le.mp b5
  obtain ⟨l6, u6⟩ := abs_le.mp b6
  obtain ⟨l7, u7⟩ := abs_le.mp b7
  obtain ⟨l8, u8⟩ := abs_le.mp b8
  have main' : Tt - E = τ * V - E * u + E * D - 2 * τ * D * u + 3 / 2 * τ * D ^ 2 +
      (E + τ * D) * q ^ 2 + Tt * q ^ 3 := by linarith
  rw [abs_le]
  constructor
  · rw [main']; linarith
  · rw [main']; linarith

/-- The pointwise bound of the remainder of a cosine after its linear part
`E = c − τ(a² + b²)/2` (`cos_ptC` without the term `|E|`). -/
lemma cos_ptR {a b c τ T : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hτ : |τ| ≤ 1)
    (hT : |T| ≤ 1) (hTeq : 0 < a * b → T = c / (a * b)) :
    |T - τ - (c - τ * ((a ^ 2 + b ^ 2) / 2))| ≤
      |τ| * (((a ^ 2 - 1) ^ 2 + (b ^ 2 - 1) ^ 2) / 4) +
      |c - τ * ((a ^ 2 + b ^ 2) / 2)| * |((a ^ 2 - 1) + (b ^ 2 - 1)) / 2| +
      5 / 2 * (|c - τ * ((a ^ 2 + b ^ 2) / 2)| * max |a ^ 2 - 1| |b ^ 2 - 1| ^ 2) +
      1 / 4 * max |a ^ 2 - 1| |b ^ 2 - 1| ^ 3 + 12 * max |a ^ 2 - 1| |b ^ 2 - 1| ^ 4 := by
  obtain ⟨E, hE⟩ : ∃ E, E = c - τ * ((a ^ 2 + b ^ 2) / 2) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = a ^ 2 - 1 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = b ^ 2 - 1 := ⟨_, rfl⟩
  rw [← hE, ← hx, ← hy]
  obtain ⟨m, hm⟩ : ∃ m, m = max |x| |y| := ⟨_, rfl⟩
  rw [← hm]
  have hT2 : |T - τ| ≤ 2 := (abs_sub _ _).trans (by linarith)
  have hu : |x| ≤ m := hm ▸ le_max_left _ _
  have hw : |y| ≤ m := hm ▸ le_max_right _ _
  have hu' := abs_le.mp hu
  have hw' := abs_le.mp hw
  have hm0 : 0 ≤ m := (abs_nonneg _).trans hu
  have hE0 := abs_nonneg E
  have hτ0 := abs_nonneg τ
  rcases (mul_nonneg ha hb).eq_or_lt with h0 | hp
  · have n2 : 0 ≤ |τ| * ((x ^ 2 + y ^ 2) / 4) := by positivity
    have n3 : 0 ≤ |E| * |(x + y) / 2| := by positivity
    have n5 : 0 ≤ m ^ 3 := by positivity
    have hm1 : 1 ≤ m := by
      rcases mul_eq_zero.mp h0.symm with h | h
      · have e : x = -1 := by rw [hx, h]; norm_num
        rw [e] at hu'
        linarith [hu'.1]
      · have e : y = -1 := by rw [hy, h]; norm_num
        rw [e] at hw'
        linarith [hw'.1]
    have h4 : 1 ≤ m ^ 4 := one_le_pow₀ hm1
    have h2 : 1 ≤ m ^ 2 := one_le_pow₀ hm1
    have n4 : |E| * 1 ≤ |E| * m ^ 2 := mul_le_mul_of_nonneg_left h2 hE0
    have h5 : |T - τ - E| ≤ |T - τ| + |E| := abs_sub _ _
    linarith
  · obtain ⟨p, hpdef⟩ : ∃ p, p = a * b := ⟨_, rfl⟩
    rw [← hpdef] at hp hTeq
    have hp0 : p ≠ 0 := hp.ne'
    obtain ⟨q, hqdef⟩ : ∃ q, q = 1 - p := ⟨_, rfl⟩
    obtain ⟨D, hD⟩ : ∃ D, D = (a - b) ^ 2 / 2 := ⟨_, rfl⟩
    have hTp0 : (T - τ) * p = c - τ * p := by
      rw [hTeq hp]; field_simp
    have hTp : (T - τ) * (1 - q) = E + τ * D := by
      rw [hqdef, show 1 - (1 - p) = p by ring, hTp0, hE, hD, hpdef]; ring
    have hq : q = D - (x + y) / 2 := by rw [hqdef, hD, hx, hy, hpdef]; ring
    have hDid : D = (x - y) ^ 2 / 8 - D * ((x + y) / 2) + D ^ 2 / 2 := by
      rw [hD, hx, hy]; ring
    have key3 : T - τ = (E + τ * D) * (1 + q + q ^ 2) + (T - τ) * q ^ 3 := by
      linear_combination (1 + q + q ^ 2) * hTp
    have main : T - τ = E + τ * ((x - y) ^ 2 / 8) - E * ((x + y) / 2) + E * D -
        2 * τ * D * ((x + y) / 2) + 3 / 2 * τ * D ^ 2 + (E + τ * D) * q ^ 2 +
        (T - τ) * q ^ 3 := by
      linear_combination key3 + (E + τ * D) * hq + τ * hDid
    have hua : |a ^ 2 - 1| ≤ m := hx ▸ hu
    have hwb : |b ^ 2 - 1| ≤ m := hy ▸ hw
    have hqm : |q| ≤ m := by
      have := one_sub_mul_le ha hb hua hwb
      rwa [← hpdef, ← hqdef] at this
    have hum : |(x + y) / 2| ≤ m := by
      rw [abs_le]
      constructor <;> linarith
    have hD0 : 0 ≤ D := by rw [hD]; positivity
    have hDm : D ≤ m := hD ▸ half_sq_sub_le ha hb hua hwb
    have hDm2 : D ≤ m ^ 2 := hD ▸ half_sq_sub_le_sq ha hb hua hwb
    have hV0 : 0 ≤ (x - y) ^ 2 / 8 := by positivity
    have hVx : (x - y) ^ 2 / 8 ≤ (x ^ 2 + y ^ 2) / 4 := by linarith [sq_nonneg (x + y)]
    have hDu := ptC_Du hD0 hm0 hDm hDm2 hum hDid (ptC_Vu hu hw)
    have hcτ : |E + τ * D| ≤ |E| + D := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hD0]
      have := mul_le_of_le_one_left hD0 hτ
      linarith
    have hTq : |T - τ| * |q| ^ 3 ≤ 1 / 2 * ((|E| + D) * q ^ 2) + 6 * q ^ 4 := by
      refine ptC_Tq (abs_nonneg _) hT2 (by linarith) ?_
      rcases le_or_gt 0 (1 - q) with h | h
      · have e1 : |T - τ| * (1 - q) = |E + τ * D| := by
          rw [← hTp, abs_mul, abs_of_nonneg h]
        linarith
      · have := mul_nonpos_of_nonneg_of_nonpos (abs_nonneg (T - τ)) h.le
        linarith
    exact ptR_fin hτ hD0 hDm2 hV0 hVx hqm hDu hTq main

/-! ## The `L²` norm of the remainder -/

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The `L²` norm of a function with the pointwise bound of `cos_ptR`.** -/
lemma rem_L2_core {Ef X Y Df : Ω → ℝ} {τ c K Q : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hK : 0 ≤ K) (hQ : 0 ≤ Q) (hEm : AEStronglyMeasurable Ef μ)
    (hXm : AEStronglyMeasurable X μ) (hYm : AEStronglyMeasurable Y μ)
    (hDm : AEStronglyMeasurable Df μ)
    (hE2 : L2le μ (fun ω => Ef ω ^ 2) (c ^ 2 * K))
    (hX2 : L2le μ (fun ω => X ω ^ 2) K) (hY2 : L2le μ (fun ω => Y ω ^ 2) K)
    (hX4 : L2le μ (fun ω => X ω ^ 4) Q) (hY4 : L2le μ (fun ω => Y ω ^ 4) Q)
    (hpt : ∀ ω, |Df ω| ≤ |τ| * ((X ω ^ 2 + Y ω ^ 2) / 4) +
      |Ef ω| * |(X ω + Y ω) / 2| + 5 / 2 * (|Ef ω| * max |X ω| |Y ω| ^ 2) +
      1 / 4 * max |X ω| |Y ω| ^ 3 + 12 * max |X ω| |Y ω| ^ 4) :
    L2le μ Df (|τ| * (K / 2) + c * K + 5 / 2 * √(K * (√2 * Q)) +
      1 / 4 * √(√2 * K * (√2 * Q)) + 12 * (√2 * Q)) := by
  have hs2 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have hτ0 := abs_nonneg τ
  have hmm : AEStronglyMeasurable (fun ω => max |X ω| |Y ω|) μ :=
    (continuous_abs.comp_aestronglyMeasurable hXm).sup
      (continuous_abs.comp_aestronglyMeasurable hYm)
  have hM2 := l2_max_pow 2 hXm hYm hX2 hY2
  have hM4 := l2_max_pow 4 hXm hYm hX4 hY4
  have hM4' : L2le μ (fun ω => (max |X ω| |Y ω| ^ 2) ^ 2) (√2 * Q) :=
    hM4.congr_fun fun ω => by ring
  have hXY := hX2.add' hY2 hK hK
  have hUm : AEStronglyMeasurable (fun ω => (X ω + Y ω) / 2) μ := by
    have := (hXm.add hYm).const_mul (1 / 2 : ℝ)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  have hm2m : AEStronglyMeasurable (fun ω => max |X ω| |Y ω| ^ 2) μ := hmm.pow 2
  have t2 := hXY.const_mul_nonneg (c := |τ| / 4) (by positivity)
  have hU2 : L2le μ (fun ω => ((X ω + Y ω) / 2) ^ 2) K := by
    have h0 := hXY.const_mul_nonneg (c := 1 / 2) (by norm_num)
    refine (L2le.of_abs_le (hUm.pow 2) h0 (fun ω => ?_)).congr_bound
      (by ring)
    change |((X ω + Y ω) / 2) ^ 2| ≤ |1 / 2 * (X ω ^ 2 + Y ω ^ 2)|
    rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity)]
    linarith [sq_nonneg (X ω - Y ω)]
  have t3 := l2_abs_mul_of_sq (mul_nonneg (sq_nonneg c) hK) hK hEm hUm hE2 hU2
  have hE2' : L2le μ (fun ω => Ef ω ^ 2) K := by
    refine hE2.mono (mul_nonneg (sq_nonneg c) hK) ?_
    have : c ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have t4 := (l2_abs_mul_of_sq hK (mul_nonneg hs2 hQ) hEm hm2m hE2' hM4').const_mul_nonneg
    (c := 5 / 2) (by norm_num)
  have t5 := (l2_abs_mul_of_sq (mul_nonneg hs2 hK) (mul_nonneg hs2 hQ) hmm hm2m hM2
    hM4').const_mul_nonneg (c := 1 / 4) (by norm_num)
  have t6 := hM4.const_mul_nonneg (c := 12) (by norm_num)
  have htot := (((t2.add' t3 (by positivity) (by positivity)).add' t4
    (by positivity) (by positivity)).add' t5 (by positivity) (by positivity)).add' t6
    (by positivity) (by positivity)
  have hsq : √(c ^ 2 * K * K) = c * K := by
    rw [show c ^ 2 * K * K = (c * K) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg hc0 hK)
  refine (L2le.of_abs_le hDm htot (fun ω => ?_)).congr_bound (by rw [hsq]; ring)
  have hm0 : 0 ≤ max |X ω| |Y ω| := le_max_of_le_left (abs_nonneg _)
  refine (hpt ω).trans ((le_of_eq ?_).trans (le_abs_self _))
  rw [abs_of_nonneg (pow_nonneg hm0 2), abs_of_nonneg hm0]
  ring

end Generic

/-- **The remainder of the cosine link after its linear part**, unit inputs, a Gaussian matrix
with entry variance `v`: `‖cos − τ − E‖₂ ≤ jCosC n`,
`E = ⟨Mh, Mh′⟩/(nv) − τ·(|Mh|² + |Mh′|²)/(2nv)`, `τ = ⟨h, h′⟩`. -/
theorem lin_rem_unit_L2 {n k : ℕ} {v : ℝ} (hv : 0 < v) (hn : 1 ≤ n) {h h' : Fin k → ℝ}
    (hh : normSq h = 1) (hh' : normSq h' = 1) :
    L2le (gaussMat n k v)
      (fun M : Matrix (Fin n) (Fin k) ℝ =>
        dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - dotp h h' -
          (dotp (M.mulVec h) (M.mulVec h') / ((n : ℝ) * v) - dotp h h' *
            ((normSq (M.mulVec h) / ((n : ℝ) * v) + normSq (M.mulVec h') / ((n : ℝ) * v)) / 2)))
      (jCosC n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hE2, -⟩ := lin_E_moments (n := n) hv hn hh hh'
  unfold kEC K4 at hE2
  set τ := dotp h h' with hτdef
  set s := (n : ℝ) * v with hs
  have hs0 : 0 < s := mul_pos hn0 hv
  set K := √(12 + 48 / (n : ℝ)) / (n : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  have hQ0 := qCos_nonneg n
  have hτ : |τ| ≤ 1 := by
    have := abs_dotp_le_nrm h h'
    rwa [nrm_of_normSq_one hh, nrm_of_normSq_one hh', mul_one] at this
  have hτ' := abs_le.mp hτ
  have hτ2 : 0 ≤ 1 - τ ^ 2 := by nlinarith
  have hτ3 : 1 - τ ^ 2 ≤ 1 := by nlinarith [sq_nonneg τ]
  have hA : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (normSq (M.mulVec h) / s - 1) ^ 2) K := by
    have := dev_sq_L2 hv hn h
    rw [hh, one_pow, one_mul, mul_one, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; field_simp
  have hB : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (normSq (M.mulVec h') / s - 1) ^ 2) K := by
    have := dev_sq_L2 hv hn h'
    rw [hh', one_pow, one_mul, mul_one, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; field_simp
  have hA4 : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (normSq (M.mulVec h) / s - 1) ^ 4) (qCos n) := by
    have := dev_four_L2 hv hn h
    rw [hh, one_pow, one_mul, mul_one, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; field_simp
  have hB4 : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (normSq (M.mulVec h') / s - 1) ^ 4) (qCos n) := by
    have := dev_four_L2 hv hn h'
    rw [hh', one_pow, one_mul, mul_one, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; field_simp
  have hXm : AEStronglyMeasurable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      normSq (M.mulVec h) / s - 1) (gaussMat n k v) :=
    (((measurable_normSq_mulVec h).div_const _).sub_const _).aestronglyMeasurable
  have hYm : AEStronglyMeasurable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      normSq (M.mulVec h') / s - 1) (gaussMat n k v) :=
    (((measurable_normSq_mulVec h').div_const _).sub_const _).aestronglyMeasurable
  have hEm : AEStronglyMeasurable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      dotp (M.mulVec h) (M.mulVec h') / s -
        τ * ((normSq (M.mulVec h) / s + normSq (M.mulVec h') / s) / 2)) (gaussMat n k v) :=
    (((measurable_dotp_mulVec h h').div_const _).sub
      (((((measurable_normSq_mulVec h).div_const _).add
        ((measurable_normSq_mulVec h').div_const _)).div_const _).const_mul
          _)).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - τ -
        (dotp (M.mulVec h) (M.mulVec h') / s -
          τ * ((normSq (M.mulVec h) / s + normSq (M.mulVec h') / s) / 2))) (gaussMat n k v) :=
    (((measurable_dotp_sphPt h h').sub_const _).aestronglyMeasurable).sub hEm
  have hcore := rem_L2_core (τ := τ) hτ2 hτ3 hK0 hQ0 hEm hXm hYm hmeas hE2 hA hB hA4 hB4
    (fun M => ?_)
  · refine hcore.mono (add_nonneg (add_nonneg (add_nonneg (add_nonneg (by positivity)
      (mul_nonneg hτ2 hK0)) (by positivity)) (by positivity)) (by positivity)) ?_
    have ht : τ ^ 2 = |τ| ^ 2 := (sq_abs τ).symm
    have h17 : |τ| * (K / 2) + (1 - τ ^ 2) * K ≤ 17 / 16 * K := by
      rw [ht]
      nlinarith [mul_nonneg (sq_nonneg (|τ| - 1 / 4)) hK0]
    unfold jCosC K4
    rw [← hK]
    linarith
  -- the pointwise bound
  have hX0 : 0 ≤ normSq (M.mulVec h) := normSq_nonneg _
  have hY0 : 0 ≤ normSq (M.mulVec h') := normSq_nonneg _
  have hsqpos : 0 < √s := Real.sqrt_pos.mpr hs0
  have hab : √(normSq (M.mulVec h) / s) * √(normSq (M.mulVec h') / s) =
      nrm (M.mulVec h) * nrm (M.mulVec h') / s := by
    rw [Real.sqrt_div hX0, Real.sqrt_div hY0]
    unfold nrm
    field_simp
    rw [Real.sq_sqrt hs0.le]; ring
  have hT : |dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h'))| ≤ 1 :=
    abs_le.2 ⟨dotp_sphPt_ge hn _ _, dotp_sphPt_le hn _ _⟩
  have hTeq : 0 < √(normSq (M.mulVec h) / s) * √(normSq (M.mulVec h') / s) →
      dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) = dotp (M.mulVec h) (M.mulVec h') / s /
        (√(normSq (M.mulVec h) / s) * √(normSq (M.mulVec h') / s)) := by
    intro hpos
    have hx : normSq (M.mulVec h) ≠ 0 := by
      intro h0
      rw [h0, zero_div, Real.sqrt_zero, zero_mul] at hpos
      exact lt_irrefl _ hpos
    have hy : normSq (M.mulVec h') ≠ 0 := by
      intro h0
      rw [h0, zero_div, Real.sqrt_zero, mul_zero] at hpos
      exact lt_irrefl _ hpos
    rw [dotp_sphPt _ _ hx hy, hab]
    have := (nrm_pos_of_ne hx).ne'
    have := (nrm_pos_of_ne hy).ne'
    field_simp
  have hpt := cos_ptR (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hτ hT hTeq
  rw [Real.sq_sqrt (div_nonneg hX0 hs0.le), Real.sq_sqrt (div_nonneg hY0 hs0.le)] at hpt
  exact hpt

/-! ## The transfer to three Gaussian vectors -/

lemma rem_scale {n : ℕ} {β τ r : ℝ} (hr : 0 < r) (hr2 : r ^ 2 = β ^ 2 + τ ^ 2)
    (a b c : Fin n → ℝ) :
    dotp (sphPt ((β / r) • a + (τ / r) • b)) (sphPt ((β / r) • a + (τ / r) • c)) -
        β ^ 2 / (β ^ 2 + τ ^ 2) -
      (dotp ((β / r) • a + (τ / r) • b) ((β / r) • a + (τ / r) • c) / ((n : ℝ) * 1) -
        β ^ 2 / (β ^ 2 + τ ^ 2) * ((normSq ((β / r) • a + (τ / r) • b) / ((n : ℝ) * 1) +
          normSq ((β / r) • a + (τ / r) • c) / ((n : ℝ) * 1)) / 2)) =
    dotp (sphPt (β • a + τ • b)) (sphPt (β • a + τ • c)) - β ^ 2 / (β ^ 2 + τ ^ 2) -
      elin3 β τ (a, b, c) := by
  have e : ∀ d : Fin n → ℝ, (β / r) • a + (τ / r) • d = (1 / r) • (β • a + τ • d) := by
    intro d
    rw [smul_add, smul_smul, smul_smul]
    congr 2 <;> ring
  have hr1 : 0 < 1 / r := by positivity
  rw [e b, e c, sphPt_smul hr1, sphPt_smul hr1, dotp_smul_smul, normSq_smul, normSq_smul]
  unfold elin3
  dsimp only
  rw [← hr2]
  field_simp

/-- **The remainder of the cosine of two points of the cheap stand-in after the linear part**:
`‖⟨x, x′⟩ − q − E‖₂ ≤ jCosC n`. -/
theorem cheapRem_L2 {n : ℕ} (hn : 1 ≤ n) {β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ) :
    L2le ((stdGauss (Fin n)).prod ((stdGauss (Fin n)).prod (stdGauss (Fin n))))
      (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
        dotp (sphPt (β • w.1 + τ • w.2.1)) (sphPt (β • w.1 + τ • w.2.2)) -
          β ^ 2 / (β ^ 2 + τ ^ 2) - elin3 β τ w) (jCosC n) := by
  have hpos : 0 < β ^ 2 + τ ^ 2 := by positivity
  obtain ⟨r, hr0, hr2⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = β ^ 2 + τ ^ 2 :=
    ⟨√(β ^ 2 + τ ^ 2), Real.sqrt_pos.mpr hpos, Real.sq_sqrt hpos.le⟩
  have h1 : normSq ((β / r) • (Pi.single 0 1 : Fin 3 → ℝ) + (τ / r) • (Pi.single 1 1 : Fin 3 → ℝ))
      = 1 := by
    rw [normSq_h01, div_pow, div_pow, hr2]
    field_simp
  have h2 : normSq ((β / r) • (Pi.single 0 1 : Fin 3 → ℝ) + (τ / r) • (Pi.single 2 1 : Fin 3 → ℝ))
      = 1 := by
    rw [normSq_h02, div_pow, div_pow, hr2]
    field_simp
  have hc : dotp ((β / r) • (Pi.single 0 1 : Fin 3 → ℝ) + (τ / r) • (Pi.single 1 1 : Fin 3 → ℝ))
      ((β / r) • (Pi.single 0 1 : Fin 3 → ℝ) + (τ / r) • (Pi.single 2 1 : Fin 3 → ℝ)) =
      β ^ 2 / (β ^ 2 + τ ^ 2) := by
    rw [dotp_h01_h02, div_pow, hr2]
  have key := lin_rem_unit_L2 (n := n) (k := 3) (v := 1) one_pos hn h1 h2
  rw [hc] at key
  rw [← gauss3 n]
  have mφ : Measurable (fun M : Matrix (Fin n) (Fin 3) ℝ => (M.mulVec (Pi.single 0 1),
      M.mulVec (Pi.single 1 1), M.mulVec (Pi.single 2 1))) :=
    (measurable_mulVec_right _).prodMk ((measurable_mulVec_right _).prodMk
      (measurable_mulVec_right _))
  have mE : Measurable (elin3 (n := n) β τ) := by
    unfold elin3
    have c1 : Continuous (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
        β • w.1 + τ • w.2.1) := by fun_prop
    have c2 : Continuous (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
        β • w.1 + τ • w.2.2) := by fun_prop
    exact (((continuous_dotp.comp (c1.prodMk c2)).div_const _).sub
      (continuous_const.mul (((continuous_normSq.comp c1).add
        (continuous_normSq.comp c2)).div_const _))).measurable
  refine L2le.of_comp_map mφ
    (((measurable_cheapDot β τ).sub measurable_const).sub mE).aestronglyMeasurable
    (key.congr_fun fun M => ?_)
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
  exact rem_scale hr0 hr2 _ _ _

/-! ## The means of the linear part -/

/-- The coefficient of `⟨ξ, γ⟩` in the mean of the linear part over `γ′`. -/
noncomputable def cA3 (β τ : ℝ) (n : ℕ) : ℝ :=
  β * τ * (1 - β ^ 2 / (β ^ 2 + τ ^ 2)) / ((n : ℝ) * (β ^ 2 + τ ^ 2))

/-- The coefficient of `|γ|²` in the mean of the linear part over `γ′`. -/
noncomputable def cB3 (β τ : ℝ) (n : ℕ) : ℝ :=
  -(β ^ 2 / (β ^ 2 + τ ^ 2) * τ ^ 2 / (2 * ((n : ℝ) * (β ^ 2 + τ ^ 2))))

/-- The coefficient of `|ξ|²` in the mean of the linear part over `γ′`. -/
noncomputable def cC3 (β τ : ℝ) (n : ℕ) : ℝ :=
  β ^ 2 * (1 - β ^ 2 / (β ^ 2 + τ ^ 2)) / ((n : ℝ) * (β ^ 2 + τ ^ 2))

lemma dotp_sw {n : ℕ} (a b : Fin n → ℝ) : dotp a b = dotp b a := by
  unfold dotp
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma dotp_lin3 {n : ℕ} (β τ : ℝ) (ξ γ γ' : Fin n → ℝ) :
    dotp (β • ξ + τ • γ) (β • ξ + τ • γ') =
      β ^ 2 * normSq ξ + β * τ * dotp ξ γ' + β * τ * dotp ξ γ + τ ^ 2 * dotp γ γ' := by
  simp only [dotp, normSq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma normSq_lin3 {n : ℕ} (β τ : ℝ) (ξ γ : Fin n → ℝ) :
    normSq (β • ξ + τ • γ) = β ^ 2 * normSq ξ + 2 * β * τ * dotp ξ γ + τ ^ 2 * normSq γ := by
  simp only [dotp, normSq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The linear part as a polynomial of the inner products. -/
lemma elin3_expand {n : ℕ} (β τ : ℝ) (ξ γ γ' : Fin n → ℝ) :
    elin3 β τ (ξ, γ, γ') =
      (cC3 β τ n * normSq ξ + cA3 β τ n * dotp ξ γ + cB3 β τ n * normSq γ) +
        cA3 β τ n * dotp ξ γ' + τ ^ 2 / ((n : ℝ) * (β ^ 2 + τ ^ 2)) * dotp γ γ' +
        cB3 β τ n * normSq γ' := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (n : ℝ) * (β ^ 2 + τ ^ 2) := ⟨_, rfl⟩
  unfold elin3 cA3 cB3 cC3
  dsimp only
  rw [dotp_lin3, normSq_lin3, normSq_lin3, ← hs]
  ring

/-- The mean of `c₀ + c₁⟨v, z⟩ + c₁′⟨v′, z⟩ + c₂|z|²` over a standard Gaussian vector `z`. -/
lemma gint3 {n : ℕ} (c0 c1 c1' c2 : ℝ) (v v' : Fin n → ℝ) :
    Integrable (fun z : Fin n → ℝ => c0 + c1 * dotp v z + c1' * dotp v' z + c2 * normSq z)
        (stdGauss (Fin n)) ∧
      ∫ z : Fin n → ℝ, (c0 + c1 * dotp v z + c1' * dotp v' z + c2 * normSq z)
        ∂stdGauss (Fin n) = c0 + c2 * n := by
  have i0 : Integrable (fun _ : Fin n → ℝ => c0) (stdGauss (Fin n)) := integrable_const _
  have i1 : Integrable (fun z : Fin n → ℝ => c1 * dotp v z) (stdGauss (Fin n)) :=
    (int_dw v).const_mul c1
  have i2 : Integrable (fun z : Fin n → ℝ => c1' * dotp v' z) (stdGauss (Fin n)) :=
    (int_dw v').const_mul c1'
  have i3 : Integrable (fun z : Fin n → ℝ => c2 * normSq z) (stdGauss (Fin n)) :=
    (gauss_normSq n).1.const_mul c2
  have e1 : ∫ z : Fin n → ℝ, dotp v z ∂stdGauss (Fin n) = 0 := integral_dw v
  have e2 : ∫ z : Fin n → ℝ, dotp v' z ∂stdGauss (Fin n) = 0 := integral_dw v'
  have i01 : Integrable (fun z : Fin n → ℝ => c0 + c1 * dotp v z) (stdGauss (Fin n)) :=
    i0.add i1
  have i012 : Integrable (fun z : Fin n → ℝ => c0 + c1 * dotp v z + c1' * dotp v' z)
      (stdGauss (Fin n)) := i01.add i2
  refine ⟨i012.add i3, ?_⟩
  rw [integral_add i012 i3, integral_add i01 i2, integral_add i0 i1,
    integral_const_mul, integral_const_mul, integral_const_mul, (gauss_normSq n).2, e1, e2]
  simp

/-- **The mean of the linear part over `γ′`.** -/
lemma elin3_int {n : ℕ} (β τ : ℝ) (ξ γ : Fin n → ℝ) :
    Integrable (fun γ' : Fin n → ℝ => elin3 β τ (ξ, γ, γ')) (stdGauss (Fin n)) ∧
      ∫ γ' : Fin n → ℝ, elin3 β τ (ξ, γ, γ') ∂stdGauss (Fin n) =
        cC3 β τ n * normSq ξ + cA3 β τ n * dotp ξ γ + cB3 β τ n * normSq γ + cB3 β τ n * n := by
  have e : (fun γ' : Fin n → ℝ => elin3 β τ (ξ, γ, γ')) = fun γ' =>
      (cC3 β τ n * normSq ξ + cA3 β τ n * dotp ξ γ + cB3 β τ n * normSq γ) +
        cA3 β τ n * dotp ξ γ' + τ ^ 2 / ((n : ℝ) * (β ^ 2 + τ ^ 2)) * dotp γ γ' +
        cB3 β τ n * normSq γ' := funext fun γ' => elin3_expand β τ ξ γ γ'
  rw [e]
  exact gint3 _ _ _ _ _ _

/-- `φ(ξ)`: the mean of the linear part over both Gaussian vectors `γ, γ'`. -/
noncomputable def phi3 {n : ℕ} (β τ : ℝ) (ξ : Fin n → ℝ) : ℝ :=
  ∫ γ, ∫ γ', elin3 β τ (ξ, γ, γ') ∂stdGauss (Fin n) ∂stdGauss (Fin n)

/-- **`φ(ξ)` in closed form.** -/
lemma phi3_eq {n : ℕ} (β τ : ℝ) (ξ : Fin n → ℝ) :
    phi3 β τ ξ = cC3 β τ n * normSq ξ + 2 * cB3 β τ n * n := by
  have e : (fun γ : Fin n → ℝ => ∫ γ', elin3 β τ (ξ, γ, γ') ∂stdGauss (Fin n)) = fun γ =>
      (cC3 β τ n * normSq ξ + cB3 β τ n * n) + cA3 β τ n * dotp ξ γ + 0 * dotp ξ γ +
        cB3 β τ n * normSq γ := funext fun γ => by
    rw [(elin3_int β τ ξ γ).2]; ring
  unfold phi3
  rw [e, (gint3 _ _ _ _ _ _).2]
  ring

lemma measurable_phi3 {n : ℕ} (β τ : ℝ) : Measurable (phi3 (n := n) β τ) := by
  have e : phi3 (n := n) β τ = fun ξ => cC3 β τ n * normSq ξ + 2 * cB3 β τ n * n :=
    funext (phi3_eq β τ)
  rw [e]
  exact (measurable_normSq.const_mul _).add_const _

/-! ## The variance of the conditional mean of the linear part -/

/-- The second moment of `a⟨ξ, γ⟩ + c` over `ξ`. -/
lemma gsec3 {n : ℕ} (a c : ℝ) (γ : Fin n → ℝ) :
    Integrable (fun ξ : Fin n → ℝ => (a * dotp ξ γ + c) ^ 2) (stdGauss (Fin n)) ∧
      ∫ ξ : Fin n → ℝ, (a * dotp ξ γ + c) ^ 2 ∂stdGauss (Fin n) = a ^ 2 * normSq γ + c ^ 2 := by
  have e : (fun ξ : Fin n → ℝ => (a * dotp ξ γ + c) ^ 2) = fun ξ =>
      a ^ 2 * (dw γ ξ * dw γ ξ) + 2 * a * c * dw γ ξ + c ^ 2 := funext fun ξ => by
    rw [dotp_sw ξ γ]
    change (a * dw γ ξ + c) ^ 2 = _
    ring
  have i1 : Integrable (fun ξ : Fin n → ℝ => a ^ 2 * (dw γ ξ * dw γ ξ)) (stdGauss (Fin n)) :=
    ((memLp_dw γ).integrable_mul (memLp_dw γ)).const_mul _
  have i2 : Integrable (fun ξ : Fin n → ℝ => 2 * a * c * dw γ ξ) (stdGauss (Fin n)) :=
    (int_dw γ).const_mul _
  have i3 : Integrable (fun _ : Fin n → ℝ => c ^ 2) (stdGauss (Fin n)) := integrable_const _
  have e3 : ∑ i, γ i * γ i = normSq γ := by
    unfold normSq
    exact Finset.sum_congr rfl fun i _ => by ring
  have i12 : Integrable (fun ξ : Fin n → ℝ => a ^ 2 * (dw γ ξ * dw γ ξ) + 2 * a * c * dw γ ξ)
      (stdGauss (Fin n)) := i1.add i2
  rw [e]
  refine ⟨i12.add i3, ?_⟩
  rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_dw_mul, integral_dw, e3]
  simp

/-- `‖a⟨ξ, γ⟩ + b(|γ|² − n)‖₂ = √(a²n + 2b²n)` (stated with `≤`). -/
lemma gG_L2 {n : ℕ} (a b : ℝ) :
    L2le ((stdGauss (Fin n)).prod (stdGauss (Fin n)))
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => a * dotp p.1 p.2 + b * (normSq p.2 - n))
      (√(a ^ 2 * n + 2 * b ^ 2 * n)) := by
  have hnn : ∀ γ : Fin n → ℝ, 0 ≤ a ^ 2 * normSq γ + (b * (normSq γ - n)) ^ 2 := fun γ =>
    add_nonneg (mul_nonneg (sq_nonneg a) (normSq_nonneg γ)) (sq_nonneg _)
  have hA0 : (0 : ℝ) ≤ a ^ 2 * n + 2 * b ^ 2 * n := by positivity
  -- the function of `γ`
  have hg : L2le (stdGauss (Fin n))
      (fun γ : Fin n → ℝ => √(a ^ 2 * normSq γ + (b * (normSq γ - n)) ^ 2))
      (√(a ^ 2 * n + 2 * b ^ 2 * n)) := by
    have e : (fun γ : Fin n → ℝ => √(a ^ 2 * normSq γ + (b * (normSq γ - n)) ^ 2) ^ 2) =
        fun γ => a ^ 2 * normSq γ + (b ^ 2 * normSq γ ^ 2 - 2 * b ^ 2 * n * normSq γ +
          b ^ 2 * (n : ℝ) ^ 2) := funext fun γ => by
      rw [Real.sq_sqrt (hnn γ)]; ring
    have i1 : Integrable (fun γ : Fin n → ℝ => a ^ 2 * normSq γ) (stdGauss (Fin n)) :=
      (gauss_normSq n).1.const_mul _
    have i2 : Integrable (fun γ : Fin n → ℝ => b ^ 2 * normSq γ ^ 2) (stdGauss (Fin n)) :=
      (gauss_normSq_sq n).1.const_mul _
    have i3 : Integrable (fun γ : Fin n → ℝ => 2 * b ^ 2 * n * normSq γ) (stdGauss (Fin n)) :=
      (gauss_normSq n).1.const_mul _
    have i4 : Integrable (fun _ : Fin n → ℝ => b ^ 2 * (n : ℝ) ^ 2) (stdGauss (Fin n)) :=
      integrable_const _
    have i23 : Integrable (fun γ : Fin n → ℝ => b ^ 2 * normSq γ ^ 2 -
        2 * b ^ 2 * n * normSq γ) (stdGauss (Fin n)) := i2.sub i3
    have i234 : Integrable (fun γ : Fin n → ℝ => b ^ 2 * normSq γ ^ 2 -
        2 * b ^ 2 * n * normSq γ + b ^ 2 * (n : ℝ) ^ 2) (stdGauss (Fin n)) := i23.add i4
    refine ⟨?_, ?_, ?_⟩
    · exact ((measurable_normSq.const_mul _).add
        (((measurable_normSq.sub_const _).const_mul _).pow_const 2)).sqrt.aestronglyMeasurable
    · rw [e]
      exact i1.add i234
    · rw [e, integral_add i1 i234, integral_add i23 i4,
        integral_sub i2 i3, integral_const_mul, integral_const_mul, integral_const_mul,
        (gauss_normSq n).2, (gauss_normSq_sq n).2, Real.sq_sqrt hA0]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, add_le_add_iff_left]
      apply le_of_eq
      ring
  -- the sections in `ξ`
  have mf : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      a * dotp z.2 z.1 + b * (normSq z.1 - n)) :=
    ((continuous_dotp.measurable.comp (measurable_snd.prodMk measurable_fst)).const_mul _).add
      (((measurable_normSq.comp measurable_fst).sub_const _).const_mul _)
  have h1 : L2le ((stdGauss (Fin n)).prod (stdGauss (Fin n)))
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) => a * dotp z.2 z.1 + b * (normSq z.1 - n))
      (√(a ^ 2 * n + 2 * b ^ 2 * n)) := by
    refine L2le.prod mf.aestronglyMeasurable hg (Filter.Eventually.of_forall fun γ => ?_)
    have hs := gsec3 a (b * (normSq γ - n)) γ
    refine ⟨hs.1, ?_⟩
    rw [Real.sq_sqrt (hnn γ)]
    exact le_of_eq hs.2
  have := h1.comp_map (P := (stdGauss (Fin n)).prod (stdGauss (Fin n))) (φ := Prod.swap)
    measurable_swap Measure.prod_swap
  exact this.congr_fun fun z => by simp

lemma cAB3_eq {n : ℕ} (hn : 1 ≤ n) {β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ) :
    cA3 β τ n ^ 2 * n + 2 * cB3 β τ n ^ 2 * n =
      β ^ 2 / (β ^ 2 + τ ^ 2) * (1 - β ^ 2 / (β ^ 2 + τ ^ 2)) ^ 2 *
        (1 - β ^ 2 / (β ^ 2 + τ ^ 2) / 2) / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < β ^ 2 + τ ^ 2 := by positivity
  unfold cA3 cB3
  field_simp
  ring

/-- **The conditional mean of the linear part over `γ′`, centred by `φ(ξ)`**, in `L²` over
`(ξ, γ)`: its second moment is `q(1 − q)²(1 − q/2)/n`. -/
theorem elin3_cond_L2 {n : ℕ} (hn : 1 ≤ n) {β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ) :
    L2le ((stdGauss (Fin n)).prod (stdGauss (Fin n)))
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        (∫ γ', elin3 β τ (p.1, p.2, γ') ∂stdGauss (Fin n)) - phi3 β τ p.1)
      (√(β ^ 2 / (β ^ 2 + τ ^ 2) * (1 - β ^ 2 / (β ^ 2 + τ ^ 2)) ^ 2 *
        (1 - β ^ 2 / (β ^ 2 + τ ^ 2) / 2) / (n : ℝ))) := by
  refine ((gG_L2 (n := n) (cA3 β τ n) (cB3 β τ n)).congr_fun fun p => ?_).congr_bound
    (congrArg Real.sqrt (cAB3_eq hn hβ hτ))
  rw [(elin3_int β τ p.1 p.2).2, phi3_eq]
  ring

/-! ## The three-point bound -/

lemma cheapDot_int {n : ℕ} (hn : 1 ≤ n) (β τ q : ℝ) (ξ γ : Fin n → ℝ) :
    Integrable (fun γ' : Fin n → ℝ =>
      dotp (sphPt (β • ξ + τ • γ)) (sphPt (β • ξ + τ • γ')) - q) (stdGauss (Fin n)) := by
  have m0 : Measurable (fun γ' : Fin n → ℝ => (ξ, γ, γ')) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have m1 := (measurable_cheapDot (n := n) β τ).comp m0
  simp only [Function.comp_def] at m1
  have i1 : Integrable (fun γ' : Fin n → ℝ =>
      dotp (sphPt (β • ξ + τ • γ)) (sphPt (β • ξ + τ • γ'))) (stdGauss (Fin n)) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) m1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun γ' => ?_)
    rw [Real.norm_eq_abs]
    exact abs_le.mpr (abs_cheapDot_mem hn β τ (ξ, γ, γ'))
  exact i1.sub (integrable_const q)

/-- **The mean of the cosine error over the second point, centred by `φ(ξ)`**, in `L²` over
`(ξ, γ)`. -/
theorem cheapCos3_L2 {n : ℕ} (hn : 1 ≤ n) {β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ) :
    L2le ((stdGauss (Fin n)).prod (stdGauss (Fin n)))
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        (∫ γ', (dotp (sphPt (β • p.1 + τ • p.2)) (sphPt (β • p.1 + τ • γ')) -
          β ^ 2 / (β ^ 2 + τ ^ 2)) ∂stdGauss (Fin n)) - phi3 β τ p.1)
      (√(β ^ 2 / (β ^ 2 + τ ^ 2) * (1 - β ^ 2 / (β ^ 2 + τ ^ 2)) ^ 2 *
        (1 - β ^ 2 / (β ^ 2 + τ ^ 2) / 2) / (n : ℝ)) + jCosC n) := by
  have hR := cheapRem_L2 hn hβ hτ
  have hass := hR.comp_map
    (P := ((stdGauss (Fin n)).prod (stdGauss (Fin n))).prod (stdGauss (Fin n)))
    (φ := MeasurableEquiv.prodAssoc) MeasurableEquiv.prodAssoc.measurable
    Measure.prodAssoc_prod
  have hint : L2le ((stdGauss (Fin n)).prod (stdGauss (Fin n)))
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        ∫ γ', (dotp (sphPt (β • p.1 + τ • p.2)) (sphPt (β • p.1 + τ • γ')) -
          β ^ 2 / (β ^ 2 + τ ^ 2) - elin3 β τ (p.1, p.2, γ')) ∂stdGauss (Fin n))
      (jCosC n) := hass.integral_right
  have key := (elin3_cond_L2 hn hβ hτ).add' hint (Real.sqrt_nonneg _) (jCosC_nonneg n)
  refine key.congr_fun fun p => ?_
  rw [integral_sub (cheapDot_int hn β τ _ p.1 p.2) (elin3_int β τ p.1 p.2).1]
  ring

/-! ## The fourth moment -/

/-- The bound of `lin_cos_M4` for the `L²` norm of the square of the cosine error. -/
noncomputable def m4c (n : ℕ) (q : ℝ) : ℝ :=
  √(((1 - q ^ 2) * √(kEC n) + j4C n) ^ 4 + t4C n)

/-- **The fourth moment of the cosine error of two points of the cheap stand-in.** -/
theorem cheapCos_M4 {n : ℕ} (hn : 1 ≤ n) {β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ) :
    L2le ((stdGauss (Fin n)).prod ((stdGauss (Fin n)).prod (stdGauss (Fin n))))
      (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
        (dotp (sphPt (β • w.1 + τ • w.2.1)) (sphPt (β • w.1 + τ • w.2.2)) -
          β ^ 2 / (β ^ 2 + τ ^ 2)) ^ 2) (m4c n (β ^ 2 / (β ^ 2 + τ ^ 2))) := by
  have hpos : 0 < β ^ 2 + τ ^ 2 := by positivity
  have hc : cosv (β • (Pi.single 0 1 : Fin 3 → ℝ) + τ • (Pi.single 1 1 : Fin 3 → ℝ))
      (β • (Pi.single 0 1 : Fin 3 → ℝ) + τ • (Pi.single 2 1 : Fin 3 → ℝ)) =
      β ^ 2 / (β ^ 2 + τ ^ 2) := by
    unfold cosv nrm
    rw [normSq_h01, normSq_h02, dotp_h01_h02, Real.mul_self_sqrt hpos.le]
  have key := lin_cos_M4 (n := n) (k := 3) (v := 1) one_pos hn
    (β • (Pi.single 0 1 : Fin 3 → ℝ) + τ • (Pi.single 1 1 : Fin 3 → ℝ))
    (β • (Pi.single 0 1 : Fin 3 → ℝ) + τ • (Pi.single 2 1 : Fin 3 → ℝ))
    (by rw [normSq_h01]; exact hpos.ne') (by rw [normSq_h02]; exact hpos.ne')
  rw [hc] at key
  have hB0 : 0 ≤ ((1 - (β ^ 2 / (β ^ 2 + τ ^ 2)) ^ 2) * √(kEC n) + j4C n) ^ 4 + t4C n :=
    add_nonneg (by positivity) (t4C_nonneg n)
  have key2 : L2le (gaussMat n 3 1) (fun M : Matrix (Fin n) (Fin 3) ℝ =>
      (dotp (sphPt (M.mulVec (β • (Pi.single 0 1 : Fin 3 → ℝ) + τ • (Pi.single 1 1 : Fin 3 → ℝ))))
        (sphPt (M.mulVec (β • (Pi.single 0 1 : Fin 3 → ℝ) + τ • (Pi.single 2 1 : Fin 3 → ℝ)))) -
        β ^ 2 / (β ^ 2 + τ ^ 2)) ^ 2) (m4c n (β ^ 2 / (β ^ 2 + τ ^ 2))) :=
    ⟨key.1.pow 2, key.2.1, key.2.2.trans (le_of_eq (Real.sq_sqrt hB0).symm)⟩
  rw [← gauss3 n]
  have mφ : Measurable (fun M : Matrix (Fin n) (Fin 3) ℝ => (M.mulVec (Pi.single 0 1),
      M.mulVec (Pi.single 1 1), M.mulVec (Pi.single 2 1))) :=
    (measurable_mulVec_right _).prodMk ((measurable_mulVec_right _).prodMk
      (measurable_mulVec_right _))
  refine L2le.of_comp_map mφ
    (((measurable_cheapDot β τ).sub measurable_const).pow_const 2).aestronglyMeasurable
    (key2.congr_fun fun M => ?_)
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul]

/-! ## The number for `n ≥ 4096` -/

/-- **`m4c n q ≤ √(((1 − q²)·1.8617 + 0.4195)⁴ + 0.8295)/n`** for `n ≥ 4096`, `0 ≤ q ≤ 1`. -/
theorem m4c_le_q {n : ℕ} (hn : 4096 ≤ n) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    m4c n q ≤ √(((1 - q ^ 2) * (18617 / 10000) + 4195 / 10000) ^ 4 + 8295 / 10000) /
      (n : ℝ) := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs : (64 : ℝ) ≤ √(n : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 1 / (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = 1 / √(n : ℝ) := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hy]; positivity
  have hz0 : 0 < z := by rw [hz]; positivity
  have hz1 : z ≤ 1 / 64 := by rw [hz]; exact one_div_le_one_div_of_le (by norm_num) hs
  have hy1 : y ≤ 1 / 4096 := by rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  have hyz : y = z * z := by
    rw [hy, hz, div_mul_div_comm, one_mul, Real.mul_self_sqrt hx0.le]
  have h2 := sqrt2_le
  have h20 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have hK0 := K4_nonneg n
  have hK : K4 n ≤ 17329 / 5000 := by
    unfold K4
    refine sqrt_le_of_sq (by norm_num) ?_
    have : 48 / (n : ℝ) ≤ 48 / 4096 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
    norm_num at this ⊢
    linarith
  have hQ0 := qCos_nonneg n
  have hQ : qCos n ≤ 25759 / 625 * y ^ 2 := by
    have e : qCos n = √(1680 + 76160 * y + 467712 * y ^ 2 + 645120 * y ^ 3) * y ^ 2 := by
      have e1 : 1680 + 76160 / (n : ℝ) + 467712 / (n : ℝ) ^ 2 + 645120 / (n : ℝ) ^ 3 =
          1680 + 76160 * y + 467712 * y ^ 2 + 645120 * y ^ 3 := by rw [hy]; ring
      unfold qCos
      rw [e1, hy]
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_right (sqrt_le_of_sq (by norm_num) ?_) (by positivity)
    have a1 : y ^ 2 ≤ (1 / 4096) ^ 2 := pow_le_pow_left₀ hy0.le hy1 2
    have a2 : y ^ 3 ≤ (1 / 4096) ^ 3 := pow_le_pow_left₀ hy0.le hy1 3
    norm_num at a1 a2 ⊢
    linarith
  have hy2 : 0 < y ^ 2 := by positivity
  have hyz64 : y ≤ 1 / 64 * z := by rw [hyz]; exact mul_le_mul_of_nonneg_right hz1 hz0.le
  -- the three parts
  have s1 : √(kEC n) ≤ 18617 / 10000 * z := by
    refine sqrt_le_of_sq (by positivity) ?_
    have e : kEC n = K4 n * y := by unfold kEC; rw [hy]; ring
    have e2 : (18617 / 10000 * z) ^ 2 = (18617 / 10000) ^ 2 * y := by rw [hyz]; ring
    rw [e, e2]
    have := mul_le_mul_of_nonneg_right hK hy0.le
    nlinarith
  have s2 : √(qCos n) ≤ 642 / 100 * y := by
    refine sqrt_le_of_sq (by positivity) ?_
    nlinarith
  have s3 : √(qCos n * (√2 * qCos n)) ≤ 490126 / 10000 * y ^ 2 := by
    refine sqrt_le_of_sq (by positivity) ?_
    have hsQ : √2 * qCos n ≤ 141422 / 100000 * (25759 / 625 * y ^ 2) :=
      mul_le_mul h2 hQ hQ0 (by norm_num)
    have := mul_le_mul hQ hsQ (by positivity) (by positivity)
    refine this.trans ?_
    have e : 25759 / 625 * y ^ 2 * (141422 / 100000 * (25759 / 625 * y ^ 2)) =
        25759 / 625 * (141422 / 100000) * (25759 / 625) * (y ^ 2) ^ 2 := by ring
    rw [e, mul_pow]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have s4 : √(√(qCos n * (√2 * qCos n))) ≤ 7001 / 1000 * y := by
    refine sqrt_le_of_sq (by positivity) ?_
    nlinarith
  have hj0 := j4C_nonneg n
  have hj : j4C n ≤ 4195 / 10000 * z := by
    have : j4C n ≤ 26842 / 1000 * y := by unfold j4C; linarith
    linarith
  have hq2 : 0 ≤ 1 - q ^ 2 := by nlinarith
  have hbase : (1 - q ^ 2) * √(kEC n) + j4C n ≤
      ((1 - q ^ 2) * (18617 / 10000) + 4195 / 10000) * z := by
    have := mul_le_mul_of_nonneg_left s1 hq2
    linarith
  have hbase0 : 0 ≤ (1 - q ^ 2) * √(kEC n) + j4C n := by positivity
  have h4 := pow_le_pow_left₀ hbase0 hbase 4
  have e4 : (((1 - q ^ 2) * (18617 / 10000) + 4195 / 10000) * z) ^ 4 =
      ((1 - q ^ 2) * (18617 / 10000) + 4195 / 10000) ^ 4 * y ^ 2 := by rw [hyz]; ring
  have ht : t4C n ≤ 8295 / 10000 * y ^ 2 := by
    unfold t4C
    have h1 : qCos n ^ 2 ≤ (25759 / 625 * y ^ 2) ^ 2 := pow_le_pow_left₀ hQ0 hQ 2
    have h3 : y ^ 2 ≤ (1 / 4096) ^ 2 := pow_le_pow_left₀ hy0.le hy1 2
    have h5 : y ^ 2 * y ^ 2 ≤ (1 / 4096) ^ 2 * y ^ 2 := mul_le_mul_of_nonneg_right h3 hy2.le
    have e5 : (25759 / 625 * y ^ 2) ^ 2 = (25759 / 625) ^ 2 * (y ^ 2 * y ^ 2) := by ring
    rw [e5] at h1
    nlinarith
  have hX0 : 0 ≤ ((1 - q ^ 2) * (18617 / 10000) + 4195 / 10000) ^ 4 + 8295 / 10000 := by
    positivity
  have htot : ((1 - q ^ 2) * √(kEC n) + j4C n) ^ 4 + t4C n ≤
      (((1 - q ^ 2) * (18617 / 10000) + 4195 / 10000) ^ 4 + 8295 / 10000) * y ^ 2 := by
    rw [e4] at h4
    linarith
  unfold m4c
  refine (Real.sqrt_le_sqrt htot).trans (le_of_eq ?_)
  rw [Real.sqrt_mul hX0, Real.sqrt_sq hy0.le, hy]
  ring

/-- **`m4c n q ≤ 5.283/n`** for `n ≥ 4096`, `0 ≤ q ≤ 1`. -/
theorem m4c_le {n : ℕ} (hn : 4096 ≤ n) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    m4c n q ≤ 5283 / 1000 / (n : ℝ) := by
  have hx0 : (0 : ℝ) < n := by
    have : (4096 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine (m4c_le_q hn hq0 hq1).trans ?_
  refine div_le_div_of_nonneg_right ?_ hx0.le
  refine sqrt_le_of_sq (by norm_num) ?_
  have hq2 : 0 ≤ 1 - q ^ 2 := by nlinarith
  have hq3 : 1 - q ^ 2 ≤ 1 := by nlinarith [sq_nonneg q]
  have hb : (1 - q ^ 2) * (18617 / 10000) + 4195 / 10000 ≤ 22812 / 10000 := by linarith
  have h4 := pow_le_pow_left₀ (by positivity :
    (0 : ℝ) ≤ (1 - q ^ 2) * (18617 / 10000) + 4195 / 10000) hb 4
  norm_num at h4 ⊢
  linarith

end BstLean.Part149

open BstLean.Part149 in
#print axioms cheapRem_L2
open BstLean.Part149 in
#print axioms elin3_cond_L2
open BstLean.Part149 in
#print axioms cheapCos3_L2
open BstLean.Part149 in
#print axioms cheapCos_M4
open BstLean.Part149 in
#print axioms m4c_le_q
open BstLean.Part149 in
#print axioms m4c_le
