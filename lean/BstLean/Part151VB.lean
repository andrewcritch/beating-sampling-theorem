import BstLean.Part151V
import BstLean.Part151VA2

/-!
# Part 151: Lemma V (abstract form) connected to the frame of Theorem 5

Paper source: `proofs/option-n/theorem5-10-transport.tex`, Lemma V.

Notation: `b = bh (W, (A₁, A₂))`, `t_A = 2/m_A`, `γ = 2/n`, `e_b = t_A|b|²/γ` (`eBV`),
`v₁(ξ) = √t_A·|b|·λ(x)` (`v1V`: this is `⟨q(x), b̂⟩`), `v₂(ξ) = σ(x)` (`sigU`: this is `|Π_b q(x)|`),
`ξ` a standard Gaussian vector of `ℝⁿ`.

* `VOK bh W A₁ A₂ ϑ s_* M_P ξ_∥ N22 N24`: the hypotheses (V1) to (V4) of Lemma V at
  `(W, A₁, A₂)`: `e_b ≤ 1 − s_*`; a function `X ≥ 0` with `E X² ≤ (M_P γ/n)²` and the three
  Poincaré facts `Var v₁ ≤ E X`, `Var v₂ ≤ E X`, `Var φ ≤ E[X ℓ²]`; (V2); the two moments (V4).
* `DvV n ϑ s_* M_P ξ_∥ N22 N24`: the bound `(2/n)·[(√(κ_ϑ M_P) + √n·𝔯_ϑ)² + ξ_∥ + n·𝔡]`.
* **`Dv_le_of_V`**: `VOK → Dv ≤ DvV` (for `b ≠ 0`, `ϖ < 1`).
* `theorem5_frameProg_V`, `theorem5_frameA12_V`, `theorem5_frameA12_V_Cr`: the frame of
  Theorem 5 with `VOK` in the place of the hypothesis `Dv ≤ D̄_v` (and of `e_b ≤ 1`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part134 (lam res sig normSq_ne_zero)
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part139 (gamK)
open BstLean.Part141 (tauWA)
open BstLean.Part149 (thA tauOutOf)
open BstLean.Part150 (CMap gSampH bTW measurable_bTW fullProg150 fullVal)

section defs

variable {n : ℕ} (bh : CMap n) (W : MlpParam (2 * n) (mW n) n)
  (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)

/-- `v₁(ξ) = √t_A·|b|·λ(x(ξ))`: the component of `q(x)` along the centre. -/
noncomputable def v1V (ξ : Fin n → ℝ) : ℝ :=
  √(2 / (mA n : ℝ)) * √(normSq (bh (W, (A₁, A₂)))) * lamU bh W A₁ A₂ ξ

/-- The energy ratio `e_b = t_A|b|²/γ_A`. -/
noncomputable def eBV : ℝ := 2 / (mA n : ℝ) * normSq (bh (W, (A₁, A₂))) / (2 / (n : ℝ))

/-- **The hypotheses (V1) to (V4) of Lemma V** at `(W, A₁, A₂)`. -/
def VOK (ϑ sstar MP xi N22 N24 : ℝ) : Prop :=
  eBV bh W A₁ A₂ ≤ 1 - sstar ∧
  ∃ X : (Fin n → ℝ) → ℝ, Measurable X ∧ (∀ ξ, 0 ≤ X ξ) ∧
    Integrable (fun ξ => X ξ ^ 2) (stdGauss (Fin n)) ∧
    ∫ ξ, X ξ ^ 2 ∂stdGauss (Fin n) ≤ (MP * (2 / (n : ℝ)) / n) ^ 2 ∧
    ∫ ξ, (v1V bh W A₁ A₂ ξ - ∫ ζ, v1V bh W A₁ A₂ ζ ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
      ∫ ξ, X ξ ∂stdGauss (Fin n) ∧
    ∫ ξ, (sigU bh W A₁ A₂ ξ - ∫ ζ, sigU bh W A₁ A₂ ζ ∂stdGauss (Fin n)) ^ 2
        ∂stdGauss (Fin n) ≤ ∫ ξ, X ξ ∂stdGauss (Fin n) ∧
    ∫ ξ, (phiV (2 / (n : ℝ)) ϑ (v1V bh W A₁ A₂) (sigU bh W A₁ A₂) ξ -
        ∫ ζ, phiV (2 / (n : ℝ)) ϑ (v1V bh W A₁ A₂) (sigU bh W A₁ A₂) ζ ∂stdGauss (Fin n)) ^ 2
        ∂stdGauss (Fin n) ≤
      ∫ ξ, X ξ * ellSqV (2 / (n : ℝ)) ϑ (v1V bh W A₁ A₂) (sigU bh W A₁ A₂) ξ
        ∂stdGauss (Fin n) ∧
    |∫ ξ, v1V bh W A₁ A₂ ξ ∂stdGauss (Fin n) - √(2 / (n : ℝ) * eBV bh W A₁ A₂)| ≤
      √(xi * (2 / (n : ℝ)) / n) ∧
    ∫ ξ, uV (2 / (n : ℝ)) (v1V bh W A₁ A₂) (sigU bh W A₁ A₂) ξ ^ 2 ∂stdGauss (Fin n) ≤
      N22 ^ 2 ∧
    ∫ ξ, uV (2 / (n : ℝ)) (v1V bh W A₁ A₂) (sigU bh W A₁ A₂) ξ ^ 4 ∂stdGauss (Fin n) ≤ N24 ^ 4

/-- The bound of `Dv` of Lemma V:
`(2/n)·[(√(κ_ϑ M_P) + √n·𝔯_ϑ)² + ξ_∥ + n·𝔡]`. -/
noncomputable def DvV (n : ℕ) (ϑ sstar MP xi N22 N24 : ℝ) : ℝ :=
  2 / (n : ℝ) * ((√(kappaV ϑ N24 * MP) + √(n : ℝ) * rthV ϑ N22 N24) ^ 2 + xi +
    n * dfrakV n sstar MP xi N22)

lemma measurable_v1V : Measurable (v1V bh W A₁ A₂) :=
  (measurable_lamU bh W A₁ A₂).const_mul _

lemma sigU_nonneg (ξ : Fin n → ℝ) : 0 ≤ sigU bh W A₁ A₂ ξ :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma eBV_nonneg : 0 ≤ eBV bh W A₁ A₂ := by
  unfold eBV
  have := normSq_nonneg (bh (W, (A₁, A₂)))
  positivity

lemma tA_le_of_eBV (hn : 1 ≤ n) {s : ℝ} (h : eBV bh W A₁ A₂ ≤ 1 - s) :
    2 / (mA n : ℝ) * normSq (bh (W, (A₁, A₂))) ≤ 2 / (n : ℝ) * (1 - s) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hg : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  unfold eBV at h
  rw [div_le_iff₀ hg] at h
  linarith

lemma hU_coord_int (hn : 1 ≤ n) (j : Fin (mA n)) :
    Integrable (fun ξ => hU W A₁ A₂ ξ j) (stdGauss (Fin n)) := by
  refine Integrable.of_bound
    ((measurable_pi_apply j).comp (measurable_hU W A₁ A₂)).aestronglyMeasurable
    (√(frob A₂ * frob A₁)) (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs]
  refine Real.abs_le_sqrt ?_
  have h1 := hU_le W A₁ A₂ hn ξ
  have h2 : hU W A₁ A₂ ξ j ^ 2 ≤ normSq (hU W A₁ A₂ ξ) := by
    unfold normSq
    exact Finset.single_le_sum (f := fun i => hU W A₁ A₂ ξ i ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
  linarith

/-- **(V2) in terms of the centre error**: `E v₁ − √(γ e_b) = √t_A·⟨ā₂ − b, b̂⟩`, with
`ā₂ = E_ξ a₂(x)` and `b̂ = b/|b|`. -/
theorem v1V_mean (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) :
    ∫ ξ, v1V bh W A₁ A₂ ξ ∂stdGauss (Fin n) - √(2 / (n : ℝ) * eBV bh W A₁ A₂) =
      √(2 / (mA n : ℝ)) * ((∑ j, ((∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) -
        bh (W, (A₁, A₂)) j) * bh (W, (A₁, A₂)) j) / √(normSq (bh (W, (A₁, A₂))))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmA0 : (0 : ℝ) < mA n := by exact_mod_cast hmA
  have htA : (0 : ℝ) ≤ 2 / (mA n : ℝ) := by positivity
  set b := bh (W, (A₁, A₂)) with hbd
  have hns0 : 0 < normSq b := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm (normSq_ne_zero hb))
  have hsn : 0 < √(normSq b) := Real.sqrt_pos.mpr hns0
  have e1 : 2 / (n : ℝ) * eBV bh W A₁ A₂ = 2 / (mA n : ℝ) * normSq b := by
    unfold eBV
    rw [← hbd]
    field_simp
  rw [e1, Real.sqrt_mul htA]
  have hl : ∫ ξ, lamU bh W A₁ A₂ ξ ∂stdGauss (Fin n) =
      (∑ j, (∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) * b j) / normSq b := by
    unfold lamU lam
    rw [← hbd, integral_div, integral_finsetSum _ fun j _ =>
      (hU_coord_int W A₁ A₂ hn j).mul_const _]
    simp_rw [integral_mul_const]
  unfold v1V
  rw [← hbd, integral_const_mul, hl]
  have hnb : normSq b = ∑ j, b j * b j := by
    unfold normSq; exact Finset.sum_congr rfl fun j _ => pow_two _
  have e3 : ∑ j, ((∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) - b j) * b j =
      (∑ j, (∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) * b j) - normSq b := by
    rw [hnb, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e3]
  field_simp
  rw [Real.sq_sqrt hns0.le]

/-- **Lemma V for the frame**: under (V1) to (V4) at `(W, A₁, A₂)` (`VOK`), with `b ≠ 0` and
`ϖ = e_Δ/s_* < 1`: `Dv ≤ (2/n)·[(√(κ_ϑ M_P) + √n·𝔯_ϑ)² + ξ_∥ + n·𝔡]`. -/
theorem Dv_le_of_V (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) {ϑ sstar MP xi N22 N24 : ℝ}
    (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hs : 0 < sstar) (hMP : 0 ≤ MP) (hxi : 0 ≤ xi)
    (hN22 : 0 ≤ N22) (hN24 : 0 ≤ N24) (hw : eDeltaV n sstar MP xi N22 / sstar < 1)
    (hV : VOK bh W A₁ A₂ ϑ sstar MP xi N22 N24) :
    Dv bh W A₁ A₂ ≤ DvV n ϑ sstar MP xi N22 N24 := by
  obtain ⟨hV1, X, hXm, hX0, hX2i, hX2, hPl, hPs, hPφ, hV2, h2, h4⟩ := hV
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmA0 : (0 : ℝ) < mA n := by exact_mod_cast hmA
  have htA : (0 : ℝ) ≤ 2 / (mA n : ℝ) := by positivity
  set b := bh (W, (A₁, A₂)) with hbd
  have hns0 : 0 < normSq b := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm (normSq_ne_zero hb))
  set F : ℝ := frob A₂ * frob A₁ with hF
  have hF0 : 0 ≤ F := mul_nonneg (frob_nonneg _) (frob_nonneg _)
  -- boundedness
  have hH : ∀ ξ, v1V bh W A₁ A₂ ξ ^ 2 + sigU bh W A₁ A₂ ξ ^ 2 ≤
      2 / (mA n : ℝ) * F + 2 / (mA n : ℝ) * F := by
    intro ξ
    have h1 := lamU_sq_le bh W A₁ A₂ hn hb ξ
    have h2' : sigU bh W A₁ A₂ ξ ^ 2 ≤ 2 / (mA n : ℝ) * F :=
      sigX_sq_le bh W (A₁, A₂, (0 : Matrix (Fin n) (Fin (mA n)) ℝ)) hn hb ξ
    have h3 : v1V bh W A₁ A₂ ξ ^ 2 ≤ 2 / (mA n : ℝ) * F := by
      unfold v1V
      rw [mul_pow, mul_pow, Real.sq_sqrt htA, Real.sq_sqrt hns0.le]
      calc 2 / (mA n : ℝ) * normSq b * lamU bh W A₁ A₂ ξ ^ 2
          ≤ 2 / (mA n : ℝ) * normSq b * (F / normSq b) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 / (mA n : ℝ) * F := by field_simp
    linarith
  have hV := lemmaV_abs_n (stdGauss (Fin n)) (measurable_v1V bh W A₁ A₂)
    (measurable_sigU bh W A₁ A₂) (sigU_nonneg bh W A₁ A₂) hH hϑ0 hϑ1 hn0
    (eBV_nonneg bh W A₁ A₂) hs hV1 hMP hxi hN22 hN24 hXm hX0 hX2i hX2 hPl hPs hPφ hV2 h2 h4 hw
  -- the two square roots
  have e1 : 2 / (n : ℝ) * eBV bh W A₁ A₂ = 2 / (mA n : ℝ) * normSq b := by
    unfold eBV
    rw [← hbd]
    field_simp
  have r1 : √(2 / (n : ℝ) * eBV bh W A₁ A₂) = √(2 / (mA n : ℝ)) * √(normSq b) := by
    rw [e1, Real.sqrt_mul htA]
  have hle := tA_le_of_eBV bh W A₁ A₂ hn hV1
  have e2 : 2 / (n : ℝ) * (1 - eBV bh W A₁ A₂) = 2 / (n : ℝ) - 2 / (mA n : ℝ) * normSq b := by
    rw [mul_sub, e1, mul_one]
  have r2 : √(2 / (n : ℝ) * (1 - eBV bh W A₁ A₂)) = tauOutOf n b := by
    unfold tauOutOf
    rw [e2, max_eq_right]
    have : 0 ≤ 2 / (n : ℝ) * sstar := by positivity
    rw [← hbd] at hle
    linarith
  rw [r1, r2] at hV
  rw [Dv_eq bh W A₁ A₂ hn hb]
  set I : ℝ := ∫ ξ, ((√(2 / (mA n : ℝ)) * √(normSq b) * lamU bh W A₁ A₂ ξ -
      √(2 / (mA n : ℝ)) * √(normSq b)) ^ 2 +
    (sigU bh W A₁ A₂ ξ - tauOutOf n b) ^ 2) ∂stdGauss (Fin n) with hI
  have hV' : (n : ℝ) ^ 2 * I ≤ 2 * ((√(kappaV ϑ N24 * MP) + √(n : ℝ) * rthV ϑ N22 N24) ^ 2 +
      xi + n * dfrakV n sstar MP xi N22) := hV
  unfold DvV
  rw [div_mul_eq_mul_div, le_div_iff₀ hn0]
  calc (n : ℝ) * I * n = (n : ℝ) ^ 2 * I := by ring
    _ ≤ _ := hV'

end defs

/-! ## The frame with the hypotheses of Lemma V -/

section frame

variable {k n : ℕ}

lemma he_of_VOK (hn : 1 ≤ n) {bh : CMap n} {W : MlpParam (2 * n) (mW n) n}
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    {ϑ sstar MP xi N22 N24 : ℝ} (hs : 0 < sstar)
    (hV : VOK bh W A₁ A₂ ϑ sstar MP xi N22 N24) :
    2 / (mA n : ℝ) * normSq (bh (W, (A₁, A₂))) ≤ 2 / (n : ℝ) := by
  have h := tA_le_of_eBV bh W A₁ A₂ hn hV.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have : 0 ≤ 2 / (n : ℝ) * sstar := by positivity
  linarith

/-- **The frame of Theorem 5 with the hypotheses of Lemma V**, for the estimator `gSampH bh k`:
on `X12`: `b ≠ 0`, `‖C_r‖_op ≤ Mr`, and (V1) to (V4) (`VOK`). -/
theorem theorem5_frameA12_V (hn : 4096 ≤ n) (hk : 1 ≤ k) {bh : CMap n} (hbh : Measurable bh)
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    {p12 : ℝ}
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ p12)
    (hb : ∀ x ∈ X12, bh x ≠ 0) {Mr : ℝ} (hMr0 : 0 < Mr)
    (hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 → CrOK bh W A₁ A₂ Mr)
    {ϑ sstar MP xi N22 N24 : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hs : 0 < sstar) (hMP : 0 ≤ MP)
    (hxi : 0 ≤ xi) (hN22 : 0 ≤ N22) (hN24 : 0 ≤ N24)
    (hw : eDeltaV n sstar MP xi N22 / sstar < 1)
    (hV : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      VOK bh W A₁ A₂ ϑ sstar MP xi N22 N24)
    {δ uF Lc : ℝ} (hδ : 0 < δ) (huF : 0 ≤ uF) (hLc : 0 ≤ Lc) {εW θ : ℝ} (hεW0 : 0 < εW)
    (hεW : εW < 1 / 2) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    1 - (1 / (n : ℝ) + 4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n +
        (p12 + Real.exp (-Lc) + 2 * Real.exp (-uF ^ 2 / 2) + 3 * chF n δ +
          3 * Real.exp (-Lc)) +
        2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - εW) * √(n * (θ * (222757 / 1000000)) /
          (vbar n k δ ((1 + deltaC n Lc) * DvV n ϑ sstar MP xi N22 N24)
            (2 * (1 + deltaC n Lc)) (LFc n uF) Mr Lc * (n : ℝ) ^ 2 / 4)))) ≤
      (jointP k n).real {p | |gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn1 : 1 ≤ n := by omega
  have he : ∀ x ∈ X12, 2 / (mA n : ℝ) * normSq (bh x) ≤ 2 / (n : ℝ) := by
    rintro ⟨W, A₁, A₂⟩ hx
    exact he_of_VOK hn1 hs (hV W A₁ A₂ hx)
  have hDv : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      Dv bh W A₁ A₂ ≤ DvV n ϑ sstar MP xi N22 N24 := fun W A₁ A₂ hx =>
    Dv_le_of_V bh W A₁ A₂ hn1 (hb _ hx) hϑ0 hϑ1 hs hMP hxi hN22 hN24 hw (hV W A₁ A₂ hx)
  exact theorem5_frameA12 hn hk hbh h12 hp12 hb he hMr0 hCr hDv hδ huF hLc hεW0 hεW hθ0 hθ1

/-- **The frame of Theorem 5 with the hypotheses of Lemma V, for the straight-line program
`fullProg150 k n J` of Part 150**: on `X12`: `b ≠ 0`, `τ̃₀ > 0`, `‖C_r‖_op ≤ Mr`, and (V1) to
(V4) (`VOK`). -/
theorem theorem5_frameProg_V (hn : 4096 ≤ n) (hk : 1 ≤ k) {J : ℕ}
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    {p12 : ℝ}
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ p12)
    (hb : ∀ x ∈ X12, bTW J x ≠ 0) (hτ : ∀ x ∈ X12, 0 < tauWA x.1) {Mr : ℝ} (hMr0 : 0 < Mr)
    (hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 → CrOK (bTW J) W A₁ A₂ Mr)
    {ϑ sstar MP xi N22 N24 : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hs : 0 < sstar) (hMP : 0 ≤ MP)
    (hxi : 0 ≤ xi) (hN22 : 0 ≤ N22) (hN24 : 0 ≤ N24)
    (hw : eDeltaV n sstar MP xi N22 / sstar < 1)
    (hV : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      VOK (bTW J) W A₁ A₂ ϑ sstar MP xi N22 N24)
    {δ uF Lc : ℝ} (hδ : 0 < δ) (huF : 0 ≤ uF) (hLc : 0 ≤ Lc) {εW θ : ℝ} (hεW0 : 0 < εW)
    (hεW : εW < 1 / 2) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    1 - (1 / (n : ℝ) + 4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n +
        (p12 + Real.exp (-Lc) + 2 * Real.exp (-uF ^ 2 / 2) + 3 * chF n δ +
          3 * Real.exp (-Lc)) +
        2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - εW) * √(n * (θ * (222757 / 1000000)) /
          (vbar n k δ ((1 + deltaC n Lc) * DvV n ϑ sstar MP xi N22 N24)
            (2 * (1 + deltaC n Lc)) (LFc n uF) Mr Lc * (n : ℝ) ^ 2 / 4)))) ≤
      (jointP k n).real {p | |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn1 : 1 ≤ n := by omega
  have he : ∀ x ∈ X12, 2 / (mA n : ℝ) * normSq (bTW J x) ≤ 2 / (n : ℝ) := by
    rintro ⟨W, A₁, A₂⟩ hx
    exact he_of_VOK hn1 hs (hV W A₁ A₂ hx)
  have hDv : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      Dv (bTW J) W A₁ A₂ ≤ DvV n ϑ sstar MP xi N22 N24 := fun W A₁ A₂ hx =>
    Dv_le_of_V (bTW J) W A₁ A₂ hn1 (hb _ hx) hϑ0 hϑ1 hs hMP hxi hN22 hN24 hw (hV W A₁ A₂ hx)
  exact theorem5_frameProg hn hk h12 hp12 hb he hτ hMr0 hCr hDv hδ huF hLc hεW0 hεW hθ0 hθ1

/-- `theorem5_frameA12_V` with Lemma Cr: the covariance bound of `a₂` and the centre error in
the place of `‖C_r‖_op ≤ Mr`; `Mr = Mcov + Mb`. -/
theorem theorem5_frameA12_V_Cr (hn : 4096 ≤ n) (hk : 1 ≤ k) {bh : CMap n}
    (hbh : Measurable bh)
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    {p12 : ℝ}
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ p12)
    (hb : ∀ x ∈ X12, bh x ≠ 0) {Mcov Mb : ℝ} (hM0 : 0 ≤ Mcov) (hMr0 : 0 < Mcov + Mb)
    (hcov : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
        (∑ j, (hU W A₁ A₂ ξ j - ∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) * w j) ^ 2
          ∂stdGauss (Fin n) ≤ Mcov * ∑ j, w j ^ 2)
    (hcen : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      2 / (mA n : ℝ) * normSq (fun j =>
        (∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) - bh (W, (A₁, A₂)) j) ≤ Mb)
    {ϑ sstar MP xi N22 N24 : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hs : 0 < sstar) (hMP : 0 ≤ MP)
    (hxi : 0 ≤ xi) (hN22 : 0 ≤ N22) (hN24 : 0 ≤ N24)
    (hw : eDeltaV n sstar MP xi N22 / sstar < 1)
    (hV : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      VOK bh W A₁ A₂ ϑ sstar MP xi N22 N24)
    {δ uF Lc : ℝ} (hδ : 0 < δ) (huF : 0 ≤ uF) (hLc : 0 ≤ Lc) {εW θ : ℝ} (hεW0 : 0 < εW)
    (hεW : εW < 1 / 2) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    1 - (1 / (n : ℝ) + 4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n +
        (p12 + Real.exp (-Lc) + 2 * Real.exp (-uF ^ 2 / 2) + 3 * chF n δ +
          3 * Real.exp (-Lc)) +
        2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - εW) * √(n * (θ * (222757 / 1000000)) /
          (vbar n k δ ((1 + deltaC n Lc) * DvV n ϑ sstar MP xi N22 N24)
            (2 * (1 + deltaC n Lc)) (LFc n uF) (Mcov + Mb) Lc * (n : ℝ) ^ 2 / 4)))) ≤
      (jointP k n).real {p | |gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn1 : 1 ≤ n := by omega
  have hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      CrOK bh W A₁ A₂ (Mcov + Mb) := fun W A₁ A₂ hx =>
    CrOK_of_cov hn1 (hb _ hx) hM0 (hcov W A₁ A₂ hx) (hcen W A₁ A₂ hx)
  exact theorem5_frameA12_V hn hk hbh h12 hp12 hb hMr0 hCr hϑ0 hϑ1 hs hMP hxi hN22 hN24 hw hV
    hδ huF hLc hεW0 hεW hθ0 hθ1

end frame

end BstLean.Part151
