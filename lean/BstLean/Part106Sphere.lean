import BstLean.Part106Thm0
import BstLean.Part106Gauss
import BstLean.Part106Cost

/-!
# Part 106: the sphere version of the World polynomial — the coupling and the first tools

Paper sources: `delegations/answers/oaW2-opus-prover.md` Section 6, `oaW2-cx-disprover.md`
Section 4, `oaW6c-cx.md` Section 4 (the Gaussian coupling `W = G/‖G‖`).

`bwSphere` is by definition the distribution of `W = bwOfCoord (ξ/|ξ|)`, `ξ` standard Gaussian;
`G = bwOfCoord ξ` has the Gaussian version with `σ = 1`; `W = G/S`, `S = |ξ|`.
* Scale invariance (`muW_smul`, `nuW_smul`, `gVal_smul`): `μ_W = μ_G`, and the stand-in of `G` at
  the level `τ_P = √(d−1)` is the stand-in of `W` at the level `a = τ_P/S` (the ideal level; it
  is random and the program does not know it).
* `thm1_prob_full`: Theorem 1 in the Chebyshev form with all the coefficients Gaussian.
* `sample_cheb_mixed`: Chebyshev for the sample mean with random low-degree coefficients.
* `nu_dom`: for `a ≤ b`, `ν(a) ≤ (b/a)ⁿ ν(b)` (a pointwise bound of the density ratio of two
  centred Gaussians, `gauss_scale_dom`).
* `dom_var`, `dom_mean`: if `P ≤ K·Q` then `Var_P φ ≤ K Var_Q φ` and
  `(E_P φ − E_Q φ)² ≤ K(K−1) Var_Q φ`. No total variation, relative entropy or Pinsker
  inequality is used.
* `sphere_prob`: the probability step in the Gaussian coordinates `ξ`.
* `sphere_transfer`: from the Gaussian coordinates to `bwSphere`.

The theorem for the sphere version of `W` is in `Part106Exact`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part106

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

variable {N n d : ℕ}

/-! ## Scale invariance -/

lemma bwOfCoord_smul (s : ℝ) (ξ : CoefIdx N n d → ℝ) :
    bwOfCoord (s • ξ) = s • bwOfCoord ξ := by
  funext i
  simp [bwOfCoord, mul_div_assoc]

lemma bwEval_smul (s : ℝ) (b : CoefIdx N n d → ℝ) (x : Fin N → ℝ) :
    bwEval (s • b) x = s • bwEval b x := by
  funext a
  simp [bwEval, Finset.mul_sum, mul_assoc]

lemma mixW_smul_zero (s : ℝ) (b : CoefIdx N n d → ℝ) : mixW (s • b) 0 = s • mixW b 0 := by
  funext i
  simp only [mixW, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  split_ifs <;> simp

lemma sphProj_smul {s : ℝ} (hs : 0 < s) (y : Fin n → ℝ) : sphProj (s • y) = sphProj y := by
  unfold sphProj
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le, smul_smul]
  congr 1
  by_cases h : Real.sqrt (∑ i, y i ^ 2) = 0
  · simp [h]
  · field_simp

lemma muW_smul {s : ℝ} (hs : 0 < s) (W : CoefIdx N n d → ℝ) : muW (s • W) = muW W := by
  unfold muW
  congr 1
  funext u
  rw [bwEval_smul, sphProj_smul hs]

lemma standIn_smul {s : ℝ} (hs : 0 < s) (b0 : CoefIdx N n d → ℝ) (τ : ℝ)
    (p : (Fin N → ℝ) × (Fin n → ℝ)) : standIn (s • b0) (s * τ) p = standIn b0 τ p := by
  unfold standIn
  rw [mixW_smul_zero, bwEval_smul, mul_smul, ← smul_add, sphProj_smul hs]

lemma nuW_smul {s : ℝ} (hs : 0 < s) (b0 : CoefIdx N n d → ℝ) (τ : ℝ) :
    nuW (s • b0) (s * τ) = nuW b0 τ := by
  rw [nuW_eq_map, nuW_eq_map]
  congr 1
  funext p
  exact standIn_smul hs b0 τ p

lemma gVal_smul {s : ℝ} (hs : 0 < s) (b0 : CoefIdx N n d → ℝ) (τ : ℝ) (φ : (Fin n → ℝ) → ℝ)
    {k : ℕ} (ω : Fin k → (Fin N → ℝ) × (Fin n → ℝ)) :
    gVal (s • b0) (s * τ) φ ω = gVal b0 τ φ ω := by
  simp only [gVal, standIn_smul hs]

/-! ## Domination of the stand-in at a lower noise level -/

/-- **Domination**: for `0 < a ≤ b` and `h ≥ 0` bounded measurable,
`E_{ν(a)} h ≤ (b/a)ⁿ E_{ν(b)} h` (`ν(τ)` the stand-in with noise level `τ`). -/
theorem nu_dom (hN : 1 ≤ N) (b0 : CoefIdx N n d → ℝ) {h : (Fin n → ℝ) → ℝ} (hh : BM h)
    (h0 : ∀ x, 0 ≤ h x) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x, h x ∂nuW b0 a ≤ (b / a) ^ n * ∫ x, h x ∂nuW b0 b := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  rw [nu_integral hN b0 a hh, nu_integral hN b0 b hh, ← integral_const_mul]
  refine integral_mono ((bm_mNoise a (fF hN b0 h) (hf_F hN b0 hh)).integrable _)
    (((BM.const _).mul (bm_mNoise b (fF hN b0 h) (hf_F hN b0 hh))).integrable _) ?_
  intro u
  exact gauss_scale_dom (bm_f_left (fF hN b0 h) (hf_F hN b0 hh) u) (fun z => h0 _) ha hab

section dom

set_option linter.unusedSectionVars false

variable {α : Type*} [MeasurableSpace α] (P Q : Measure α) [IsProbabilityMeasure P]
  [IsProbabilityMeasure Q]

lemma int_sq_shift {φ : α → ℝ} (hφ : BM φ) (c : ℝ) :
    ∫ x, (φ x - c) ^ 2 ∂P = Var[φ; P] + (∫ x, φ x ∂P - c) ^ 2 := by
  rw [variance_eq_integral hφ.meas.aemeasurable]
  set m := ∫ x, φ x ∂P with hm
  have e : ∀ x, (φ x - c) ^ 2 = (φ x - m) ^ 2 + (2 * (m - c)) * (φ x - m) + (m - c) ^ 2 := by
    intro x; ring
  simp_rw [e]
  have i1 : Integrable (fun x => (φ x - m) ^ 2) P := ((hφ.sub (BM.const m)).sq).integrable P
  have i2 : Integrable (fun x => (2 * (m - c)) * (φ x - m)) P :=
    ((BM.const _).mul (hφ.sub (BM.const m))).integrable P
  have h1 : ∫ x, ((φ x - m) ^ 2 + (2 * (m - c)) * (φ x - m) + (m - c) ^ 2) ∂P =
      ∫ x, ((φ x - m) ^ 2 + (2 * (m - c)) * (φ x - m)) ∂P + ∫ _x, (m - c) ^ 2 ∂P :=
    integral_add (i1.add i2) (integrable_const _)
  have h2 : ∫ x, ((φ x - m) ^ 2 + (2 * (m - c)) * (φ x - m)) ∂P =
      ∫ x, (φ x - m) ^ 2 ∂P + ∫ x, (2 * (m - c)) * (φ x - m) ∂P := integral_add i1 i2
  have h3 : ∫ x, (φ x - m) ∂P = 0 := by
    rw [integral_sub (hφ.integrable P) (integrable_const _)]
    simp [← hm]
  rw [h1, h2, integral_const_mul, h3]
  simp

variable (K : ℝ)
  (hdom : ∀ h : α → ℝ, BM h → (∀ x, 0 ≤ h x) → ∫ x, h x ∂P ≤ K * ∫ x, h x ∂Q)

include hdom in
lemma dom_one_le : 1 ≤ K := by
  have := hdom (fun _ => 1) (BM.const 1) (fun _ => zero_le_one)
  simpa using this

include hdom in
/-- If `P ≤ K·Q` then `Var_P φ ≤ K Var_Q φ`. -/
lemma dom_var {φ : α → ℝ} (hφ : BM φ) : Var[φ; P] ≤ K * Var[φ; Q] := by
  have h1 := int_sq_shift P hφ (∫ x, φ x ∂Q)
  have h2 := hdom (fun x => (φ x - ∫ y, φ y ∂Q) ^ 2) ((hφ.sub (BM.const _)).sq)
    (fun x => sq_nonneg _)
  rw [variance_eq_integral (μ := Q) hφ.meas.aemeasurable]
  nlinarith [sq_nonneg (∫ x, φ x ∂P - ∫ x, φ x ∂Q)]

include hdom in
/-- If `P ≤ K·Q` then `(E_P φ − E_Q φ)² ≤ K (K−1) Var_Q φ`. -/
lemma dom_mean {φ : α → ℝ} (hφ : BM φ) :
    (∫ x, φ x ∂P - ∫ x, φ x ∂Q) ^ 2 ≤ K * (K - 1) * Var[φ; Q] := by
  have hK := dom_one_le P Q K hdom
  set m := ∫ x, φ x ∂P - ∫ x, φ x ∂Q with hm
  set V := Var[φ; Q] with hV
  have hV0 : 0 ≤ V := variance_nonneg _ _
  have key : ∀ t : ℝ, (m + t) ^ 2 ≤ K * (V + t ^ 2) := by
    intro t
    have h1 := int_sq_shift P hφ (∫ x, φ x ∂Q - t)
    have h2 := int_sq_shift Q hφ (∫ x, φ x ∂Q - t)
    have h3 := hdom (fun x => (φ x - (∫ y, φ y ∂Q - t)) ^ 2) ((hφ.sub (BM.const _)).sq)
      (fun x => sq_nonneg _)
    rw [h1, h2] at h3
    have hP0 : 0 ≤ Var[φ; P] := variance_nonneg _ _
    have e1 : ∫ x, φ x ∂P - (∫ x, φ x ∂Q - t) = m + t := by rw [hm]; ring
    have e2 : ∫ x, φ x ∂Q - (∫ x, φ x ∂Q - t) = t := by ring
    rw [e1, e2] at h3
    linarith
  rcases hK.eq_or_lt with h1 | h1
  · -- `K = 1`: `m = 0`
    have hm0 : m = 0 := by
      by_contra hne
      have := key ((V + 1 - m ^ 2) / (2 * m))
      rw [← h1] at this
      have e : (m + (V + 1 - m ^ 2) / (2 * m)) ^ 2 =
          m ^ 2 + (V + 1 - m ^ 2) + ((V + 1 - m ^ 2) / (2 * m)) ^ 2 := by
        field_simp
        ring
      rw [e] at this
      linarith
    rw [hm0, ← h1]
    simp
  · set c := K - 1 with hc
    have hc0 : 0 < c := by linarith
    set s := m / c with hs
    have hms : m = s * c := by rw [hs]; field_simp
    have hk := key s
    have hKc : K = c + 1 := by rw [hc]; ring
    rw [hms, hKc] at hk
    have h5 : (c + 1) * (s ^ 2 * c) ≤ (c + 1) * V := by nlinarith [hk]
    have h6 : s ^ 2 * c ≤ V := le_of_mul_le_mul_left h5 (by linarith)
    have h7 : m ^ 2 ≤ c * V := by
      rw [hms]
      calc (s * c) ^ 2 = c * (s ^ 2 * c) := by ring
        _ ≤ c * V := mul_le_mul_of_nonneg_left h6 hc0.le
    calc m ^ 2 ≤ c * V := h7
      _ ≤ K * c * V := by
        have : 0 ≤ c * V := mul_nonneg hc0.le hV0
        nlinarith

end dom

/-! ## Theorem 1, Chebyshev form, with all coefficients random -/

/-- **Theorem 1, Chebyshev form, all coefficients Gaussian**: for `W` with the Gaussian version of
the Bombieri–Weyl distribution, the event `λ_0 Var_{ν_W} φ < δ (E_{μ_W} φ − E_{ν_W} φ)²` has
probability at most `δ`. -/
theorem thm1_prob_full (hN : 1 ≤ N) (hd : 2 ≤ d) (σ : ℝ) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ)
    {δ : ℝ} (hδ : 0 < δ) :
    (bwGauss N n d σ).real {W | lam0 N d * Var[φ; nuW W (tauOf d σ)] <
      δ * (∫ x, φ x ∂muW W - ∫ x, φ x ∂nuW W (tauOf d σ)) ^ 2} ≤ δ := by
  set G := bwGauss N n d σ with hG
  set E : Set (CoefIdx N n d → ℝ) := {W | lam0 N d * Var[φ; nuW W (tauOf d σ)] <
      δ * (∫ x, φ x ∂muW W - ∫ x, φ x ∂nuW W (tauOf d σ)) ^ 2} with hE
  have hEm : MeasurableSet E :=
    measurableSet_lt (measurable_const.mul (bm_nuVar hN hφ _).meas)
      (measurable_const.mul ((bm_muInt hN hφ).sub (bm_nuInt hN hφ _)).sq.meas)
  have h1 : G E = (G.prod G) ((fun p : (CoefIdx N n d → ℝ) × (CoefIdx N n d → ℝ) =>
      mixW p.1 p.2) ⁻¹' E) := by
    rw [← Measure.map_apply measurable_mixW2 hEm, hG, bwGauss_mix σ]
  have h2 : G E ≤ ENNReal.ofReal δ := by
    rw [h1, Measure.prod_apply (measurable_mixW2 hEm)]
    calc ∫⁻ b0, G (Prod.mk b0 ⁻¹' ((fun p : (CoefIdx N n d → ℝ) × (CoefIdx N n d → ℝ) =>
          mixW p.1 p.2) ⁻¹' E)) ∂G
        ≤ ∫⁻ _b0, ENNReal.ofReal δ ∂G := by
          refine lintegral_mono fun b0 => ?_
          have hs : Prod.mk b0 ⁻¹' ((fun p : (CoefIdx N n d → ℝ) × (CoefIdx N n d → ℝ) =>
              mixW p.1 p.2) ⁻¹' E) = {c | lam0 N d * Var[φ; nuW b0 (tauOf d σ)] <
                δ * (∫ x, φ x ∂muW (mixW b0 c) - ∫ x, φ x ∂nuW b0 (tauOf d σ)) ^ 2} := by
            ext c
            simp only [hE, Set.mem_preimage, Set.mem_setOf_eq, nuW_mix]
          rw [hs, ← ofReal_measureReal]
          exact ENNReal.ofReal_le_ofReal (thm1_prob hN hd σ b0 hφ hδ)
      _ = ENNReal.ofReal δ := by simp
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hδ.le h2

/-! ## The sample mean, with the low-degree coefficients random -/

lemma measurable_gVal_joint {Ξ : Type*} [MeasurableSpace Ξ] {Wf : Ξ → CoefIdx N n d → ℝ}
    (hW : Measurable Wf) (τ : ℝ) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) (k : ℕ) :
    Measurable (fun p : Ξ × (Fin k → (Fin N → ℝ) × (Fin n → ℝ)) => gVal (Wf p.1) τ φ p.2) := by
  unfold gVal
  refine (Finset.measurable_sum _ fun i _ => ?_).div_const _
  have h := (measurable_nuMap2 (N := N) (n := n) (d := d) τ).comp
    (((measurable_pi_apply i).comp
      (measurable_snd : Measurable (fun p : Ξ × (Fin k → (Fin N → ℝ) × (Fin n → ℝ)) => p.2))).prodMk
      (hW.comp measurable_fst))
  exact hφ.meas.comp h

/-- **Chebyshev for the mean of `k` samples, with random low-degree coefficients** `Wf ξ`. -/
theorem sample_cheb_mixed {Ξ : Type*} [MeasurableSpace Ξ] (γ : Measure Ξ) [IsProbabilityMeasure γ]
    {Wf : Ξ → CoefIdx N n d → ℝ} (hW : Measurable Wf) (hN : 1 ≤ N) (τ : ℝ)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) {k : ℕ} (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    (γ.prod (Measure.pi fun _ : Fin k => (uniformSphere N).prod (stdGauss (Fin n)))).real
      {p | Var[φ; nuW (Wf p.1) τ] <
        k * δ * (gVal (Wf p.1) τ φ p.2 - ∫ x, φ x ∂nuW (Wf p.1) τ) ^ 2} ≤ δ := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  set π : Measure (Fin k → (Fin N → ℝ) × (Fin n → ℝ)) :=
    Measure.pi fun _ : Fin k => (uniformSphere N).prod (stdGauss (Fin n)) with hπ
  set E : Set (Ξ × (Fin k → (Fin N → ℝ) × (Fin n → ℝ))) := {p | Var[φ; nuW (Wf p.1) τ] <
        k * δ * (gVal (Wf p.1) τ φ p.2 - ∫ x, φ x ∂nuW (Wf p.1) τ) ^ 2} with hE
  have hEm : MeasurableSet E := by
    refine measurableSet_lt (((bm_nuVar hN hφ τ).meas.comp hW).comp measurable_fst) ?_
    exact measurable_const.mul (((measurable_gVal_joint hW τ hφ k).sub
      (((bm_nuInt hN hφ τ).meas.comp hW).comp measurable_fst)).pow_const 2)
  have h2 : (γ.prod π) E ≤ ENNReal.ofReal δ := by
    rw [Measure.prod_apply hEm]
    calc ∫⁻ ξ, π (Prod.mk ξ ⁻¹' E) ∂γ ≤ ∫⁻ _ξ, ENNReal.ofReal δ ∂γ := by
          refine lintegral_mono fun ξ => ?_
          rw [← ofReal_measureReal]
          exact ENNReal.ofReal_le_ofReal (sample_cheb hN (Wf ξ) τ hφ hk hδ)
      _ = ENNReal.ofReal δ := by simp
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hδ.le h2

/-! ## The deterministic step -/

lemma tri3 {x y z V c₁ c₂ c₃ : ℝ} (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂) (h3 : 0 ≤ c₃)
    (hx : x ^ 2 ≤ c₁ ^ 2 * V) (hy : y ^ 2 ≤ c₂ ^ 2 * V) (hz : z ^ 2 ≤ c₃ ^ 2 * V) :
    |x + y + z| ≤ (c₁ + c₂ + c₃) * Real.sqrt V := by
  have hsq : ∀ {x c : ℝ}, 0 ≤ c → x ^ 2 ≤ c ^ 2 * V → |x| ≤ c * Real.sqrt V := by
    intro x c hc hx
    have := Real.abs_le_sqrt hx
    rwa [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc] at this
  calc |x + y + z| ≤ |x| + |y| + |z| := abs_add_three x y z
    _ ≤ c₁ * Real.sqrt V + c₂ * Real.sqrt V + c₃ * Real.sqrt V :=
        add_le_add (add_le_add (hsq h1 hx) (hsq h2 hy)) (hsq h3 hz)
    _ = (c₁ + c₂ + c₃) * Real.sqrt V := by ring

lemma tauOf_one_pos (hd : 2 ≤ d) : 0 < tauOf d 1 := by
  unfold tauOf
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  rw [mul_one]
  exact Real.sqrt_pos.mpr (by linarith)

/-! ## The probability step -/

/-- **The probability step**: for `ξ` standard Gaussian (the coordinates of the coefficients) and
`k` independent blocks, except with probability `δ₁ + δ₃ + 2D/t²`: `||ξ|² − D| < t`, the bound of
Theorem 1 holds for `G = bwOfCoord ξ` at the level `tauOf d 1`, and the bound of the sample mean
holds for `W = bwOfCoord (ξ/|ξ|)` at the level `τ`. -/
theorem sphere_prob (hN : 1 ≤ N) (hd : 2 ≤ d) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) {k : ℕ}
    (hk : 1 ≤ k) {δ₁ δ₃ t : ℝ} (h1 : 0 < δ₁) (h3 : 0 < δ₃) (ht : 0 < t) (τ : ℝ) :
    1 - (δ₁ + δ₃ + 2 * (Fintype.card (CoefIdx N n d) : ℝ) / t ^ 2) ≤
      ((stdGauss (CoefIdx N n d)).prod
        (Measure.pi fun _ : Fin k => (uniformSphere N).prod (stdGauss (Fin n)))).real
        {p | |∑ i, p.1 i ^ 2 - (Fintype.card (CoefIdx N n d) : ℝ)| < t ∧
          δ₁ * (∫ x, φ x ∂muW (bwOfCoord p.1) - ∫ x, φ x ∂nuW (bwOfCoord p.1) (tauOf d 1)) ^ 2 ≤
            lam0 N d * Var[φ; nuW (bwOfCoord p.1) (tauOf d 1)] ∧
          k * δ₃ * (gVal (bwOfCoord ((1 / Real.sqrt (∑ i, p.1 i ^ 2)) • p.1)) τ φ p.2 -
              ∫ x, φ x ∂nuW (bwOfCoord ((1 / Real.sqrt (∑ i, p.1 i ^ 2)) • p.1)) τ) ^ 2 ≤
            Var[φ; nuW (bwOfCoord ((1 / Real.sqrt (∑ i, p.1 i ^ 2)) • p.1)) τ]} := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  set γ := stdGauss (CoefIdx N n d) with hγ
  set π : Measure (Fin k → (Fin N → ℝ) × (Fin n → ℝ)) :=
    Measure.pi fun _ : Fin k => (uniformSphere N).prod (stdGauss (Fin n)) with hπ
  set D : ℝ := (Fintype.card (CoefIdx N n d) : ℝ) with hD
  set E4 : Set (CoefIdx N n d → ℝ) := {ξ | t ≤ |∑ i, ξ i ^ 2 - D|} with hE4
  set E1 : Set (CoefIdx N n d → ℝ) := {ξ | lam0 N d * Var[φ; nuW (bwOfCoord ξ) (tauOf d 1)] <
    δ₁ * (∫ x, φ x ∂muW (bwOfCoord ξ) - ∫ x, φ x ∂nuW (bwOfCoord ξ) (tauOf d 1)) ^ 2} with hE1
  set E3 : Set ((CoefIdx N n d → ℝ) × (Fin k → (Fin N → ℝ) × (Fin n → ℝ))) :=
    {p | Var[φ; nuW (bwOfCoord ((1 / Real.sqrt (∑ i, p.1 i ^ 2)) • p.1)) τ] <
      k * δ₃ * (gVal (bwOfCoord ((1 / Real.sqrt (∑ i, p.1 i ^ 2)) • p.1)) τ φ p.2 -
        ∫ x, φ x ∂nuW (bwOfCoord ((1 / Real.sqrt (∑ i, p.1 i ^ 2)) • p.1)) τ) ^ 2} with hE3
  have hP4 : γ.real E4 ≤ 2 * D / t ^ 2 := chiSq_cheb (CoefIdx N n d) ht
  have hP1 : γ.real E1 ≤ δ₁ := by
    have hfull := thm1_prob_full (N := N) (n := n) (d := d) hN hd 1 hφ h1
    have hsub : E1 ⊆ (fun ξ : CoefIdx N n d → ℝ => bwOfCoord ((1 : ℝ) • ξ)) ⁻¹'
        {W | lam0 N d * Var[φ; nuW W (tauOf d 1)] <
          δ₁ * (∫ x, φ x ∂muW W - ∫ x, φ x ∂nuW W (tauOf d 1)) ^ 2} := by
      intro ξ hξ
      simp only [Set.mem_preimage, Set.mem_setOf_eq, one_smul]
      exact hξ
    have hle := Measure.le_map_apply (μ := γ) (measurable_bwGaussMap (k := N) (q := n) (d := d)
      (1 : ℝ)).aemeasurable {W | lam0 N d * Var[φ; nuW W (tauOf d 1)] <
          δ₁ * (∫ x, φ x ∂muW W - ∫ x, φ x ∂nuW W (tauOf d 1)) ^ 2}
    have h2 : γ.real E1 ≤ (bwGauss N n d 1).real {W | lam0 N d * Var[φ; nuW W (tauOf d 1)] <
          δ₁ * (∫ x, φ x ∂muW W - ∫ x, φ x ∂nuW W (tauOf d 1)) ^ 2} := by
      rw [measureReal_def, measureReal_def]
      exact ENNReal.toReal_mono (measure_ne_top _ _) ((measure_mono hsub).trans hle)
    exact h2.trans hfull
  have hP3 : (γ.prod π).real E3 ≤ δ₃ :=
    sample_cheb_mixed γ measurable_bwSphereMap hN τ hφ hk h3
  set Good : Set ((CoefIdx N n d → ℝ) × (Fin k → (Fin N → ℝ) × (Fin n → ℝ))) :=
    {p | |∑ i, p.1 i ^ 2 - D| < t ∧
          δ₁ * (∫ x, φ x ∂muW (bwOfCoord p.1) - ∫ x, φ x ∂nuW (bwOfCoord p.1) (tauOf d 1)) ^ 2 ≤
            lam0 N d * Var[φ; nuW (bwOfCoord p.1) (tauOf d 1)] ∧
          k * δ₃ * (gVal (bwOfCoord ((1 / Real.sqrt (∑ i, p.1 i ^ 2)) • p.1)) τ φ p.2 -
              ∫ x, φ x ∂nuW (bwOfCoord ((1 / Real.sqrt (∑ i, p.1 i ^ 2)) • p.1)) τ) ^ 2 ≤
            Var[φ; nuW (bwOfCoord ((1 / Real.sqrt (∑ i, p.1 i ^ 2)) • p.1)) τ]} with hGood
  have hcov : (Set.univ : Set ((CoefIdx N n d → ℝ) × (Fin k → (Fin N → ℝ) × (Fin n → ℝ)))) ⊆
      Good ∪ ((E4 ×ˢ Set.univ ∪ E1 ×ˢ Set.univ) ∪ E3) := by
    intro p _
    by_cases hp : p ∈ Good
    · exact Or.inl hp
    · right
      simp only [hGood, Set.mem_setOf_eq, not_and_or, not_le, not_lt] at hp
      rcases hp with hp | hp | hp
      · exact Or.inl (Or.inl ⟨hp, Set.mem_univ _⟩)
      · exact Or.inl (Or.inr ⟨hp, Set.mem_univ _⟩)
      · exact Or.inr hp
  have hu : (γ.prod π).real Set.univ ≤
      (γ.prod π).real Good + (((γ.prod π).real (E4 ×ˢ Set.univ) +
        (γ.prod π).real (E1 ×ˢ Set.univ)) + (γ.prod π).real E3) :=
    (measureReal_mono hcov).trans ((measureReal_union_le _ _).trans
      (add_le_add le_rfl ((measureReal_union_le _ _).trans
        (add_le_add (measureReal_union_le _ _) le_rfl))))
  have e4 : (γ.prod π).real (E4 ×ˢ Set.univ) = γ.real E4 := by
    simp [measureReal_def, Measure.prod_prod]
  have e1 : (γ.prod π).real (E1 ×ˢ Set.univ) = γ.real E1 := by
    simp [measureReal_def, Measure.prod_prod]
  rw [e4, e1] at hu
  have h1' : (γ.prod π).real Set.univ = 1 := by simp
  linarith

/-- **The transfer to the sphere version**: `bwSphere` is the distribution of
`bwOfCoord (ξ/|ξ|)`. -/
lemma sphere_transfer (hN : 1 ≤ N) {k : ℕ}
    (T : Set ((CoefIdx N n d → ℝ) × (Fin k → (Fin N → ℝ) × (Fin n → ℝ)))) :
    ((stdGauss (CoefIdx N n d)).prod
      (Measure.pi fun _ : Fin k => (uniformSphere N).prod (stdGauss (Fin n)))).real
        {p | ((bwOfCoord ((1 / Real.sqrt (∑ i, p.1 i ^ 2)) • p.1), p.2) :
          (CoefIdx N n d → ℝ) × (Fin k → (Fin N → ℝ) × (Fin n → ℝ))) ∈ T} ≤
      ((bwSphere N n d).prod
        (Measure.pi fun _ : Fin k => (uniformSphere N).prod (stdGauss (Fin n)))).real T := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  set γ := stdGauss (CoefIdx N n d) with hγ
  set π : Measure (Fin k → (Fin N → ℝ) × (Fin n → ℝ)) :=
    Measure.pi fun _ : Fin k => (uniformSphere N).prod (stdGauss (Fin n)) with hπ
  have hWm : Measurable (fun ξ : CoefIdx N n d → ℝ =>
      bwOfCoord ((1 / Real.sqrt (∑ i, ξ i ^ 2)) • ξ)) := measurable_bwSphereMap
  have e : (bwSphere N n d).prod π = (γ.prod π).map
      (Prod.map (fun ξ : CoefIdx N n d → ℝ => bwOfCoord ((1 / Real.sqrt (∑ i, ξ i ^ 2)) • ξ))
        id) := by
    have h := Measure.map_prod_map γ π hWm measurable_id
    rw [Measure.map_id] at h
    exact h
  have hle := Measure.le_map_apply (μ := γ.prod π) (hWm.prodMap measurable_id).aemeasurable T
  rw [← e] at hle
  rw [measureReal_def, measureReal_def]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hle

/-! ## Numeric steps -/

/-- Bernoulli: `(1 + y)ⁿ ≤ 1/(1 − n y)` for `y ≥ 0`, `n y < 1`. -/
lemma one_add_pow_le {y : ℝ} (hy : 0 ≤ y) (n : ℕ) (hny : (n : ℝ) * y < 1) :
    (1 + y) ^ n ≤ 1 / (1 - n * y) := by
  have h1y : 0 < 1 + y := by linarith
  have hfr : y / (1 + y) ≤ y := div_le_self hy (by linarith)
  have hfr0 : 0 ≤ y / (1 + y) := div_nonneg hy h1y.le
  have hfr1 : y / (1 + y) ≤ 1 := (div_le_one h1y).mpr (by linarith)
  have hb := one_add_mul_le_pow (a := -(y / (1 + y))) (by linarith) n
  have e : 1 + -(y / (1 + y)) = (1 + y)⁻¹ := by field_simp; ring
  rw [e, inv_pow] at hb
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : 1 - n * y ≤ 1 + n * -(y / (1 + y)) := by nlinarith
  have hpos : 0 < 1 - n * y := by linarith
  have h2 : 1 - n * y ≤ ((1 + y) ^ n)⁻¹ := h1.trans hb
  rw [one_div]
  exact (le_inv_comm₀ hpos (pow_pos h1y n)).mp h2

/-- `λ_0` at degree `8` is below the bound used at degree `6`. -/
lemma lam0_eight_le {n : ℕ} (hn : 1 ≤ n) :
    lam0 (2 * n) 8 ≤ 1 / (10 * (n : ℝ)) * (1 + 2 / (n : ℝ)) := by
  refine (lam0_bound8 n hn).trans ?_
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0 : ℝ) < n := by linarith
  have h1n : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one h0]; exact hn'
  have h1n0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have hv : (1 + 3 / (n : ℝ)) / 14 ≤ (1 + 2 / (n : ℝ)) / 10 := by
    have e3 : 3 / (n : ℝ) = 3 * (1 / n) := by ring
    have e2 : 2 / (n : ℝ) = 2 * (1 / n) := by ring
    rw [e3, e2]
    linarith
  calc 1 / (14 * (n : ℝ)) * (1 + 3 / (n : ℝ)) = 1 / (n : ℝ) * ((1 + 3 / (n : ℝ)) / 14) := by ring
    _ ≤ 1 / (n : ℝ) * ((1 + 2 / (n : ℝ)) / 10) := mul_le_mul_of_nonneg_left hv h1n0
    _ = 1 / (10 * (n : ℝ)) * (1 + 2 / (n : ℝ)) := by ring

end BstLean.Part106

#print axioms BstLean.Part106.nu_dom
#print axioms BstLean.Part106.dom_var
#print axioms BstLean.Part106.dom_mean
#print axioms BstLean.Part106.thm1_prob_full
#print axioms BstLean.Part106.sample_cheb_mixed
#print axioms BstLean.Part106.sphere_prob
#print axioms BstLean.Part106.sphere_transfer
