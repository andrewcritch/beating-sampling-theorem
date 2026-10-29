import BstLean.Part106Sphere
import BstLean.Part106Gauss2

/-!
# Part 106: Theorem 0 for the sphere version of `W`, with the paper noise level `τ² = (d−1)/D`

`W` has the Bombieri–Weyl sphere distribution (`bwSphere`). The program uses the FIXED noise
level of the paper, `tauPaper`, `τ_0² = (d−1)/D` (`5/D` at `d = 6`), `D` the number of
coefficients of `W`. The spread is that of the stand-in at that level.

Route (the tools are in `Part106Sphere`). In the Gaussian coordinates `ξ`, the stand-in that
Theorem 1 controls has the ideal level `a = τ_P/|ξ|`; the program uses the level `b = τ_0`.
* Where `a ≤ b`: `ν(a) ≤ (b/a)ⁿ ν(b)` (`nu_dom`).
* Where `a > b` (this file):
  * `gauss_shift_dom` (`Part106Gauss2`): a narrower Gaussian with another centre is dominated by
    a wider Gaussian, `N(μ₁, a²I) ≤ (b/a)ⁿ exp(|μ₁−μ₂|²/(2(b²−a²))) N(μ₂, b²I)` for `a < b`.
  * `proj_dom_up`: the direction `y/|y|` does not change if `y` is multiplied by `t² = (b/a)²`;
    so the direction of `m + a g` is the direction of `t²m + (tb) g`, a Gaussian that is narrower
    than `N(m, b²I)`. Hence, for `a > b` and `h ≥ 0`,
    `E h(π(m + a g)) ≤ (a/b)ⁿ exp((1 − b²/a²)|m|²/(2b²)) E h(π(m + b g))`.
  * `nu_dom_up`: the same for the stand-in, with `|m|² = |W_0 + W_1 u|² ≤ M` for unit `u`.
  * `low_bound`: `|W_0 + W_1 u|² ≤ 2 (Σ_a W_{0,a}² + Σ_{a,j} W_{1,a,j}²)`; in the Gaussian
    coordinates the sum is `χ_low/|ξ|²`, `χ_low` a chi-square variable with `n(N+1)` degrees of
    freedom (`chiSq_cheb_sub`).
* So in both cases `ν(a) ≤ K·ν(b)` with `K ≤ 1 + 8/10000`, except with probability at most
  `5/10000` over `ξ` (`| |ξ|² − D | < D/(1024n²)` and `χ_low < 2n(2n+1)`). Then `dom_var`,
  `dom_mean` and the triangle inequality (`point_dom`, `sphere_point_exact`).
This comparison is a new argument; the paper route (total variation by relative entropy and the
Pinsker inequality) is not used.

Headlines: `thm0_sphere_dA3`, `thm0_sphere_dA4` (every `n ≥ 4096`, every `k ≥ 1200`).

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part106

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

variable {N n d : ℕ}

/-! ## The coefficients of degree `0` and `1` -/

/-- The index of a coefficient of degree `0` (`none`) or `1` (`some j`: the variable `x_j`). -/
def lowIdx (N n d : ℕ) (hd : 1 ≤ d) (p : Fin n × Option (Fin N)) : CoefIdx N n d :=
  (p.1, p.2.elim (mono0 N d) (mono1 N d hd))

lemma lowIdx_injective (hd : 1 ≤ d) : Function.Injective (lowIdx N n d hd) := by
  rintro ⟨a, o⟩ ⟨a', o'⟩ h
  simp only [lowIdx, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  subst h1
  congr 1
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some j =>
      have := congrArg (fun m : MonoIdx N d => m.1.val) h2
      simp [mono0, mono1] at this
  | some i =>
    cases o' with
    | none =>
      have := congrArg (fun m : MonoIdx N d => m.1.val) h2
      simp [mono0, mono1] at this
    | some j =>
      have := congrArg (fun m : MonoIdx N d => m.2.val) h2
      simp only [Option.elim, mono1] at this
      have h3 : i = j := by simpa using this
      rw [h3]

lemma bwWeight_mono0 : bwWeight (mono0 N d) = 1 := by
  simp [bwWeight, mono0, MonoIdx.deg]

lemma bwWeight_mono1 (hd : 1 ≤ d) (j : Fin N) : bwWeight (mono1 N d hd j) = 1 := by
  have h : ∀ l : Fin N, ((Multiset.count l ({j} : Multiset (Fin N))).factorial : ℝ) = 1 := by
    intro l
    rw [Multiset.count_singleton]
    split_ifs <;> simp
  simp only [bwWeight, mono1, MonoIdx.deg, Nat.factorial_one, Nat.cast_one, div_one]
  exact Finset.prod_eq_one fun l _ => h l

lemma bwWeight_lowIdx (hd : 1 ≤ d) (p : Fin n × Option (Fin N)) :
    bwWeight (lowIdx N n d hd p).2 = 1 := by
  obtain ⟨a, o⟩ := p
  cases o with
  | none => exact bwWeight_mono0
  | some j => exact bwWeight_mono1 hd j

/-- The sum of the squares of the coefficients of degree `0` and `1`. -/
noncomputable def lowSq (hd : 1 ≤ d) (b0 : CoefIdx N n d → ℝ) : ℝ :=
  ∑ p : Fin n × Option (Fin N), b0 (lowIdx N n d hd p) ^ 2

lemma lowSq_nonneg (hd : 1 ≤ d) (b0 : CoefIdx N n d → ℝ) : 0 ≤ lowSq hd b0 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma lowSq_smul (hd : 1 ≤ d) (s : ℝ) (b0 : CoefIdx N n d → ℝ) :
    lowSq hd (s • b0) = s ^ 2 * lowSq hd b0 := by
  simp only [lowSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

lemma lowSq_bwOfCoord (hd : 1 ≤ d) (ξ : CoefIdx N n d → ℝ) :
    lowSq hd (bwOfCoord ξ) = ∑ p : Fin n × Option (Fin N), ξ (lowIdx N n d hd p) ^ 2 := by
  unfold lowSq bwOfCoord
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [bwWeight_lowIdx hd p]
  simp

/-- `|W_0 + W_1 u|² ≤ 2·lowSq` for a unit vector `u`. -/
lemma low_bound (hd : 1 ≤ d) (b0 : CoefIdx N n d → ℝ) (u : Fin N → ℝ) (hu : dot u u = 1) :
    ∑ a, (bwEval (mixW b0 0) u a) ^ 2 ≤ 2 * lowSq hd b0 := by
  have hu' : ∑ j, u j ^ 2 = 1 := by rw [← dot_self_eq]; exact hu
  have e : lowSq hd b0 = ∑ a : Fin n, (b0 (a, mono0 N d) ^ 2 +
      ∑ j, b0 (a, mono1 N d hd j) ^ 2) := by
    unfold lowSq
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_option]
    rfl
  rw [e, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [lowEval hd]
  have hcs : (∑ j, b0 (a, mono1 N d hd j) * u j) ^ 2 ≤ ∑ j, b0 (a, mono1 N d hd j) ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => b0 (a, mono1 N d hd j)) u
    rwa [hu', mul_one] at this
  nlinarith [sq_nonneg (b0 (a, mono0 N d) - ∑ j, b0 (a, mono1 N d hd j) * u j)]

/-! ## Domination of the stand-in at a higher noise level -/

/-- **Domination after the projection, upward**: for `0 < b < a`, `h ≥ 0`:
`E h(π(m + a g)) ≤ (a/b)ⁿ exp((1 − (b/a)²)|m|²/(2b²)) E h(π(m + b g))`. -/
lemma proj_dom_up {h : (Fin n → ℝ) → ℝ} (hh : BM h) (h0 : ∀ x, 0 ≤ h x) {a b : ℝ} (hb : 0 < b)
    (hba : b < a) (m : Fin n → ℝ) :
    ∫ z, h (sphProj (m + a • z)) ∂stdGauss (Fin n) ≤
      (a / b) ^ n * Real.exp ((1 - (b / a) ^ 2) * ((∑ i, m i ^ 2) / (2 * b ^ 2))) *
        ∫ z, h (sphProj (m + b • z)) ∂stdGauss (Fin n) := by
  have ha : 0 < a := hb.trans hba
  set t := b / a with ht
  have ht0 : 0 < t := div_pos hb ha
  have ht1 : t < 1 := (div_lt_one ha).mpr hba
  have hta : t ^ 2 * a = t * b := by rw [ht]; field_simp
  have e1 : ∀ z : Fin n → ℝ, sphProj (m + a • z) = sphProj (t ^ 2 • m + (t * b) • z) := by
    intro z
    rw [← sphProj_smul (pow_pos ht0 2) (m + a • z), smul_add, smul_smul, hta]
  simp_rw [e1]
  have hf : BM (fun y => h (sphProj y)) := hh.comp measurable_sphProj
  have htb : t * b < b := by nlinarith
  have key := gauss_shift_dom hf (fun z => h0 _) (mul_pos ht0 hb) htb (t ^ 2 • m) m
  have c1 : b / (t * b) = a / b := by rw [ht]; field_simp
  have h1t : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  have c2 : (∑ i, ((t ^ 2 • m) i - m i) ^ 2) / (2 * (b ^ 2 - (t * b) ^ 2)) =
      (1 - t ^ 2) * ((∑ i, m i ^ 2) / (2 * b ^ 2)) := by
    have hi : ∀ i, ((t ^ 2 • m) i - m i) ^ 2 = (1 - t ^ 2) ^ 2 * m i ^ 2 := by
      intro i
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [hi, ← Finset.mul_sum]
    have h1t' : (1 - t ^ 2) ≠ 0 := h1t.ne'
    have e : b ^ 2 - (t * b) ^ 2 = b ^ 2 * (1 - t ^ 2) := by ring
    rw [e]
    field_simp
  rw [c1, c2] at key
  exact key

/-- **Domination of the stand-in, upward**: for `0 < b < a` and `|W_0 + W_1 u|² ≤ M` for every
unit vector `u`: `E_{ν(a)} h ≤ (a/b)ⁿ exp((1 − (b/a)²) M/(2b²)) E_{ν(b)} h`. -/
theorem nu_dom_up (hN : 1 ≤ N) (b0 : CoefIdx N n d → ℝ) {h : (Fin n → ℝ) → ℝ} (hh : BM h)
    (h0 : ∀ x, 0 ≤ h x) {a b M : ℝ} (hb : 0 < b) (hba : b < a)
    (hM : ∀ u : Fin N → ℝ, dot u u = 1 → ∑ i, (bwEval (mixW b0 0) u i) ^ 2 ≤ M) :
    ∫ x, h x ∂nuW b0 a ≤
      (a / b) ^ n * Real.exp ((1 - (b / a) ^ 2) * (M / (2 * b ^ 2))) * ∫ x, h x ∂nuW b0 b := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  have ha : 0 < a := hb.trans hba
  have ht : 0 ≤ 1 - (b / a) ^ 2 := by
    have h1 : b / a ≤ 1 := (div_le_one ha).mpr hba.le
    have h2 : 0 ≤ b / a := (div_pos hb ha).le
    nlinarith
  rw [nu_integral hN b0 a hh, nu_integral hN b0 b hh, ← integral_const_mul]
  refine integral_mono ((bm_mNoise a (fF hN b0 h) (hf_F hN b0 hh)).integrable _)
    (((BM.const _).mul (bm_mNoise b (fF hN b0 h) (hf_F hN b0 hh))).integrable _) ?_
  intro u
  have key := proj_dom_up hh h0 hb hba (bwEval (mixW b0 0) (fixU hN u))
  refine key.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun z => h0 _)
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (div_pos ha hb).le n)
  refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ ht)
  exact div_le_div_of_nonneg_right (hM _ (dot_fixU hN u)) (by positivity)

/-! ## The deterministic step -/

/-- **The deterministic step from a domination**: if `ν(a) ≤ K·ν(b)` (in the sense of integrals
of nonnegative bounded functions), then from the bound of Theorem 1 at the level `a` and the bound
of the sample mean at the level `b`: `|g − E_μ φ| ≤ (c₁ + c₂ + c₃)·sd_{ν(b)}`. -/
lemma point_dom (hN : 1 ≤ N) (W : CoefIdx N n d → ℝ) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ)
    {a b K : ℝ}
    (hdom : ∀ h : (Fin n → ℝ) → ℝ, BM h → (∀ x, 0 ≤ h x) →
      ∫ x, h x ∂nuW W a ≤ K * ∫ x, h x ∂nuW W b) {k : ℕ}
    (ω : Fin k → (Fin N → ℝ) × (Fin n → ℝ)) {lam δ₁ κ c₁ c₂ c₃ : ℝ} (hlam : 0 ≤ lam)
    (hδ : 0 < δ₁) (hκ : 0 < κ) (hc1 : 0 ≤ c₁) (hc2 : 0 ≤ c₂) (hc3 : 0 ≤ c₃)
    (n1 : lam * K ≤ c₁ ^ 2 * δ₁) (n2 : K * (K - 1) ≤ c₂ ^ 2) (n3 : 1 ≤ c₃ ^ 2 * κ)
    (h1 : δ₁ * (∫ x, φ x ∂muW W - ∫ x, φ x ∂nuW W a) ^ 2 ≤ lam * Var[φ; nuW W a])
    (h3 : κ * (gVal W b φ ω - ∫ x, φ x ∂nuW W b) ^ 2 ≤ Var[φ; nuW W b]) :
    |gVal W b φ ω - ∫ x, φ x ∂muW W| ≤ (c₁ + c₂ + c₃) * Real.sqrt (Var[φ; nuW W b]) := by
  have := nuW_prob hN W a
  have := nuW_prob hN W b
  have hv := dom_var (nuW W a) (nuW W b) K hdom hφ
  have hm := dom_mean (nuW W a) (nuW W b) K hdom hφ
  set V := Var[φ; nuW W b] with hV
  have hV0 : 0 ≤ V := variance_nonneg _ _
  have hx : (∫ x, φ x ∂nuW W a - ∫ x, φ x ∂muW W) ^ 2 ≤ c₁ ^ 2 * V := by
    have e : (∫ x, φ x ∂nuW W a - ∫ x, φ x ∂muW W) ^ 2 =
        (∫ x, φ x ∂muW W - ∫ x, φ x ∂nuW W a) ^ 2 := by ring
    rw [e]
    have : δ₁ * (∫ x, φ x ∂muW W - ∫ x, φ x ∂nuW W a) ^ 2 ≤ δ₁ * (c₁ ^ 2 * V) := by
      calc δ₁ * (∫ x, φ x ∂muW W - ∫ x, φ x ∂nuW W a) ^ 2 ≤ lam * Var[φ; nuW W a] := h1
        _ ≤ lam * (K * V) := mul_le_mul_of_nonneg_left hv hlam
        _ = lam * K * V := by ring
        _ ≤ c₁ ^ 2 * δ₁ * V := mul_le_mul_of_nonneg_right n1 hV0
        _ = δ₁ * (c₁ ^ 2 * V) := by ring
    exact le_of_mul_le_mul_left this hδ
  have hy : (∫ x, φ x ∂nuW W b - ∫ x, φ x ∂nuW W a) ^ 2 ≤ c₂ ^ 2 * V := by
    have e : (∫ x, φ x ∂nuW W b - ∫ x, φ x ∂nuW W a) ^ 2 =
        (∫ x, φ x ∂nuW W a - ∫ x, φ x ∂nuW W b) ^ 2 := by ring
    rw [e]
    exact hm.trans (mul_le_mul_of_nonneg_right n2 hV0)
  have hz : (gVal W b φ ω - ∫ x, φ x ∂nuW W b) ^ 2 ≤ c₃ ^ 2 * V := by
    have : κ * (gVal W b φ ω - ∫ x, φ x ∂nuW W b) ^ 2 ≤ κ * (c₃ ^ 2 * V) := by
      calc κ * (gVal W b φ ω - ∫ x, φ x ∂nuW W b) ^ 2 ≤ V := h3
        _ = 1 * V := (one_mul V).symm
        _ ≤ c₃ ^ 2 * κ * V := mul_le_mul_of_nonneg_right n3 hV0
        _ = κ * (c₃ ^ 2 * V) := by ring
    exact le_of_mul_le_mul_left this hκ
  have h := tri3 hc1 hc2 hc3 hx hy hz
  have e : gVal W b φ ω - ∫ x, φ x ∂muW W =
      (∫ x, φ x ∂nuW W a - ∫ x, φ x ∂muW W) + (∫ x, φ x ∂nuW W b - ∫ x, φ x ∂nuW W a) +
        (gVal W b φ ω - ∫ x, φ x ∂nuW W b) := by ring
  rw [e]
  exact h

/-- **The deterministic step in the Gaussian coordinates, both directions.** The fixed level is
`τ_P/√D_f`. Hypotheses: `D_f(1−θ) ≤ |ξ|² ≤ D_f(1+θ)`, and the sum of the squares of the
coordinates of degree `0` and `1` of `ξ` is at most `L`. The result is relative to the spread at
the fixed level. -/
lemma sphere_point_exact (hN : 1 ≤ N) (hd : 2 ≤ d) (ξ : CoefIdx N n d → ℝ)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) {Df θ L K : ℝ} (hDf : 0 < Df) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hχ1 : Df * (1 - θ) ≤ ∑ i, ξ i ^ 2) (hχ2 : ∑ i, ξ i ^ 2 ≤ Df * (1 + θ))
    (hL : ∑ p : Fin n × Option (Fin N), ξ (lowIdx N n d (by omega) p) ^ 2 ≤ L)
    (hKup : (1 / (1 - θ)) ^ n * Real.exp (θ * (L / ((1 - θ) * tauOf d 1 ^ 2))) ≤ K)
    (hKdn : (1 + θ) ^ n ≤ K) {k : ℕ}
    (ω : Fin k → (Fin N → ℝ) × (Fin n → ℝ)) {lam δ₁ κ c₁ c₂ c₃ : ℝ} (hlam : 0 ≤ lam)
    (hδ : 0 < δ₁) (hκ : 0 < κ) (hc1 : 0 ≤ c₁) (hc2 : 0 ≤ c₂) (hc3 : 0 ≤ c₃)
    (n1 : lam * K ≤ c₁ ^ 2 * δ₁) (n2 : K * (K - 1) ≤ c₂ ^ 2) (n3 : 1 ≤ c₃ ^ 2 * κ)
    (h1 : δ₁ * (∫ x, φ x ∂muW (bwOfCoord ξ) - ∫ x, φ x ∂nuW (bwOfCoord ξ) (tauOf d 1)) ^ 2 ≤
      lam * Var[φ; nuW (bwOfCoord ξ) (tauOf d 1)])
    (h3 : κ * (gVal (bwOfCoord ((1 / Real.sqrt (∑ i, ξ i ^ 2)) • ξ))
          (tauOf d 1 / Real.sqrt Df) φ ω -
        ∫ x, φ x ∂nuW (bwOfCoord ((1 / Real.sqrt (∑ i, ξ i ^ 2)) • ξ))
          (tauOf d 1 / Real.sqrt Df)) ^ 2 ≤
      Var[φ; nuW (bwOfCoord ((1 / Real.sqrt (∑ i, ξ i ^ 2)) • ξ)) (tauOf d 1 / Real.sqrt Df)]) :
    |gVal (bwOfCoord ((1 / Real.sqrt (∑ i, ξ i ^ 2)) • ξ)) (tauOf d 1 / Real.sqrt Df) φ ω -
        ∫ x, φ x ∂muW (bwOfCoord ((1 / Real.sqrt (∑ i, ξ i ^ 2)) • ξ))| ≤
      (c₁ + c₂ + c₃) * Real.sqrt
        (Var[φ; nuW (bwOfCoord ((1 / Real.sqrt (∑ i, ξ i ^ 2)) • ξ))
          (tauOf d 1 / Real.sqrt Df)]) := by
  have hd1 : 1 ≤ d := by omega
  set χ := ∑ i, ξ i ^ 2 with hχ
  have h1θ : 0 < 1 - θ := by linarith
  have hχ0 : 0 < χ := lt_of_lt_of_le (mul_pos hDf h1θ) hχ1
  set S := Real.sqrt χ with hS
  have hS0 : 0 < S := Real.sqrt_pos.mpr hχ0
  set τP := tauOf d 1 with hτP
  have hτ0 : 0 < τP := tauOf_one_pos hd
  set W : CoefIdx N n d → ℝ := bwOfCoord ((1 / S) • ξ) with hW
  have hG : bwOfCoord ξ = S • W := by
    rw [hW, bwOfCoord_smul, smul_smul, mul_one_div_cancel hS0.ne', one_smul]
  set a := τP / S with ha
  have hSa : S * a = τP := by rw [ha]; field_simp
  have ha0 : 0 < a := div_pos hτ0 hS0
  have e_mu : muW (bwOfCoord ξ) = muW W := by rw [hG, muW_smul hS0]
  have e_nu : nuW (bwOfCoord ξ) τP = nuW W a := by rw [hG, ← hSa, nuW_smul hS0]
  set R0 := Real.sqrt Df with hR0
  have hR00 : 0 < R0 := Real.sqrt_pos.mpr hDf
  have hb0 : 0 < τP / R0 := div_pos hτ0 hR00
  have hS2 : S ^ 2 = χ := Real.sq_sqrt hχ0.le
  have hR2 : R0 ^ 2 = Df := Real.sq_sqrt hDf.le
  rw [e_mu, e_nu] at h1
  have hdom : ∀ h : (Fin n → ℝ) → ℝ, BM h → (∀ x, 0 ≤ h x) →
      ∫ x, h x ∂nuW W a ≤ K * ∫ x, h x ∂nuW W (τP / R0) := by
    intro h hh h0
    have hI0 : 0 ≤ ∫ x, h x ∂nuW W (τP / R0) := integral_nonneg h0
    rcases le_or_gt R0 S with hRS | hSR
    · -- the ideal level is at most the fixed level
      have hab : a ≤ τP / R0 := div_le_div_of_nonneg_left hτ0.le hR00 hRS
      have hba : τP / R0 / a = S / R0 := by rw [ha]; field_simp
      have hKK : (τP / R0 / a) ^ n ≤ K := by
        rw [hba]
        have hba1 : 1 ≤ S / R0 := (one_le_div hR00).mpr hRS
        have hsq : (S / R0) ^ 2 ≤ 1 + θ := by
          rw [div_pow, hS2, hR2, div_le_iff₀ hDf]
          linarith
        calc (S / R0) ^ n ≤ (S / R0) ^ (2 * n) := pow_le_pow_right₀ hba1 (by omega)
          _ = ((S / R0) ^ 2) ^ n := pow_mul _ _ _
          _ ≤ (1 + θ) ^ n := pow_le_pow_left₀ (sq_nonneg _) hsq n
          _ ≤ K := hKdn
      exact (nu_dom hN W hh h0 ha0 hab).trans (mul_le_mul_of_nonneg_right hKK hI0)
    · -- the ideal level is above the fixed level
      have hba : τP / R0 < a := div_lt_div_of_pos_left hτ0 hS0 hSR
      have hM : ∀ u : Fin N → ℝ, dot u u = 1 →
          ∑ i, (bwEval (mixW W 0) u i) ^ 2 ≤ 2 * lowSq hd1 W := fun u hu => low_bound hd1 W u hu
      have hup := nu_dom_up hN W hh h0 hb0 hba hM
      refine hup.trans (mul_le_mul_of_nonneg_right ?_ hI0)
      refine le_trans ?_ hKup
      -- the two factors
      have hab' : a / (τP / R0) = R0 / S := by rw [ha]; field_simp
      have hba' : τP / R0 / a = S / R0 := by rw [ha]; field_simp
      have hRS1 : 1 ≤ R0 / S := (one_le_div hS0).mpr hSR.le
      have hsq : (R0 / S) ^ 2 ≤ 1 / (1 - θ) := by
        rw [div_pow, hS2, hR2, div_le_div_iff₀ hχ0 h1θ]
        linarith
      have hf1 : (a / (τP / R0)) ^ n ≤ (1 / (1 - θ)) ^ n := by
        rw [hab']
        calc (R0 / S) ^ n ≤ (R0 / S) ^ (2 * n) := pow_le_pow_right₀ hRS1 (by omega)
          _ = ((R0 / S) ^ 2) ^ n := pow_mul _ _ _
          _ ≤ (1 / (1 - θ)) ^ n := pow_le_pow_left₀ (sq_nonneg _) hsq n
      have hsq2 : (S / R0) ^ 2 = χ / Df := by rw [div_pow, hS2, hR2]
      have hθ' : 1 - (τP / R0 / a) ^ 2 ≤ θ := by
        rw [hba', hsq2]
        have : 1 - θ ≤ χ / Df := by rw [le_div_iff₀ hDf]; linarith
        linarith
      have hθ'0 : 0 ≤ 1 - (τP / R0 / a) ^ 2 := by
        rw [hba', hsq2]
        have : χ / Df ≤ 1 := by
          rw [div_le_one hDf, ← hS2, ← hR2]
          exact pow_le_pow_left₀ hS0.le hSR.le 2
        linarith
      have hlow : lowSq hd1 W = (∑ p : Fin n × Option (Fin N), ξ (lowIdx N n d hd1 p) ^ 2) / χ := by
        rw [hW, bwOfCoord_smul, lowSq_smul, lowSq_bwOfCoord, one_div, inv_pow, hS2]
        ring
      have hLχ : 0 ≤ ∑ p : Fin n × Option (Fin N), ξ (lowIdx N n d hd1 p) ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hM2 : 2 * lowSq hd1 W / (2 * (τP / R0) ^ 2) ≤ L / ((1 - θ) * τP ^ 2) := by
        rw [hlow, div_pow, hR2]
        have e : 2 * ((∑ p : Fin n × Option (Fin N), ξ (lowIdx N n d hd1 p) ^ 2) / χ) /
            (2 * (τP ^ 2 / Df)) =
            (∑ p : Fin n × Option (Fin N), ξ (lowIdx N n d hd1 p) ^ 2) * Df / (χ * τP ^ 2) := by
          field_simp
        rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
        have hτ2 : 0 < τP ^ 2 := by positivity
        calc (∑ p : Fin n × Option (Fin N), ξ (lowIdx N n d hd1 p) ^ 2) * Df *
              ((1 - θ) * τP ^ 2)
            = (∑ p : Fin n × Option (Fin N), ξ (lowIdx N n d hd1 p) ^ 2) *
                (Df * (1 - θ)) * τP ^ 2 := by ring
          _ ≤ L * χ * τP ^ 2 := by
              refine mul_le_mul_of_nonneg_right ?_ hτ2.le
              exact mul_le_mul hL hχ1 (mul_pos hDf h1θ).le (hLχ.trans hL)
          _ = L * (χ * τP ^ 2) := by ring
      have hM20 : 0 ≤ 2 * lowSq hd1 W / (2 * (τP / R0) ^ 2) :=
        div_nonneg (mul_nonneg (by norm_num) (lowSq_nonneg hd1 W)) (by positivity)
      have hexp : Real.exp ((1 - (τP / R0 / a) ^ 2) * (2 * lowSq hd1 W / (2 * (τP / R0) ^ 2))) ≤
          Real.exp (θ * (L / ((1 - θ) * τP ^ 2))) :=
        Real.exp_le_exp.mpr (mul_le_mul hθ' hM2 hM20 hθ0.le)
      exact mul_le_mul hf1 hexp (Real.exp_pos _).le (pow_nonneg (by positivity) n)
  exact point_dom hN W hφ hdom ω hlam hδ hκ hc1 hc2 hc3 n1 n2 n3 h1 h3

/-! ## The paper noise level and the headlines -/

/-- **The noise level of the paper** for the sphere version of `W : ℝ^N → ℝⁿ` of degree `d`:
`τ_0 = √(d−1)/√D`, `D` the number of coefficients of `W` (`τ_0² = 5/D` at `d = 6`). -/
noncomputable def tauPaper (N n d : ℕ) : ℝ :=
  tauOf d 1 / Real.sqrt (Fintype.card (CoefIdx N n d) : ℝ)

/-- `τ_0²` as a rational number: `(d−1)/D`. -/
def tauPaperSq (N n d : ℕ) : ℚ := ((d : ℚ) - 1) / (Fintype.card (CoefIdx N n d) : ℚ)

/-- `τ_0` is the square root of the rational number `(d−1)/D`. -/
theorem tauPaper_eq_sqrt (N n d : ℕ) (hd : 1 ≤ d) :
    tauPaper N n d = Real.sqrt ((tauPaperSq N n d : ℚ) : ℝ) := by
  unfold tauPaper tauPaperSq tauOf
  have : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  push_cast
  rw [mul_one, Real.sqrt_div this]

lemma tauOf_one_sq (hd : 1 ≤ d) : tauOf d 1 ^ 2 = (d : ℝ) - 1 := by
  unfold tauOf
  have : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [mul_one, Real.sq_sqrt this]

/-- The numeric bounds of the two domination constants, `θ = 1/(1024n²)`, `n ≥ 4096`,
`L ≤ 2·n(2n+1)`, `τ_P² ≥ 5`. -/
lemma K_num {n : ℕ} (hn : 4096 ≤ n) {L T : ℝ} (hL0 : 0 ≤ L)
    (hL : L ≤ 2 * ((n : ℝ) * (2 * n + 1))) (hT : 5 ≤ T) :
    (1 / (1 - 1 / (1024 * (n : ℝ) ^ 2))) ^ n *
        Real.exp (1 / (1024 * (n : ℝ) ^ 2) * (L / ((1 - 1 / (1024 * (n : ℝ) ^ 2)) * T))) ≤
          1 + 8 / 10000 ∧
      (1 + 1 / (1024 * (n : ℝ) ^ 2)) ^ n ≤ 1 + 8 / 10000 := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set θ : ℝ := 1 / (1024 * (n : ℝ) ^ 2) with hθ
  have hθ0 : 0 < θ := by positivity
  have hnθ : (n : ℝ) * θ = 1 / (1024 * n) := by rw [hθ]; field_simp
  have hnθ1 : (n : ℝ) * θ ≤ 1 / 4194304 := by
    rw [hnθ]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hθ1 : θ ≤ 1 / 4194304 := by
    have : θ ≤ (n : ℝ) * θ := by nlinarith
    linarith
  have h1θ : 0 < 1 - θ := by linarith
  -- (i) the power
  have hb := one_add_mul_le_pow (a := -θ) (by linarith) n
  have hpow : (1 / (1 - θ)) ^ n ≤ 1 / (1 - n * θ) := by
    rw [one_div, inv_pow, one_div]
    have h1 : 1 - n * θ ≤ (1 - θ) ^ n := by
      have e : (1 : ℝ) + -θ = 1 - θ := by ring
      rw [e] at hb
      linarith
    exact inv_anti₀ (by linarith) h1
  -- (ii) the exponent
  have hT0 : 0 < T := by linarith
  have he : θ * (L / ((1 - θ) * T)) ≤ 79 / 100000 := by
    have h1 : L / ((1 - θ) * T) ≤ 2 * ((n : ℝ) * (2 * n + 1)) / ((1 - θ) * 5) :=
      div_le_div₀ (by positivity) hL (by positivity)
        (mul_le_mul_of_nonneg_left hT h1θ.le)
    have h2 : θ * (L / ((1 - θ) * T)) ≤ θ * (2 * ((n : ℝ) * (2 * n + 1)) / ((1 - θ) * 5)) :=
      mul_le_mul_of_nonneg_left h1 hθ0.le
    refine h2.trans ?_
    have e : θ * (2 * ((n : ℝ) * (2 * n + 1)) / ((1 - θ) * 5)) =
        (4 + 2 / (n : ℝ)) / (5120 * (1 - θ)) := by
      rw [hθ]; field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    have h2n : 2 / (n : ℝ) ≤ 2 / 4096 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn'
    nlinarith
  have he0 : 0 ≤ θ * (L / ((1 - θ) * T)) := by positivity
  have hexp : Real.exp (θ * (L / ((1 - θ) * T))) ≤ 1 / (1 - 79 / 100000) := by
    have h1 := Real.add_one_le_exp (-(θ * (L / ((1 - θ) * T))))
    rw [Real.exp_neg] at h1
    have hpos : 0 < Real.exp (θ * (L / ((1 - θ) * T))) := Real.exp_pos _
    have h2 : 1 - 79 / 100000 ≤ (Real.exp (θ * (L / ((1 - θ) * T))))⁻¹ := by linarith
    rw [one_div]
    exact (le_inv_comm₀ (by norm_num) hpos).mp h2
  constructor
  · calc (1 / (1 - θ)) ^ n * Real.exp (θ * (L / ((1 - θ) * T)))
        ≤ 1 / (1 - n * θ) * (1 / (1 - 79 / 100000)) :=
          mul_le_mul hpow hexp (Real.exp_pos _).le (by
            rw [one_div]; exact inv_nonneg.mpr (by linarith))
      _ ≤ 1 / (1 - 1 / 4194304) * (1 / (1 - 79 / 100000)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
          exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      _ ≤ 1 + 8 / 10000 := by norm_num
  · have h := one_add_pow_le hθ0.le n (by linarith)
    refine h.trans ?_
    calc 1 / (1 - n * θ) ≤ 1 / (1 - 1 / 4194304) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      _ ≤ 1 + 8 / 10000 := by norm_num

/-- **Theorem 0 for the sphere version of `W` with the paper noise level, core form.**
`W : ℝ^{2n} → ℝⁿ` of degree `d ≥ 6` with the Bombieri–Weyl sphere distribution; `n ≥ 4096`;
`k ≥ 1200` samples; `λ_0 ≤ (1/(10n))(1+2/n)`; `D ≥ 5242880000·n⁴`. With probability at least
`99/100` over all the coefficients of `W` and the random inputs of the program:
`|g − B(W, A, F)| ≤ (1/2)·sd_ν`, with `g` and `sd_ν` at the noise level `tauPaper`,
`τ_0² = (d−1)/D`. -/
theorem thm0_sphere_core (hd : 6 ≤ d) (hn : 4096 ≤ n) {k dA dF : ℕ}
    (hk : 1200 ≤ k) (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ)
    (hlam : lam0 (2 * n) d ≤ 1 / (10 * (n : ℝ)) * (1 + 2 / (n : ℝ)))
    (hD : 5242880000 * (n : ℝ) ^ 4 ≤ (Fintype.card (CoefIdx (2 * n) n d) : ℝ)) :
    99 / 100 ≤
      ((bwSphere (2 * n) n d).prod
        (Measure.pi fun _ : Fin k => (uniformSphere (2 * n)).prod (stdGauss (Fin n)))).real
        {p | |gVal p.1 (tauPaper (2 * n) n d) (phiAF A F) p.2 - ∫ x, phiAF A F x ∂muW p.1| ≤
          1 / 2 * Real.sqrt (Var[phiAF A F; nuW p.1 (tauPaper (2 * n) n d)])} := by
  have hN : 1 ≤ 2 * n := by omega
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have := BstLean.Part29.uniformSphere_isProbability (2 * n) hN
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hk1 : 1 ≤ k := by omega
  have hk' : (1200 : ℝ) ≤ k := by exact_mod_cast hk
  set γ := stdGauss (CoefIdx (2 * n) n d) with hγ
  set π : Measure (Fin k → (Fin (2 * n) → ℝ) × (Fin n → ℝ)) :=
    Measure.pi fun _ : Fin k => (uniformSphere (2 * n)).prod (stdGauss (Fin n)) with hπ
  set D : ℝ := (Fintype.card (CoefIdx (2 * n) n d) : ℝ) with hDdef
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD
  set θ : ℝ := 1 / (1024 * (n : ℝ) ^ 2) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by
    rw [hθ, div_lt_one (by positivity)]
    nlinarith
  have ht : 0 < θ * D := mul_pos hθ0 hD0
  -- the probability step of `Part106Sphere`
  have hsp := sphere_prob hN hd2 (bm_phiT A F) hk1 (δ₁ := 20 / 10000) (δ₃ := 75 / 10000)
    (t := θ * D) (by norm_num) (by norm_num) ht (tauPaper (2 * n) n d)
  have hnum : 2 * D / (θ * D) ^ 2 ≤ 4 / 10000 := by
    have e : 2 * D / (θ * D) ^ 2 = 2097152 * (n : ℝ) ^ 4 / D := by
      rw [hθ]; field_simp; ring
    rw [e, div_le_iff₀ hD0]
    linarith
  -- the coefficients of degree 0 and 1
  set Dl : ℝ := (Fintype.card (Fin n × Option (Fin (2 * n))) : ℝ) with hDl
  have hDlv : Dl = (n : ℝ) * (2 * n + 1) := by
    rw [hDl]
    simp [Fintype.card_prod, Fintype.card_option]
  have hDl0 : 0 < Dl := by rw [hDlv]; positivity
  set E5 : Set (CoefIdx (2 * n) n d → ℝ) :=
    {ξ | Dl ≤ |∑ p : Fin n × Option (Fin (2 * n)), ξ (lowIdx (2 * n) n d hd1 p) ^ 2 - Dl|}
    with hE5
  have hP5 : γ.real E5 ≤ 1 / 10000 := by
    have h := chiSq_cheb_sub (CoefIdx (2 * n) n d) (lowIdx (2 * n) n d hd1)
      (lowIdx_injective hd1) hDl0
    refine h.trans ?_
    have e : 2 * Dl / Dl ^ 2 = 2 / Dl := by field_simp
    rw [e, div_le_div_iff₀ hDl0 (by norm_num), hDlv]
    nlinarith
  refine le_trans ?_ (sphere_transfer hN _)
  set T : Set ((CoefIdx (2 * n) n d → ℝ) × (Fin k → (Fin (2 * n) → ℝ) × (Fin n → ℝ))) :=
    {p | ((bwOfCoord ((1 / Real.sqrt (∑ i, p.1 i ^ 2)) • p.1), p.2) :
          (CoefIdx (2 * n) n d → ℝ) × (Fin k → (Fin (2 * n) → ℝ) × (Fin n → ℝ))) ∈
        {p | |gVal p.1 (tauPaper (2 * n) n d) (phiAF A F) p.2 - ∫ x, phiAF A F x ∂muW p.1| ≤
          1 / 2 * Real.sqrt (Var[phiAF A F; nuW p.1 (tauPaper (2 * n) n d)])}} with hT
  have hsub : {p : (CoefIdx (2 * n) n d → ℝ) × (Fin k → (Fin (2 * n) → ℝ) × (Fin n → ℝ)) |
        |∑ i, p.1 i ^ 2 - D| < θ * D ∧
          20 / 10000 * (∫ x, phiT A F x ∂muW (bwOfCoord p.1) -
              ∫ x, phiT A F x ∂nuW (bwOfCoord p.1) (tauOf d 1)) ^ 2 ≤
            lam0 (2 * n) d * Var[phiT A F; nuW (bwOfCoord p.1) (tauOf d 1)] ∧
          k * (75 / 10000) *
              (gVal (bwOfCoord ((1 / Real.sqrt (∑ i, p.1 i ^ 2)) • p.1)) (tauPaper (2 * n) n d)
                  (phiT A F) p.2 -
                ∫ x, phiT A F x ∂nuW (bwOfCoord ((1 / Real.sqrt (∑ i, p.1 i ^ 2)) • p.1))
                  (tauPaper (2 * n) n d)) ^ 2 ≤
            Var[phiT A F; nuW (bwOfCoord ((1 / Real.sqrt (∑ i, p.1 i ^ 2)) • p.1))
              (tauPaper (2 * n) n d)]} ⊆ T ∪ E5 ×ˢ Set.univ := by
    intro p hp
    by_cases h5 : p.1 ∈ E5
    · exact Or.inr ⟨h5, Set.mem_univ _⟩
    left
    obtain ⟨h4, h1, h3⟩ := hp
    simp only [hE5, Set.mem_setOf_eq, not_le] at h5
    simp only [hT, Set.mem_setOf_eq]
    rw [gVal_phiT, muInt_phiT, nuVar_phiT]
    have h4' := abs_lt.mp h4
    have h5' := abs_lt.mp h5
    have hlam0 : 0 ≤ lam0 (2 * n) d := lam0_nonneg hN hd2
    have hΛ := lam_num hn
    have hT5 : (5 : ℝ) ≤ tauOf d 1 ^ 2 := by
      rw [tauOf_one_sq hd1]
      have : (6 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have hKn := K_num hn (L := 2 * Dl) (T := tauOf d 1 ^ 2) (by positivity)
      (by rw [hDlv]) hT5
    have hc1 : D * (1 - θ) ≤ ∑ i, p.1 i ^ 2 := by
      have e : D * (1 - θ) = D - θ * D := by ring
      rw [e]; linarith [h4'.1]
    have hc2 : ∑ i, p.1 i ^ 2 ≤ D * (1 + θ) := by
      have e : D * (1 + θ) = D + θ * D := by ring
      rw [e]; linarith [h4'.2]
    have hc3 : ∑ q : Fin n × Option (Fin (2 * n)), p.1 (lowIdx (2 * n) n d hd1 q) ^ 2 ≤
        2 * Dl := by linarith [h5'.2]
    have hn1 : lam0 (2 * n) d * (1 + 8 / 10000) ≤ (111 / 1000 : ℝ) ^ 2 * (20 / 10000) := by
      have h : lam0 (2 * n) d ≤ (108 / 1000 : ℝ) ^ 2 * (21 / 10000) := hlam.trans hΛ
      calc lam0 (2 * n) d * (1 + 8 / 10000)
          ≤ (108 / 1000 : ℝ) ^ 2 * (21 / 10000) * (1 + 8 / 10000) :=
            mul_le_mul_of_nonneg_right h (by norm_num)
        _ ≤ (111 / 1000 : ℝ) ^ 2 * (20 / 10000) := by norm_num
    have hn3 : (1 : ℝ) ≤ (334 / 1000 : ℝ) ^ 2 * ((k : ℝ) * (75 / 10000)) := by linarith
    have hκ : (0 : ℝ) < (k : ℝ) * (75 / 10000) := by linarith
    have hpt := sphere_point_exact hN hd2 p.1 (bm_phiT A F) (Df := D) (θ := θ) (L := 2 * Dl)
      (K := 1 + 8 / 10000) hD0 hθ0 hθ1 hc1 hc2 hc3
      hKn.1 hKn.2 p.2 (lam := lam0 (2 * n) d) (δ₁ := 20 / 10000)
      (κ := (k : ℝ) * (75 / 10000)) (c₁ := 111 / 1000) (c₂ := 29 / 1000) (c₃ := 334 / 1000)
      hlam0 (by norm_num) hκ (by norm_num) (by norm_num) (by norm_num)
      hn1 (by norm_num) hn3 h1 h3
    have htf : tauPaper (2 * n) n d = tauOf d 1 / Real.sqrt D := rfl
    rw [htf]
    refine hpt.trans ?_
    exact mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)
  have h1 : (γ.prod π).real (E5 ×ˢ Set.univ) = γ.real E5 := by
    simp [measureReal_def, Measure.prod_prod]
  have h2 := (measureReal_mono hsub (μ := γ.prod π)).trans (measureReal_union_le _ _)
  rw [h1] at h2
  linarith

/-- The number of coefficients of `W` at `r = 2`, `d = 6` is at least `5242880000·n⁴`. -/
lemma card_six_ge {n : ℕ} (hn : 4096 ≤ n) :
    5242880000 * (n : ℝ) ^ 4 ≤ (Fintype.card (CoefIdx (2 * n) n 6) : ℝ) := by
  rw [card_coefIdx]
  have h5 := choose6_ge n
  have h6 : (2 * n + 5).choose 6 ≤ (2 * n + 6).choose 6 := Nat.choose_le_choose 6 (by omega)
  have h3 : 58982400000 ≤ n ^ 3 :=
    le_trans (by norm_num) (Nat.pow_le_pow_left hn 3)
  have key : 720 * (5242880000 * n ^ 4) ≤ 720 * (n * (2 * n + 6).choose 6) := by
    calc 720 * (5242880000 * n ^ 4) = 64 * 58982400000 * n ^ 4 := by ring
      _ ≤ 64 * n ^ 3 * n ^ 4 := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3)
      _ = n * (64 * n ^ 6) := by ring
      _ ≤ n * (720 * (2 * n + 5).choose 6) := Nat.mul_le_mul_left _ h5
      _ ≤ n * (720 * (2 * n + 6).choose 6) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h6)
      _ = 720 * (n * (2 * n + 6).choose 6) := by ring
  have := Nat.le_of_mul_le_mul_left key (by norm_num)
  exact_mod_cast this

/-- The number of coefficients of `W` at `r = 2`, `d = 8` is at least `5242880000·n⁴`. -/
lemma card_eight_ge {n : ℕ} (hn : 4096 ≤ n) :
    5242880000 * (n : ℝ) ^ 4 ≤ (Fintype.card (CoefIdx (2 * n) n 8) : ℝ) := by
  rw [card_coefIdx]
  have h5 := choose8_ge n
  have h6 : (2 * n + 7).choose 8 ≤ (2 * n + 8).choose 8 := Nat.choose_le_choose 8 (by omega)
  have h3 : 825753600000 ≤ n ^ 5 :=
    le_trans (by norm_num) (Nat.pow_le_pow_left hn 5)
  have key : 40320 * (5242880000 * n ^ 4) ≤ 40320 * (n * (2 * n + 8).choose 8) := by
    calc 40320 * (5242880000 * n ^ 4) = 256 * 825753600000 * n ^ 4 := by ring
      _ ≤ 256 * n ^ 5 * n ^ 4 := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3)
      _ = n * (256 * n ^ 8) := by ring
      _ ≤ n * (40320 * (2 * n + 7).choose 8) := Nat.mul_le_mul_left _ h5
      _ ≤ n * (40320 * (2 * n + 8).choose 8) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h6)
      _ = 40320 * (n * (2 * n + 8).choose 8) := by ring
  have := Nat.le_of_mul_le_mul_left key (by norm_num)
  exact_mod_cast this

/-- **Theorem 0 for the sphere version of `W`, `r = 2`, `d_A = 3`, paper noise level**
(`W : ℝ^{2n} → ℝⁿ` of degree `6` with the Bombieri–Weyl sphere distribution, the distribution of
the north star; every `d_F`). For every `n ≥ 4096`, every `k ≥ 1200`, every `A` and `F`: with
probability at least `99/100` over ALL the coefficients of `W` and the `k` blocks of random
inputs of the program `g`, `|g − B(W, A, F)| ≤ (1/2)·sd_ν`. Here `g` reads the coefficients of
degree `0` and `1` of `W` and uses the fixed noise level `τ_0 = tauPaper (2n) n 6`,
`τ_0² = 5/D_W`, and `sd_ν² = Var_{ν_W}(F ∘ A)` is the variance under the stand-in at that
level. -/
theorem thm0_sphere_dA3 (n k dF : ℕ) (hn : 4096 ≤ n) (hk : 1200 ≤ k)
    (A : CoefIdx n n 3 → ℝ) (F : CoefIdx n 1 dF → ℝ) :
    99 / 100 ≤
      ((bwSphere (2 * n) n 6).prod
        (Measure.pi fun _ : Fin k => (uniformSphere (2 * n)).prod (stdGauss (Fin n)))).real
        {p | |gVal p.1 (tauPaper (2 * n) n 6) (phiAF A F) p.2 - ∫ x, phiAF A F x ∂muW p.1| ≤
          1 / 2 * Real.sqrt (Var[phiAF A F; nuW p.1 (tauPaper (2 * n) n 6)])} :=
  thm0_sphere_core (d := 6) (by norm_num) hn hk A F (lam0_bound n (by omega)) (card_six_ge hn)

/-- **Theorem 0 for the sphere version of `W`, `r = 2`, `d_A = 4`, paper noise level**
(degree `8`; `τ_0² = 7/D_W`). The statement is that of `thm0_sphere_dA3`. -/
theorem thm0_sphere_dA4 (n k dF : ℕ) (hn : 4096 ≤ n) (hk : 1200 ≤ k)
    (A : CoefIdx n n 4 → ℝ) (F : CoefIdx n 1 dF → ℝ) :
    99 / 100 ≤
      ((bwSphere (2 * n) n 8).prod
        (Measure.pi fun _ : Fin k => (uniformSphere (2 * n)).prod (stdGauss (Fin n)))).real
        {p | |gVal p.1 (tauPaper (2 * n) n 8) (phiAF A F) p.2 - ∫ x, phiAF A F x ∂muW p.1| ≤
          1 / 2 * Real.sqrt (Var[phiAF A F; nuW p.1 (tauPaper (2 * n) n 8)])} :=
  thm0_sphere_core (d := 8) (by norm_num) hn hk A F (lam0_eight_le (by omega))
    (card_eight_ge hn)

end BstLean.Part106

#print axioms BstLean.Part106.proj_dom_up
#print axioms BstLean.Part106.nu_dom_up
#print axioms BstLean.Part106.low_bound
#print axioms BstLean.Part106.sphere_point_exact
#print axioms BstLean.Part106.tauPaper_eq_sqrt
#print axioms BstLean.Part106.thm0_sphere_core
#print axioms BstLean.Part106.thm0_sphere_dA3
#print axioms BstLean.Part106.thm0_sphere_dA4
