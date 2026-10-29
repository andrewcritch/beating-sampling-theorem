import BstLean.Part160Defs

/-!
# Part 160 (file `Mass4`): fourth moments of `1`-Lipschitz functions of the hidden vector

Do not use `sorry`, `native_decide` or `axiom`.

`t = 2/m`, `h = hid2 A₁ A₂`, `x(ξ) = sphPt (c + τ ξ)`, `ξ` standard Gaussian. For a function
`F` of the hidden space that is `1`-Lipschitz (`EuLip F 1`), `u(ξ) = F(√t·h(x(ξ)))` (`uD`).

* `lipD_var`: `Var_ξ u ≤ Ξ` (Lemma S, second assertion).
* `lipD_fourth_sharp`: `E_ξ (u − E u)⁴ ≤ (2a + √(4a² + V²))²` for every `a ≥ Ξ₄`,
  `V ≥ Var_ξ u`. The proof uses the Poincaré inequality with a pointwise Lipschitz constant
  (`lemmaS_loc_sl` of Part 153) for `(u − E u)²`, and no `L⁴` Poincaré inequality:
  `X − Var² ≤ 4tτ² E[(u − Eu)²·‖𝒥Π‖²/|y|²] ≤ (2/k)X + 2k Ξ₄²` for every `k > 0`.
* `lipD_fourth`: `E_ξ (u − E u)⁴ ≤ (2 + √5)²·Ξ₄²`.
* `lipD_cheb`, `lipD_markov4`, `lipD_markov4_sharp`: the tail bounds.
* Instances: `v1D` (`v = √t·⟨h, b/|b|⟩ = √t·|b|·λ`) and `sigD` (`σ = √t·|res b h|`), with
  `v1D_var`, `v1D_fourth`, `v1D_cheb`, `v1D_markov4`, `sigD_var`, `sigD_fourth`, `sigD_cheb`,
  `sigD_markov4`, and the sharp forms.
* `res_energy_eq`: `t|res b h|² = t|h|² − (√t·|b|·λ)²`; `sigD_sq`: `σ² = t|res b h|²`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part148 (EuLip)
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm jacT XiS Xi4)

variable {n m : ℕ}

/-! ## A fact about real numbers -/

/-- If `X − V² ≤ (2/k)X + 2k a²` for every `k > 0`, then `X ≤ (2a + √(4a² + V²))²`. -/
lemma quad_bound {X a V : ℝ} (hX : 0 ≤ X) (ha : 0 ≤ a)
    (h : ∀ k : ℝ, 0 < k → X - V ^ 2 ≤ 2 / k * X + 2 * k * a ^ 2) :
    X ≤ (2 * a + √(4 * a ^ 2 + V ^ 2)) ^ 2 := by
  have hr : 0 ≤ √(4 * a ^ 2 + V ^ 2) := Real.sqrt_nonneg _
  have hD : 0 ≤ 4 * a ^ 2 + V ^ 2 := by positivity
  rcases hX.eq_or_lt with hX0 | hXpos
  · rw [← hX0]; positivity
  rcases ha.eq_or_lt with ha0 | hapos
  · rw [← ha0]
    have e : (2 * (0 : ℝ) + √(4 * 0 ^ 2 + V ^ 2)) ^ 2 = V ^ 2 := by
      have : (4 : ℝ) * 0 ^ 2 + V ^ 2 = V ^ 2 := by ring
      rw [this, mul_zero, zero_add, Real.sq_sqrt (sq_nonneg V)]
    rw [e]
    by_contra hc
    rw [not_le] at hc
    have hd : 0 < X - V ^ 2 := by linarith
    have h1 := h (4 * X / (X - V ^ 2)) (by positivity)
    rw [← ha0] at h1
    have e2 : 2 / (4 * X / (X - V ^ 2)) * X = (X - V ^ 2) / 2 := by
      field_simp
      ring
    rw [e2] at h1
    nlinarith
  · obtain ⟨s, hs⟩ : ∃ s : ℝ, s = √X := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hXpos
    have hs2 : s ^ 2 = X := by rw [hs]; exact Real.sq_sqrt hX
    have h1 := h (s / a) (by positivity)
    have e : 2 / (s / a) * X + 2 * (s / a) * a ^ 2 = 4 * a * s := by
      rw [← hs2]
      field_simp
      ring
    rw [e, ← hs2] at h1
    have h2 : (s - 2 * a) ^ 2 ≤ 4 * a ^ 2 + V ^ 2 := by nlinarith
    have h3 : s - 2 * a ≤ √(4 * a ^ 2 + V ^ 2) := by
      have := Real.abs_le_sqrt h2
      exact (le_abs_self _).trans this
    rw [← hs2]
    exact pow_le_pow_left₀ hs0.le (by linarith) 2

/-! ## The general statement -/

/-- `u(ξ) = F(√t·h(x(ξ)))`, `t = 2/m`. -/
noncomputable def uD (F : (Fin m → ℝ) → ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) : ℝ :=
  F (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ)))

lemma eulip_nrm {F : (Fin m → ℝ) → ℝ} (hF : EuLip F 1) (x y : Fin m → ℝ) :
    |F x - F y| ≤ nrm (x - y) := by
  have h := hF x y
  rw [one_mul] at h
  exact h

lemma measurable_uD {F : (Fin m → ℝ) → ℝ} (hF : EuLip F 1) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) (τ : ℝ) : Measurable (uD F A₁ A₂ c τ) := by
  have h1 : Measurable (fun ξ : Fin n → ℝ =>
      √(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) :=
    (measurable_const_smul (√(2 / (m : ℝ)))).comp
      (BstLean.Part153.measurable_hid2_sph_cr A₁ A₂ c τ)
  exact (BstLean.Part148.EuLip.continuous zero_le_one hF).measurable.comp h1

lemma uD_bdd (hn : 1 ≤ n) {F : (Fin m → ℝ) → ℝ} (hF : EuLip F 1)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ, |uD F A₁ A₂ c τ ξ| ≤ B := by
  have hop : 0 ≤ opN A₂ * opN A₁ :=
    mul_nonneg (BstLean.Part152.opN_nonneg _) (BstLean.Part152.opN_nonneg _)
  refine ⟨|F 0| + √(2 / (m : ℝ)) * (opN A₂ * opN A₁),
    add_nonneg (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hop), fun ξ => ?_⟩
  have h1 := eulip_nrm hF (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) 0
  rw [sub_zero, BstLean.Part153.nrm_smul, abs_of_nonneg (Real.sqrt_nonneg _)] at h1
  have h2 := BstLean.Part153.nrm_hid2_sph_le_cr hn A₁ A₂ (c + τ • ξ)
  have h3 := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg (2 / (m : ℝ)))
  have h4 : |uD F A₁ A₂ c τ ξ| ≤ |uD F A₁ A₂ c τ ξ - F 0| + |F 0| := by
    have := abs_add_le (uD F A₁ A₂ c τ ξ - F 0) (F 0)
    rwa [sub_add_cancel] at this
  have h5 : |uD F A₁ A₂ c τ ξ - F 0| ≤ √(2 / (m : ℝ)) * (opN A₂ * opN A₁) := h1.trans h3
  linarith

/-- **The variance of a `1`-Lipschitz function of the hidden vector**: `Var_ξ u ≤ Ξ`. -/
theorem lipD_var (hn : 6 ≤ n) {F : (Fin m → ℝ) → ℝ} (hF : EuLip F 1)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∫ ξ, (uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 2
      ∂stdGauss (Fin n) ≤ XiS A₁ A₂ c τ := by
  have h := (BstLean.Part153.lemmaS_jac hn A₁ A₂ c hτ zero_le_one hF).2
  rw [one_pow, one_mul] at h
  exact h

/-- The core inequality: for every `k > 0`, `X − Var² ≤ (2/k)·X + 2k·Ξ₄²`, with
`X = E(u − Eu)⁴`. Also the integrability of the fourth power. -/
theorem lipD_core (hn : 6 ≤ n) {F : (Fin m → ℝ) → ℝ} (hF : EuLip F 1)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun ξ => (uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 4)
      (stdGauss (Fin n)) ∧
    ∀ k : ℝ, 0 < k →
      ∫ ξ, (uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 4
          ∂stdGauss (Fin n) -
        (∫ ξ, (uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 2
          ∂stdGauss (Fin n)) ^ 2 ≤
      2 / k * ∫ ξ, (uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 4
          ∂stdGauss (Fin n) + 2 * k * Xi4 A₁ A₂ c τ ^ 2 := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn1 : 1 ≤ n := by omega
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ, m₀ = ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← hm₀]
  obtain ⟨u, hu⟩ : ∃ u : (Fin n → ℝ) → ℝ, u = fun ξ => uD F A₁ A₂ c τ ξ - m₀ := ⟨_, rfl⟩
  have hum : Measurable u := by rw [hu]; exact (measurable_uD hF A₁ A₂ c τ).sub_const _
  obtain ⟨B0, hB0, hB⟩ := uD_bdd hn1 hF A₁ A₂ c τ
  have hub : ∀ ξ, |u ξ| ≤ B0 + |m₀| := fun ξ => by
    rw [hu]; exact (abs_sub _ _).trans (add_le_add (hB ξ) le_rfl)
  have hpow : ∀ k : ℕ, Integrable (fun ξ => u ξ ^ k) (stdGauss (Fin n)) := fun k =>
    Integrable.of_bound (hum.pow_const k).aestronglyMeasurable ((B0 + |m₀|) ^ k)
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hub ξ) k)
  have e4 : (fun ξ => (uD F A₁ A₂ c τ ξ - m₀) ^ 4) = fun ξ => u ξ ^ 4 := by rw [hu]
  have e2 : (fun ξ => (uD F A₁ A₂ c τ ξ - m₀) ^ 2) = fun ξ => u ξ ^ 2 := by rw [hu]
  rw [e4, e2]
  refine ⟨hpow 4, ?_⟩
  -- the Poincaré inequality for `(u − m₀)²`
  obtain ⟨φ, hφ⟩ : ∃ φ : (Fin m → ℝ) → ℝ, φ = fun z => (F z - m₀) ^ 2 := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : (Fin m → ℝ) → ℝ, ℓ = fun z => 2 * |F z - m₀| := ⟨_, rfl⟩
  have hq : ∀ ξ, F (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) - m₀ = u ξ := by
    intro ξ
    rw [hu]
    rfl
  have hℓnn : ∀ z, 0 ≤ ℓ z := fun z => by
    rw [hℓ]; exact mul_nonneg (by norm_num) (abs_nonneg _)
  have key : ∀ z z' : Fin m → ℝ, |φ z' - φ z| ≤ (ℓ z + nrm (z' - z)) * nrm (z' - z) := by
    intro z z'
    have hd := eulip_nrm hF z' z
    have e : φ z' - φ z = (F z' - F z) * ((F z' - F z) + 2 * (F z - m₀)) := by rw [hφ]; ring
    rw [e, abs_mul, mul_comm]
    refine mul_le_mul ?_ hd (abs_nonneg _)
      (add_nonneg (hℓnn z) (BstLean.Part153.nrm_nonneg _))
    refine (abs_add_le _ _).trans ?_
    have e' : ℓ z = 2 * |F z - m₀| := by rw [hℓ]
    rw [e', abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hℓbd : ∀ R : ℝ, ∀ z : Fin m → ℝ, nrm z ≤ R → ℓ z ≤ 2 * (|R| + |F 0| + |m₀|) := by
    intro R z hz
    have e' : ℓ z = 2 * |F z - m₀| := by rw [hℓ]
    rw [e']
    have h1 := eulip_nrm hF z 0
    rw [sub_zero] at h1
    have h2 := abs_sub (F z) m₀
    have h3 := le_abs_self R
    have h4 : |F z| ≤ |F z - F 0| + |F 0| := by
      have := abs_add_le (F z - F 0) (F 0)
      rwa [sub_add_cancel] at this
    linarith
  have S := BstLean.Part153.lemmaS_loc_sl hn A₁ A₂ c hτ (φ := φ) (ℓ := ℓ)
    (by
      intro R
      refine ⟨2 * (|R| + |F 0| + |m₀|) + 2 * |R|, by positivity, fun x _ y _ hx hy => ?_⟩
      have h1 := key y x
      have h2 := hℓbd R y hy
      have h3 : nrm (x - y) ≤ 2 * |R| := by
        have e : x - y = x + (-1 : ℝ) • y := by
          ext j; simp [sub_eq_add_neg]
        have h4 := BstLean.Part153.nrm_add_le x ((-1 : ℝ) • y)
        rw [BstLean.Part153.nrm_smul, abs_neg, abs_one, one_mul] at h4
        rw [e]
        have := le_abs_self R
        linarith
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ (BstLean.Part153.nrm_nonneg _))
      linarith)
    (by
      intro z _ δ hδ
      refine ⟨δ, hδ, fun z' _ hz' => ?_⟩
      refine (key z z').trans (mul_le_mul_of_nonneg_right ?_ (BstLean.Part153.nrm_nonneg _))
      linarith)
    (fun z _ => hℓnn z)
    (by
      have e : (fun ξ : Fin n → ℝ => ℓ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ)))) =
          fun ξ => 2 * |u ξ| := by
        funext ξ; rw [hℓ]; change 2 * |_| = _; rw [hq]
      rw [e]
      exact (continuous_abs.measurable.comp hum).const_mul 2)
    (by
      intro R
      exact ⟨2 * (|R| + |F 0| + |m₀|), fun z _ hz => hℓbd R z hz⟩)
  obtain ⟨G, hG⟩ : ∃ G : (Fin n → ℝ) → ℝ, G = fun ξ =>
      opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹ := ⟨_, rfl⟩
  have eφ' : ∀ ξ : Fin n → ℝ, φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) = u ξ ^ 2 := by
    intro ξ; rw [hφ]; change (_ - m₀) ^ 2 = _; rw [hq]
  have eℓ : (fun ξ : Fin n → ℝ => ℓ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
      (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹)) =
      fun ξ => 4 * u ξ ^ 2 * G ξ := by
    funext ξ
    rw [hℓ, hG]
    change (2 * |_|) ^ 2 * _ = _
    rw [hq, mul_pow, sq_abs]
    norm_num
  obtain ⟨S1, S2, S3⟩ := S
  simp only [eφ'] at S2 S3
  rw [eℓ] at S1 S3
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = ∫ ξ, u ξ ^ 2 ∂stdGauss (Fin n) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∫ ξ, u ξ ^ 4 ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← hV] at S3
  rw [← hX, ← hV]
  have hvar : ∫ ξ, (u ξ ^ 2 - V) ^ 2 ∂stdGauss (Fin n) = X - V ^ 2 := by
    have e : (fun ξ => (u ξ ^ 2 - V) ^ 2) = fun ξ => u ξ ^ 4 - 2 * V * u ξ ^ 2 + V ^ 2 :=
      funext fun ξ => by ring
    have h2 : Integrable (fun ξ => 2 * V * u ξ ^ 2) (stdGauss (Fin n)) := (hpow 2).const_mul _
    have h3 : Integrable (fun ξ => u ξ ^ 4 - 2 * V * u ξ ^ 2) (stdGauss (Fin n)) :=
      (hpow 4).sub h2
    rw [e, integral_add h3 (integrable_const _), integral_sub (hpow 4) h2,
      integral_const_mul, integral_const, ← hV, ← hX]
    rw [show (stdGauss (Fin n)).real Set.univ = 1 from by simp, one_smul]
    ring
  rw [hvar] at S3
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 2 / (m : ℝ) * τ ^ 2 := ⟨_, rfl⟩
  rw [← hT] at S3
  have hGi := BstLean.Part153.integrable_Xi4 hn A₁ A₂ c hτ
  have eG2 : (fun ξ : Fin n → ℝ => opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 4 *
      (normSq (c + τ • ξ))⁻¹ ^ 2) = fun ξ => G ξ ^ 2 := by
    funext ξ; rw [hG]; ring
  rw [eG2] at hGi
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = ∫ ξ, G ξ ^ 2 ∂stdGauss (Fin n) := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by rw [hY]; exact integral_nonneg fun ξ => sq_nonneg _
  have ha2 : Xi4 A₁ A₂ c τ ^ 2 = T ^ 2 * Y := by
    unfold Xi4
    rw [eG2, ← hY, ← hT, mul_pow, Real.sq_sqrt hY0]
  intro k hk0
  -- pointwise: `4 T u² G ≤ (2/k) u⁴ + 2k T² G²`
  have hpt : ∀ ξ, T * (4 * u ξ ^ 2 * G ξ) ≤ 2 / k * u ξ ^ 4 + 2 * k * T ^ 2 * G ξ ^ 2 := by
    intro ξ
    have h := sq_nonneg (u ξ ^ 2 - k * T * G ξ)
    have e : 2 / k * u ξ ^ 4 + 2 * k * T ^ 2 * G ξ ^ 2 - T * (4 * u ξ ^ 2 * G ξ) =
        2 / k * (u ξ ^ 2 - k * T * G ξ) ^ 2 := by
      field_simp
      ring
    have : 0 ≤ 2 / k * (u ξ ^ 2 - k * T * G ξ) ^ 2 := mul_nonneg (by positivity) h
    linarith
  have hint : T * ∫ ξ, 4 * u ξ ^ 2 * G ξ ∂stdGauss (Fin n) ≤ 2 / k * X + 2 * k * T ^ 2 * Y := by
    rw [← integral_const_mul, hX, hY, ← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hpow 4).const_mul _) (hGi.const_mul _)]
    exact integral_mono (S1.const_mul _) (((hpow 4).const_mul _).add (hGi.const_mul _)) hpt
  have hmain : X - V ^ 2 ≤ 2 / k * X + 2 * k * T ^ 2 * Y := S3.trans hint
  rw [ha2]
  linarith

/-- **The fourth moment, sharp form**: `E(u − Eu)⁴ ≤ (2a + √(4a² + V²))²` for every `a ≥ Ξ₄`
and `V ≥ Var u`. -/
theorem lipD_fourth_sharp (hn : 6 ≤ n) {F : (Fin m → ℝ) → ℝ} (hF : EuLip F 1)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {a V : ℝ} (ha : Xi4 A₁ A₂ c τ ≤ a)
    (hV : ∫ ξ, (uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 2
      ∂stdGauss (Fin n) ≤ V) :
    ∫ ξ, (uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 4
      ∂stdGauss (Fin n) ≤ (2 * a + √(4 * a ^ 2 + V ^ 2)) ^ 2 := by
  obtain ⟨-, hk⟩ := lipD_core hn hF A₁ A₂ c hτ
  have ha0 : 0 ≤ Xi4 A₁ A₂ c τ := by unfold Xi4; positivity
  have hV0 : 0 ≤ ∫ ξ, (uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 2
      ∂stdGauss (Fin n) := integral_nonneg fun ξ => sq_nonneg _
  have hX0 : 0 ≤ ∫ ξ, (uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 4
      ∂stdGauss (Fin n) := integral_nonneg fun ξ => by positivity
  refine quad_bound hX0 (ha0.trans ha) fun k hk0 => ?_
  have h1 := hk k hk0
  have h2 := pow_le_pow_left₀ hV0 hV 2
  have h3 := pow_le_pow_left₀ ha0 ha 2
  have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * k)
  linarith

/-- **The fourth moment**: `E(u − Eu)⁴ ≤ (2 + √5)²·Ξ₄²`. -/
theorem lipD_fourth (hn : 6 ≤ n) {F : (Fin m → ℝ) → ℝ} (hF : EuLip F 1)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun ξ => (uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 4)
      (stdGauss (Fin n)) ∧
    ∫ ξ, (uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 4
      ∂stdGauss (Fin n) ≤ (2 + √5) ^ 2 * Xi4 A₁ A₂ c τ ^ 2 := by
  refine ⟨(lipD_core hn hF A₁ A₂ c hτ).1, ?_⟩
  have ha0 : 0 ≤ Xi4 A₁ A₂ c τ := by unfold Xi4; positivity
  have h := lipD_fourth_sharp hn hF A₁ A₂ c hτ le_rfl
    ((lipD_var hn hF A₁ A₂ c hτ).trans (BstLean.Part153.XiS_le_Xi4 hn A₁ A₂ c hτ))
  have e : √(4 * Xi4 A₁ A₂ c τ ^ 2 + Xi4 A₁ A₂ c τ ^ 2) = √5 * Xi4 A₁ A₂ c τ := by
    rw [show 4 * Xi4 A₁ A₂ c τ ^ 2 + Xi4 A₁ A₂ c τ ^ 2 = 5 * Xi4 A₁ A₂ c τ ^ 2 by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq ha0]
  rw [e] at h
  calc _ ≤ (2 * Xi4 A₁ A₂ c τ + √5 * Xi4 A₁ A₂ c τ) ^ 2 := h
    _ = (2 + √5) ^ 2 * Xi4 A₁ A₂ c τ ^ 2 := by ring

/-- Chebyshev: `Pr(|u − E u| ≥ g) ≤ Ξ/g²`. -/
theorem lipD_cheb (hn : 6 ≤ n) {F : (Fin m → ℝ) → ℝ} (hF : EuLip F 1)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {g : ℝ} (hg : 0 < g) :
    (stdGauss (Fin n)).real
      {ξ | g ≤ |uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)|} ≤
      XiS A₁ A₂ c τ / g ^ 2 := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn1 : 1 ≤ n := by omega
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ, m₀ = ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n) := ⟨_, rfl⟩
  have hv := lipD_var hn hF A₁ A₂ c hτ
  rw [← hm₀] at hv ⊢
  have hum : Measurable (fun ξ => uD F A₁ A₂ c τ ξ - m₀) :=
    (measurable_uD hF A₁ A₂ c τ).sub_const _
  obtain ⟨B0, hB0, hB⟩ := uD_bdd hn1 hF A₁ A₂ c τ
  have hi : Integrable (fun ξ => (uD F A₁ A₂ c τ ξ - m₀) ^ 2) (stdGauss (Fin n)) :=
    Integrable.of_bound (hum.pow_const 2).aestronglyMeasurable ((B0 + |m₀|) ^ 2)
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _)
          ((abs_sub _ _).trans (add_le_add (hB ξ) le_rfl)) 2)
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := stdGauss (Fin n))
    (Filter.Eventually.of_forall fun ξ => sq_nonneg (uD F A₁ A₂ c τ ξ - m₀)) hi (g ^ 2)
  have hsub : {ξ | g ≤ |uD F A₁ A₂ c τ ξ - m₀|} ⊆
      {ξ | g ^ 2 ≤ (uD F A₁ A₂ c τ ξ - m₀) ^ 2} := fun ξ hξ => by
    have : g ^ 2 ≤ |uD F A₁ A₂ c τ ξ - m₀| ^ 2 := pow_le_pow_left₀ hg.le hξ 2
    rwa [sq_abs] at this
  have hmono := measureReal_mono (μ := stdGauss (Fin n)) hsub
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact (mul_le_mul_of_nonneg_left hmono (by positivity)).trans (hM.trans hv)

/-- Markov at the fourth moment, sharp form:
`Pr(|u − E u| ≥ g) ≤ (2a + √(4a² + V²))²/g⁴`, `a ≥ Ξ₄`, `V ≥ Var u`. -/
theorem lipD_markov4_sharp (hn : 6 ≤ n) {F : (Fin m → ℝ) → ℝ} (hF : EuLip F 1)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {a V : ℝ} (ha : Xi4 A₁ A₂ c τ ≤ a)
    (hV : ∫ ξ, (uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 2
      ∂stdGauss (Fin n) ≤ V) {g : ℝ} (hg : 0 < g) :
    (stdGauss (Fin n)).real
      {ξ | g ≤ |uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)|} ≤
      (2 * a + √(4 * a ^ 2 + V ^ 2)) ^ 2 / g ^ 4 := by
  have hi := (lipD_core hn hF A₁ A₂ c hτ).1
  have hv := lipD_fourth_sharp hn hF A₁ A₂ c hτ ha hV
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ, m₀ = ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← hm₀] at hv hi ⊢
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := stdGauss (Fin n))
    (Filter.Eventually.of_forall fun ξ =>
      (by positivity : 0 ≤ (uD F A₁ A₂ c τ ξ - m₀) ^ 4)) hi (g ^ 4)
  have hsub : {ξ | g ≤ |uD F A₁ A₂ c τ ξ - m₀|} ⊆
      {ξ | g ^ 4 ≤ (uD F A₁ A₂ c τ ξ - m₀) ^ 4} := fun ξ hξ => by
    have : g ^ 4 ≤ |uD F A₁ A₂ c τ ξ - m₀| ^ 4 := pow_le_pow_left₀ hg.le hξ 4
    rwa [Even.pow_abs (by decide)] at this
  have hmono := measureReal_mono (μ := stdGauss (Fin n)) hsub
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact (mul_le_mul_of_nonneg_left hmono (by positivity)).trans (hM.trans hv)

/-- Markov at the fourth moment: `Pr(|u − E u| ≥ g) ≤ (2 + √5)²·Ξ₄²/g⁴`. -/
theorem lipD_markov4 (hn : 6 ≤ n) {F : (Fin m → ℝ) → ℝ} (hF : EuLip F 1)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {g : ℝ} (hg : 0 < g) :
    (stdGauss (Fin n)).real
      {ξ | g ≤ |uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)|} ≤
      (2 + √5) ^ 2 * Xi4 A₁ A₂ c τ ^ 2 / g ^ 4 := by
  have ha0 : 0 ≤ Xi4 A₁ A₂ c τ := by unfold Xi4; positivity
  have h := lipD_markov4_sharp hn hF A₁ A₂ c hτ le_rfl
    ((lipD_var hn hF A₁ A₂ c hτ).trans (BstLean.Part153.XiS_le_Xi4 hn A₁ A₂ c hτ)) hg
  have e : √(4 * Xi4 A₁ A₂ c τ ^ 2 + Xi4 A₁ A₂ c τ ^ 2) = √5 * Xi4 A₁ A₂ c τ := by
    rw [show 4 * Xi4 A₁ A₂ c τ ^ 2 + Xi4 A₁ A₂ c τ ^ 2 = 5 * Xi4 A₁ A₂ c τ ^ 2 by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq ha0]
  rw [e] at h
  have e' : (2 * Xi4 A₁ A₂ c τ + √5 * Xi4 A₁ A₂ c τ) ^ 2 =
      (2 + √5) ^ 2 * Xi4 A₁ A₂ c τ ^ 2 := by ring
  rwa [e'] at h

/-! ## The directional component `v = √t·|b|·λ` -/

/-- `v(ξ) = √t·⟨h(x(ξ)), b/|b|⟩ = √t·|b|·λ(x)`, `t = 2/m`. -/
noncomputable def v1D (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (b : Fin m → ℝ) (ξ : Fin n → ℝ) : ℝ :=
  √(2 / (m : ℝ)) * √(normSq b) * lam b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))

/-- `φ₁(z) = ⟨z, b/|b|⟩`. -/
noncomputable def phi1D (b z : Fin m → ℝ) : ℝ := (z ⬝ᵥ b) / nrm b

lemma eulip_phi1D {b : Fin m → ℝ} (hb : 0 < normSq b) : EuLip (phi1D b) 1 := by
  intro x y
  have hN : 0 < nrm b := Real.sqrt_pos.mpr hb
  have e : phi1D b x - phi1D b y = ((x - y) ⬝ᵥ b) / nrm b := by
    unfold phi1D
    rw [sub_dotProduct]
    ring
  rw [e, abs_div, abs_of_pos hN, div_le_iff₀ hN, one_mul]
  exact BstLean.Part153.abs_dot_le_nrm (x - y) b

lemma v1_eq_phi1D {b : Fin m → ℝ} (hb : 0 < normSq b) (t : ℝ) (h : Fin m → ℝ) :
    √t * √(normSq b) * lam b h = phi1D b (√t • h) := by
  have hN : 0 < √(normSq b) := Real.sqrt_pos.mpr hb
  have e : lam b h = (h ⬝ᵥ b) / normSq b := rfl
  have e2 : normSq b = √(normSq b) ^ 2 := (Real.sq_sqrt hb.le).symm
  unfold phi1D nrm
  rw [e, smul_dotProduct, smul_eq_mul]
  generalize h ⬝ᵥ b = d
  rw [e2, Real.sqrt_sq hN.le]
  field_simp

lemma v1D_eq {b : Fin m → ℝ} (hb : 0 < normSq b) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    v1D A₁ A₂ c τ b = uD (phi1D b) A₁ A₂ c τ :=
  funext fun _ => v1_eq_phi1D hb _ _

lemma measurable_v1D {b : Fin m → ℝ} (hb : 0 < normSq b)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (v1D A₁ A₂ c τ b) := by
  rw [v1D_eq hb]; exact measurable_uD (eulip_phi1D hb) A₁ A₂ c τ

/-- **The variance of the directional component**: `Var_ξ v ≤ Ξ`. -/
theorem v1D_var (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {b : Fin m → ℝ} (hb : 0 < normSq b) :
    ∫ ξ, (v1D A₁ A₂ c τ b ξ - ∫ ζ, v1D A₁ A₂ c τ b ζ ∂stdGauss (Fin n)) ^ 2
      ∂stdGauss (Fin n) ≤ XiS A₁ A₂ c τ := by
  rw [v1D_eq hb]; exact lipD_var hn (eulip_phi1D hb) A₁ A₂ c hτ

/-- **The fourth moment of the directional component**: `E_ξ (v − E v)⁴ ≤ (2 + √5)²·Ξ₄²`. -/
theorem v1D_fourth (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {b : Fin m → ℝ} (hb : 0 < normSq b) :
    Integrable (fun ξ => (v1D A₁ A₂ c τ b ξ - ∫ ζ, v1D A₁ A₂ c τ b ζ ∂stdGauss (Fin n)) ^ 4)
      (stdGauss (Fin n)) ∧
    ∫ ξ, (v1D A₁ A₂ c τ b ξ - ∫ ζ, v1D A₁ A₂ c τ b ζ ∂stdGauss (Fin n)) ^ 4
      ∂stdGauss (Fin n) ≤ (2 + √5) ^ 2 * Xi4 A₁ A₂ c τ ^ 2 := by
  rw [v1D_eq hb]; exact lipD_fourth hn (eulip_phi1D hb) A₁ A₂ c hτ

/-- Chebyshev: `Pr(|v − E v| ≥ g) ≤ Ξ/g²`. -/
theorem v1D_cheb (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {b : Fin m → ℝ} (hb : 0 < normSq b) {g : ℝ}
    (hg : 0 < g) :
    (stdGauss (Fin n)).real
      {ξ | g ≤ |v1D A₁ A₂ c τ b ξ - ∫ ζ, v1D A₁ A₂ c τ b ζ ∂stdGauss (Fin n)|} ≤
      XiS A₁ A₂ c τ / g ^ 2 := by
  rw [v1D_eq hb]; exact lipD_cheb hn (eulip_phi1D hb) A₁ A₂ c hτ hg

/-- Markov at the fourth moment: `Pr(|v − E v| ≥ g) ≤ (2 + √5)²·Ξ₄²/g⁴`. -/
theorem v1D_markov4 (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {b : Fin m → ℝ}
    (hb : 0 < normSq b) {g : ℝ} (hg : 0 < g) :
    (stdGauss (Fin n)).real
      {ξ | g ≤ |v1D A₁ A₂ c τ b ξ - ∫ ζ, v1D A₁ A₂ c τ b ζ ∂stdGauss (Fin n)|} ≤
      (2 + √5) ^ 2 * Xi4 A₁ A₂ c τ ^ 2 / g ^ 4 := by
  rw [v1D_eq hb]; exact lipD_markov4 hn (eulip_phi1D hb) A₁ A₂ c hτ hg

/-- The sharp Markov form for `v`. -/
theorem v1D_markov4_sharp (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {b : Fin m → ℝ}
    (hb : 0 < normSq b) {a V : ℝ} (ha : Xi4 A₁ A₂ c τ ≤ a) (hV : XiS A₁ A₂ c τ ≤ V) {g : ℝ}
    (hg : 0 < g) :
    (stdGauss (Fin n)).real
      {ξ | g ≤ |v1D A₁ A₂ c τ b ξ - ∫ ζ, v1D A₁ A₂ c τ b ζ ∂stdGauss (Fin n)|} ≤
      (2 * a + √(4 * a ^ 2 + V ^ 2)) ^ 2 / g ^ 4 := by
  rw [v1D_eq hb]
  exact lipD_markov4_sharp hn (eulip_phi1D hb) A₁ A₂ c hτ ha
    ((lipD_var hn (eulip_phi1D hb) A₁ A₂ c hτ).trans hV) hg

/-! ## The residual scale `σ = √t·|res b h|` -/

/-- `σ(ξ) = √t·|res b h(x(ξ))|`, `t = 2/m` (`sig` of Part 134). -/
noncomputable def sigD (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (b : Fin m → ℝ) (ξ : Fin n → ℝ) : ℝ :=
  sig (2 / (m : ℝ)) b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))

/-- `φ₂(z) = |Π_b z|`. -/
noncomputable def phi2D (b z : Fin m → ℝ) : ℝ := nrm (res b z)

lemma res_sub_D (b x y : Fin m → ℝ) : res b x - res b y = res b (x - y) := by
  have e : ∑ j, (x j - y j) * b j = ∑ j, x j * b j - ∑ j, y j * b j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  ext j
  simp only [res, lam, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e]
  ring

lemma res_smul_D (b h : Fin m → ℝ) (s : ℝ) : res b (s • h) = s • res b h := by
  have e : ∑ j, s * h j * b j = s * ∑ j, h j * b j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  ext j
  simp only [res, lam, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e]
  ring

lemma nrm_res_le_D {b : Fin m → ℝ} (hb : 0 < normSq b) (h : Fin m → ℝ) :
    nrm (res b h) ≤ nrm h := by
  refine Real.sqrt_le_sqrt ?_
  rw [BstLean.Part136.normSq_res hb.ne']
  have h2 : 0 ≤ (∑ j, h j * b j) ^ 2 / normSq b := div_nonneg (sq_nonneg _) hb.le
  linarith

lemma eulip_phi2D {b : Fin m → ℝ} (hb : 0 < normSq b) : EuLip (phi2D b) 1 := by
  intro x y
  rw [one_mul]
  unfold phi2D
  refine (BstLean.Part153.abs_nrm_sub_le _ _).trans ?_
  rw [res_sub_D]
  exact nrm_res_le_D hb (x - y)

lemma sig_eq_phi2D (b : Fin m → ℝ) (t : ℝ) (h : Fin m → ℝ) :
    sig t b h = phi2D b (√t • h) := by
  unfold phi2D
  rw [res_smul_D, BstLean.Part153.nrm_smul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rfl

lemma sigD_eq (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ)
    (τ : ℝ) (b : Fin m → ℝ) : sigD A₁ A₂ c τ b = uD (phi2D b) A₁ A₂ c τ :=
  funext fun _ => sig_eq_phi2D b _ _

lemma sigD_nonneg (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (b : Fin m → ℝ) (ξ : Fin n → ℝ) : 0 ≤ sigD A₁ A₂ c τ b ξ :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- `σ² = t·|res b h|²`. -/
theorem sigD_sq (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (b : Fin m → ℝ) (ξ : Fin n → ℝ) :
    sigD A₁ A₂ c τ b ξ ^ 2 =
      2 / (m : ℝ) * normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) := by
  unfold sigD sig
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (normSq_nonneg _)]

lemma measurable_sigD {b : Fin m → ℝ} (hb : 0 < normSq b)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (sigD A₁ A₂ c τ b) := by
  rw [sigD_eq]; exact measurable_uD (eulip_phi2D hb) A₁ A₂ c τ

/-- **The variance of the residual scale**: `Var_ξ σ ≤ Ξ`. -/
theorem sigD_var (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {b : Fin m → ℝ} (hb : 0 < normSq b) :
    ∫ ξ, (sigD A₁ A₂ c τ b ξ - ∫ ζ, sigD A₁ A₂ c τ b ζ ∂stdGauss (Fin n)) ^ 2
      ∂stdGauss (Fin n) ≤ XiS A₁ A₂ c τ := by
  rw [sigD_eq]; exact lipD_var hn (eulip_phi2D hb) A₁ A₂ c hτ

/-- **The fourth moment of the residual scale**: `E_ξ (σ − E σ)⁴ ≤ (2 + √5)²·Ξ₄²`. -/
theorem sigD_fourth (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {b : Fin m → ℝ} (hb : 0 < normSq b) :
    Integrable (fun ξ => (sigD A₁ A₂ c τ b ξ - ∫ ζ, sigD A₁ A₂ c τ b ζ ∂stdGauss (Fin n)) ^ 4)
      (stdGauss (Fin n)) ∧
    ∫ ξ, (sigD A₁ A₂ c τ b ξ - ∫ ζ, sigD A₁ A₂ c τ b ζ ∂stdGauss (Fin n)) ^ 4
      ∂stdGauss (Fin n) ≤ (2 + √5) ^ 2 * Xi4 A₁ A₂ c τ ^ 2 := by
  rw [sigD_eq]; exact lipD_fourth hn (eulip_phi2D hb) A₁ A₂ c hτ

/-- Chebyshev: `Pr(|σ − E σ| ≥ g) ≤ Ξ/g²`. -/
theorem sigD_cheb (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {b : Fin m → ℝ} (hb : 0 < normSq b) {g : ℝ}
    (hg : 0 < g) :
    (stdGauss (Fin n)).real
      {ξ | g ≤ |sigD A₁ A₂ c τ b ξ - ∫ ζ, sigD A₁ A₂ c τ b ζ ∂stdGauss (Fin n)|} ≤
      XiS A₁ A₂ c τ / g ^ 2 := by
  rw [sigD_eq]; exact lipD_cheb hn (eulip_phi2D hb) A₁ A₂ c hτ hg

/-- Markov at the fourth moment: `Pr(|σ − E σ| ≥ g) ≤ (2 + √5)²·Ξ₄²/g⁴`. -/
theorem sigD_markov4 (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {b : Fin m → ℝ}
    (hb : 0 < normSq b) {g : ℝ} (hg : 0 < g) :
    (stdGauss (Fin n)).real
      {ξ | g ≤ |sigD A₁ A₂ c τ b ξ - ∫ ζ, sigD A₁ A₂ c τ b ζ ∂stdGauss (Fin n)|} ≤
      (2 + √5) ^ 2 * Xi4 A₁ A₂ c τ ^ 2 / g ^ 4 := by
  rw [sigD_eq]; exact lipD_markov4 hn (eulip_phi2D hb) A₁ A₂ c hτ hg

/-- The sharp Markov form for `σ`: `≤ (2a + √(4a² + V²))²/g⁴`, `a ≥ Ξ₄`, `V ≥ Ξ`. -/
theorem sigD_markov4_sharp (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {b : Fin m → ℝ}
    (hb : 0 < normSq b) {a V : ℝ} (ha : Xi4 A₁ A₂ c τ ≤ a) (hV : XiS A₁ A₂ c τ ≤ V) {g : ℝ}
    (hg : 0 < g) :
    (stdGauss (Fin n)).real
      {ξ | g ≤ |sigD A₁ A₂ c τ b ξ - ∫ ζ, sigD A₁ A₂ c τ b ζ ∂stdGauss (Fin n)|} ≤
      (2 * a + √(4 * a ^ 2 + V ^ 2)) ^ 2 / g ^ 4 := by
  rw [sigD_eq]
  exact lipD_markov4_sharp hn (eulip_phi2D hb) A₁ A₂ c hτ ha
    ((lipD_var hn (eulip_phi2D hb) A₁ A₂ c hτ).trans hV) hg

/-- **Pythagoras for the residual energy**: `t|res b h|² = t|h|² − (√t·|b|·λ)²`, `t = 2/m`. -/
theorem res_energy_eq {b : Fin m → ℝ} (hb : 0 < normSq b) (h : Fin m → ℝ) :
    2 / (m : ℝ) * normSq (res b h) =
      2 / (m : ℝ) * normSq h - (√(2 / (m : ℝ)) * √(normSq b) * lam b h) ^ 2 := by
  have e : lam b h = (∑ j, h j * b j) / normSq b := rfl
  have ht : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  rw [BstLean.Part136.normSq_res hb.ne', mul_pow, mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hb.le, e]
  field_simp

end BstLean.Part160

open BstLean.Part160 in
#print axioms lipD_var
open BstLean.Part160 in
#print axioms lipD_fourth_sharp
open BstLean.Part160 in
#print axioms lipD_fourth
open BstLean.Part160 in
#print axioms lipD_cheb
open BstLean.Part160 in
#print axioms lipD_markov4_sharp
open BstLean.Part160 in
#print axioms lipD_markov4
open BstLean.Part160 in
#print axioms v1D_var
open BstLean.Part160 in
#print axioms v1D_fourth
open BstLean.Part160 in
#print axioms v1D_cheb
open BstLean.Part160 in
#print axioms v1D_markov4
open BstLean.Part160 in
#print axioms v1D_markov4_sharp
open BstLean.Part160 in
#print axioms sigD_var
open BstLean.Part160 in
#print axioms sigD_fourth
open BstLean.Part160 in
#print axioms sigD_cheb
open BstLean.Part160 in
#print axioms sigD_markov4
open BstLean.Part160 in
#print axioms sigD_markov4_sharp
open BstLean.Part160 in
#print axioms sigD_sq
open BstLean.Part160 in
#print axioms res_energy_eq
