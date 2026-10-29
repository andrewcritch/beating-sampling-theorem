import BstLean.Part160Mass4
import BstLean.Part160Event

/-!
# Part 160 (file `Mass8`): eighth moments of `1`-Lipschitz functions of the hidden vector

Do not use `sorry`, `native_decide` or `axiom`.

One more step of the chain of `Part160Mass4`. `t = 2/m`, `x(ξ) = sphPt (c + τ ξ)`,
`u(ξ) = F(√t·h(x(ξ)))` (`uD`) for a `1`-Lipschitz `F`.

* `Xi8`: `Ξ₈ = t·τ²·(E_ξ[‖𝒥Π‖⁸/|y|⁸])^{1/4}`, the `L⁸` analogue of `Ξ₄`.
* `lipD_eighth_core`: `X₈ − X₄² ≤ 12 s X₈ + (4/s³) Ξ₈⁴` for every `s > 0`, with
  `X₈ = E(u − Eu)⁸`, `X₄ = E(u − Eu)⁴` (the Poincaré inequality with a pointwise Lipschitz
  constant for `(u − Eu)⁴`, and a pointwise Young inequality).
* `lipD_eighth`: `E(u − Eu)⁸ ≤ (C₄·a)⁴`, `C₄ = 1609/100`, for every `a ≥ Ξ₄`, `a ≥ Ξ₈`.
* `lipD_markov8`, `sigD_markov8`: `Pr(|u − Eu| ≥ g) ≤ (C₄ a)⁴/g⁸`.
* `Xi8_markov`: `Pr(Ξ₈ > M γ_A/n) ≤ (j_S² n/((n − 1 − 2P) M))^P`, `P ≥ 4`;
  `Xi8_numeric_16384`: `Pr(Ξ₈ > 1.1911 γ_A/n) ≤ 5·10⁻⁵`, `n ≥ 16 384`.
* `SXi8`, `measurableSet_SXi8`, `SXi8_charge`: the event for the framework of `Part160Event`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part148 (EuLip)
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm jacT XiS Xi4 nuA Xq jS)
open scoped ENNReal

section gen

variable {n m : ℕ}

/-- `Ξ₈ = t·τ²·(E_ξ[‖𝒥(x)Π_x‖_op⁸/|y|⁸])^{1/4}`. -/
noncomputable def Xi8 (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  2 / (m : ℝ) * τ ^ 2 * √(√(∫ ξ, opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 8 *
    (normSq (c + τ • ξ))⁻¹ ^ 4 ∂stdGauss (Fin n)))

lemma Xi8_nonneg (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) : 0 ≤ Xi8 A₁ A₂ c τ := by
  unfold Xi8; positivity

/-- The integrand of `Ξ₈` is integrable (`n ≥ 10`). -/
theorem integrable_Xi8 (hn : 10 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun ξ : Fin n → ℝ => opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 8 *
      (normSq (c + τ • ξ))⁻¹ ^ 4) (stdGauss (Fin n)) := by
  have hi := (BstLean.Part153.invMoment_le (p := 4) (by omega) c hτ).1
  refine Integrable.mono' (hi.const_mul ((opN A₂ * opN A₁) ^ 8))
    (((BstLean.Part153.measurable_opN_jacT_sj A₁ A₂ c τ).pow_const 8).mul
      ((BstLean.Part153.cont_ns c τ).measurable.inv.pow_const 4)).aestronglyMeasurable
    (ae_of_all _ fun ξ => ?_)
  have h0 : 0 ≤ (normSq (c + τ • ξ))⁻¹ ^ 4 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) h0)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (BstLean.Part152.opN_nonneg _)
    (BstLean.Part153.opN_jacT_le_sj A₁ A₂ (normSq_sphPt (by omega) _)) 8) h0

/-- `3x⁴ − 4x³y + y⁴ ≥ 0`. -/
lemma young34 (x y : ℝ) : 0 ≤ 3 * x ^ 4 - 4 * x ^ 3 * y + y ^ 4 := by
  have e : 3 * x ^ 4 - 4 * x ^ 3 * y + y ^ 4 = (x - y) ^ 2 * (2 * x ^ 2 + (x + y) ^ 2) := by ring
  rw [e]; positivity

/-- The increment of the fourth power: `|(a + d)⁴ − a⁴| ≤ r·(4|a|³ + 6|a|²r + 4|a|r² + r³)` if
`|d| ≤ r`. -/
lemma pow4_incr {a d r : ℝ} (hd : |d| ≤ r) :
    |(a + d) ^ 4 - a ^ 4| ≤ r * (4 * |a| ^ 3 + 6 * |a| ^ 2 * r + 4 * |a| * r ^ 2 + r ^ 3) := by
  have hr0 : 0 ≤ r := (abs_nonneg d).trans hd
  have hA := abs_nonneg a
  have hD := abs_nonneg d
  have e : (a + d) ^ 4 - a ^ 4 = d * (4 * a ^ 3 + 6 * a ^ 2 * d + 4 * a * d ^ 2 + d ^ 3) := by
    ring
  rw [e, abs_mul]
  have h1 : |4 * a ^ 3 + 6 * a ^ 2 * d + 4 * a * d ^ 2 + d ^ 3| ≤
      4 * |a| ^ 3 + 6 * |a| ^ 2 * |d| + 4 * |a| * |d| ^ 2 + |d| ^ 3 := by
    have t1 : |4 * a ^ 3| = 4 * |a| ^ 3 := by
      rw [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have t2 : |6 * a ^ 2 * d| = 6 * |a| ^ 2 * |d| := by
      rw [abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    have t3 : |4 * a * d ^ 2| = 4 * |a| * |d| ^ 2 := by
      rw [abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have t4 : |d ^ 3| = |d| ^ 3 := abs_pow _ _
    have s1 := abs_add_le (4 * a ^ 3 + 6 * a ^ 2 * d + 4 * a * d ^ 2) (d ^ 3)
    have s2 := abs_add_le (4 * a ^ 3 + 6 * a ^ 2 * d) (4 * a * d ^ 2)
    have s3 := abs_add_le (4 * a ^ 3) (6 * a ^ 2 * d)
    rw [t1, t2] at s3
    rw [t3] at s2
    rw [t4] at s1
    linarith
  have h2 : 4 * |a| ^ 3 + 6 * |a| ^ 2 * |d| + 4 * |a| * |d| ^ 2 + |d| ^ 3 ≤
      4 * |a| ^ 3 + 6 * |a| ^ 2 * r + 4 * |a| * r ^ 2 + r ^ 3 := by
    have p2 : |d| ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hD hd 2
    have p3 : |d| ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hD hd 3
    have q1 : 6 * |a| ^ 2 * |d| ≤ 6 * |a| ^ 2 * r :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    have q2 : 4 * |a| * |d| ^ 2 ≤ 4 * |a| * r ^ 2 :=
      mul_le_mul_of_nonneg_left p2 (by positivity)
    linarith
  exact mul_le_mul hd (h1.trans h2) (abs_nonneg _) hr0

/-- The core inequality of the eighth moment: for every `s > 0`,
`X₈ − X₄² ≤ 12 s·X₈ + (4/s³)·Ξ₈⁴`, with `X₈ = E(u − Eu)⁸`, `X₄ = E(u − Eu)⁴`. Also the
integrability of the eighth power. -/
theorem lipD_eighth_core (hn : 10 ≤ n) {F : (Fin m → ℝ) → ℝ} (hF : EuLip F 1)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun ξ => (uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 8)
      (stdGauss (Fin n)) ∧
    ∀ s : ℝ, 0 < s →
      ∫ ξ, (uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 8
          ∂stdGauss (Fin n) -
        (∫ ξ, (uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 4
          ∂stdGauss (Fin n)) ^ 2 ≤
      12 * s * ∫ ξ, (uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 8
          ∂stdGauss (Fin n) + 4 / s ^ 3 * Xi8 A₁ A₂ c τ ^ 4 := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn1 : 1 ≤ n := by omega
  have hn6 : 6 ≤ n := by omega
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
  have e8 : (fun ξ => (uD F A₁ A₂ c τ ξ - m₀) ^ 8) = fun ξ => u ξ ^ 8 := by rw [hu]
  have e4 : (fun ξ => (uD F A₁ A₂ c τ ξ - m₀) ^ 4) = fun ξ => u ξ ^ 4 := by rw [hu]
  rw [e8, e4]
  refine ⟨hpow 8, ?_⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : (Fin m → ℝ) → ℝ, φ = fun z => (F z - m₀) ^ 4 := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : (Fin m → ℝ) → ℝ, ℓ = fun z => 4 * |F z - m₀| ^ 3 := ⟨_, rfl⟩
  have hq : ∀ ξ, F (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) - m₀ = u ξ := by
    intro ξ
    rw [hu]
    rfl
  have hℓe : ∀ z, ℓ z = 4 * |F z - m₀| ^ 3 := fun z => by rw [hℓ]
  have hℓnn : ∀ z, 0 ≤ ℓ z := fun z => by rw [hℓe]; positivity
  have key : ∀ z z' : Fin m → ℝ, |φ z' - φ z| ≤
      nrm (z' - z) * (4 * |F z - m₀| ^ 3 + 6 * |F z - m₀| ^ 2 * nrm (z' - z) +
        4 * |F z - m₀| * nrm (z' - z) ^ 2 + nrm (z' - z) ^ 3) := by
    intro z z'
    have hd := eulip_nrm hF z' z
    have h := pow4_incr (a := F z - m₀) hd
    have e : φ z' - φ z = (F z - m₀ + (F z' - F z)) ^ 4 - (F z - m₀) ^ 4 := by
      rw [hφ]; ring
    rw [e]; exact h
  have hAbd : ∀ R : ℝ, ∀ z : Fin m → ℝ, nrm z ≤ R → |F z - m₀| ≤ |R| + |F 0| + |m₀| := by
    intro R z hz
    have h1 := eulip_nrm hF z 0
    rw [sub_zero] at h1
    have h2 := abs_sub (F z) m₀
    have h3 := le_abs_self R
    have h4 : |F z| ≤ |F z - F 0| + |F 0| := by
      have := abs_add_le (F z - F 0) (F 0)
      rwa [sub_add_cancel] at this
    linarith
  have S := BstLean.Part153.lemmaS_loc_sl hn6 A₁ A₂ c hτ (φ := φ) (ℓ := ℓ)
    (by
      intro R
      obtain ⟨B, hBd⟩ : ∃ B : ℝ, B = |R| + |F 0| + |m₀| := ⟨_, rfl⟩
      have hB0' : 0 ≤ B := by rw [hBd]; positivity
      refine ⟨4 * B ^ 3 + 6 * B ^ 2 * (2 * |R|) + 4 * B * (2 * |R|) ^ 2 + (2 * |R|) ^ 3,
        by positivity, fun x _ y _ hx hy => ?_⟩
      have h1 := key y x
      have hA : |F y - m₀| ≤ B := by rw [hBd]; exact hAbd R y hy
      have hA0 := abs_nonneg (F y - m₀)
      have hr0 := BstLean.Part153.nrm_nonneg (x - y)
      have h3 : nrm (x - y) ≤ 2 * |R| := by
        have e : x - y = x + (-1 : ℝ) • y := by
          ext j; simp [sub_eq_add_neg]
        have h4 := BstLean.Part153.nrm_add_le x ((-1 : ℝ) • y)
        rw [BstLean.Part153.nrm_smul, abs_neg, abs_one, one_mul] at h4
        rw [e]
        have := le_abs_self R
        linarith
      have hmono : 4 * |F y - m₀| ^ 3 + 6 * |F y - m₀| ^ 2 * nrm (x - y) +
          4 * |F y - m₀| * nrm (x - y) ^ 2 + nrm (x - y) ^ 3 ≤
          4 * B ^ 3 + 6 * B ^ 2 * (2 * |R|) + 4 * B * (2 * |R|) ^ 2 + (2 * |R|) ^ 3 := by
        gcongr
      rw [mul_comm] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right hmono hr0))
    (by
      intro z _ δ hδ
      obtain ⟨A, hA⟩ : ∃ A : ℝ, A = |F z - m₀| := ⟨_, rfl⟩
      have hA0 : 0 ≤ A := by rw [hA]; exact abs_nonneg _
      have hK : 0 < 6 * A ^ 2 + 4 * A + 1 := by positivity
      refine ⟨min 1 (δ / (6 * A ^ 2 + 4 * A + 1)), lt_min one_pos (div_pos hδ hK),
        fun z' _ hz' => ?_⟩
      have h1 := key z z'
      rw [← hA] at h1
      have hr0 := BstLean.Part153.nrm_nonneg (z' - z)
      have hr1 : nrm (z' - z) < 1 := lt_of_lt_of_le hz' (min_le_left _ _)
      have hr2 : nrm (z' - z) < δ / (6 * A ^ 2 + 4 * A + 1) :=
        lt_of_lt_of_le hz' (min_le_right _ _)
      have hr3 : nrm (z' - z) * (6 * A ^ 2 + 4 * A + 1) ≤ δ :=
        ((lt_div_iff₀ hK).mp hr2).le
      have hsq : nrm (z' - z) ^ 2 ≤ nrm (z' - z) := by nlinarith
      have hcu : nrm (z' - z) ^ 3 ≤ nrm (z' - z) := by nlinarith
      have hbr : 4 * A ^ 3 + 6 * A ^ 2 * nrm (z' - z) + 4 * A * nrm (z' - z) ^ 2 +
          nrm (z' - z) ^ 3 ≤ ℓ z + δ := by
        rw [hℓe, ← hA]
        have q2 : 4 * A * nrm (z' - z) ^ 2 ≤ 4 * A * nrm (z' - z) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        nlinarith
      rw [mul_comm] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right hbr hr0))
    (fun z _ => hℓnn z)
    (by
      have e : (fun ξ : Fin n → ℝ => ℓ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ)))) =
          fun ξ => 4 * |u ξ| ^ 3 := by
        funext ξ; rw [hℓe, hq]
      rw [e]
      exact ((continuous_abs.measurable.comp hum).pow_const 3).const_mul 4)
    (by
      intro R
      refine ⟨4 * (|R| + |F 0| + |m₀|) ^ 3, fun z _ hz => ?_⟩
      rw [hℓe]
      have := pow_le_pow_left₀ (abs_nonneg _) (hAbd R z hz) 3
      linarith)
  obtain ⟨G, hG⟩ : ∃ G : (Fin n → ℝ) → ℝ, G = fun ξ =>
      opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹ := ⟨_, rfl⟩
  have eφ' : ∀ ξ : Fin n → ℝ, φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) = u ξ ^ 4 := by
    intro ξ; rw [hφ]; change (_ - m₀) ^ 4 = _; rw [hq]
  have eℓ : (fun ξ : Fin n → ℝ => ℓ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
      (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹)) =
      fun ξ => 16 * u ξ ^ 6 * G ξ := by
    funext ξ
    rw [hℓe, hq, hG]
    have e6 : (|u ξ| ^ 3) ^ 2 = u ξ ^ 6 := by
      rw [← pow_mul, show 3 * 2 = 6 from rfl, Even.pow_abs (by decide)]
    rw [mul_pow, e6]
    norm_num
  obtain ⟨S1, S2, S3⟩ := S
  simp only [eφ'] at S2 S3
  rw [eℓ] at S1 S3
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∫ ξ, u ξ ^ 4 ∂stdGauss (Fin n) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∫ ξ, u ξ ^ 8 ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← hW] at S3
  rw [← hX, ← hW]
  have hvar : ∫ ξ, (u ξ ^ 4 - W) ^ 2 ∂stdGauss (Fin n) = X - W ^ 2 := by
    have e : (fun ξ => (u ξ ^ 4 - W) ^ 2) = fun ξ => u ξ ^ 8 - 2 * W * u ξ ^ 4 + W ^ 2 :=
      funext fun ξ => by ring
    have h2 : Integrable (fun ξ => 2 * W * u ξ ^ 4) (stdGauss (Fin n)) := (hpow 4).const_mul _
    have h3 : Integrable (fun ξ => u ξ ^ 8 - 2 * W * u ξ ^ 4) (stdGauss (Fin n)) :=
      (hpow 8).sub h2
    rw [e, integral_add h3 (integrable_const _), integral_sub (hpow 8) h2,
      integral_const_mul, integral_const, ← hW, ← hX]
    rw [show (stdGauss (Fin n)).real Set.univ = 1 from by simp, one_smul]
    ring
  rw [hvar] at S3
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 2 / (m : ℝ) * τ ^ 2 := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  rw [← hT] at S3
  have hGi := integrable_Xi8 hn A₁ A₂ c hτ
  have eG4 : (fun ξ : Fin n → ℝ => opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 8 *
      (normSq (c + τ • ξ))⁻¹ ^ 4) = fun ξ => G ξ ^ 4 := by
    funext ξ; rw [hG]; ring
  rw [eG4] at hGi
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = ∫ ξ, G ξ ^ 4 ∂stdGauss (Fin n) := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by rw [hY]; exact integral_nonneg fun ξ => by positivity
  have ha4 : Xi8 A₁ A₂ c τ ^ 4 = T ^ 4 * Y := by
    unfold Xi8
    rw [eG4, ← hY, ← hT, mul_pow]
    have : √(√Y) ^ 4 = Y := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
        Real.sq_sqrt hY0]
    rw [this]
  intro s hs0
  have hpt : ∀ ξ, T * (16 * u ξ ^ 6 * G ξ) ≤
      12 * s * u ξ ^ 8 + 4 / s ^ 3 * T ^ 4 * G ξ ^ 4 := by
    intro ξ
    have h := young34 (u ξ ^ 2) (T * G ξ / s)
    have e : 12 * s * u ξ ^ 8 + 4 / s ^ 3 * T ^ 4 * G ξ ^ 4 - T * (16 * u ξ ^ 6 * G ξ) =
        4 * s * (3 * (u ξ ^ 2) ^ 4 - 4 * (u ξ ^ 2) ^ 3 * (T * G ξ / s) + (T * G ξ / s) ^ 4) := by
      field_simp
      ring
    have : 0 ≤ 4 * s * (3 * (u ξ ^ 2) ^ 4 - 4 * (u ξ ^ 2) ^ 3 * (T * G ξ / s) +
        (T * G ξ / s) ^ 4) := mul_nonneg (by positivity) h
    linarith
  have hint : T * ∫ ξ, 16 * u ξ ^ 6 * G ξ ∂stdGauss (Fin n) ≤
      12 * s * X + 4 / s ^ 3 * T ^ 4 * Y := by
    rw [← integral_const_mul, hX, hY, ← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hpow 8).const_mul _) (hGi.const_mul _)]
    exact integral_mono (S1.const_mul _) (((hpow 8).const_mul _).add (hGi.const_mul _)) hpt
  have hmain : X - W ^ 2 ≤ 12 * s * X + 4 / s ^ 3 * T ^ 4 * Y := S3.trans hint
  rw [ha4]
  linarith

/-- `(2 + √5)⁴ ≤ 323`. -/
lemma c2_pow4_le : ((2 + √5) ^ 2) ^ 2 ≤ 323 := by
  have h5 : √5 ≤ 22361 / 10000 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √5 := Real.sqrt_nonneg _
  have h2 : (2 + √5) ^ 2 ≤ (2 + 22361 / 10000) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h3 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (2 + √5) ^ 2) h2 2
  refine h3.trans (by norm_num)

/-- **The eighth moment**: `E(u − Eu)⁸ ≤ (C₄·a)⁴` with `C₄ = 1609/100`, for every `a ≥ Ξ₄`,
`a ≥ Ξ₈`. -/
theorem lipD_eighth (hn : 10 ≤ n) {F : (Fin m → ℝ) → ℝ} (hF : EuLip F 1)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {a : ℝ} (ha4 : Xi4 A₁ A₂ c τ ≤ a)
    (ha8 : Xi8 A₁ A₂ c τ ≤ a) :
    ∫ ξ, (uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 8
      ∂stdGauss (Fin n) ≤ (1609 / 100 * a) ^ 4 := by
  obtain ⟨-, hk⟩ := lipD_eighth_core hn hF A₁ A₂ c hτ
  have h4 := (lipD_fourth (by omega) hF A₁ A₂ c hτ).2
  have hX4 : 0 ≤ Xi4 A₁ A₂ c τ := by unfold Xi4; positivity
  have hX8 := Xi8_nonneg A₁ A₂ c τ
  have ha0 : 0 ≤ a := hX4.trans ha4
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∫ ξ, (uD F A₁ A₂ c τ ξ -
      ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 4 ∂stdGauss (Fin n) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∫ ξ, (uD F A₁ A₂ c τ ξ -
      ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)) ^ 8 ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← hW] at h4 hk
  rw [← hX] at hk ⊢
  have hW0 : 0 ≤ W := by rw [hW]; exact integral_nonneg fun ξ => by positivity
  have h1 := hk (1 / 16) (by norm_num)
  have hWa : W ≤ (2 + √5) ^ 2 * a ^ 2 :=
    h4.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX4 ha4 2) (by positivity))
  have hW2 : W ^ 2 ≤ 323 * a ^ 4 := by
    have := pow_le_pow_left₀ hW0 hWa 2
    have e : ((2 + √5) ^ 2 * a ^ 2) ^ 2 = ((2 + √5) ^ 2) ^ 2 * a ^ 4 := by ring
    rw [e] at this
    exact this.trans (mul_le_mul_of_nonneg_right c2_pow4_le (by positivity))
  have h8 : Xi8 A₁ A₂ c τ ^ 4 ≤ a ^ 4 := pow_le_pow_left₀ hX8 ha8 4
  have e2 : (1609 / 100 * a) ^ 4 = (1609 / 100 : ℝ) ^ 4 * a ^ 4 := by ring
  rw [e2]
  have ha4' : 0 ≤ a ^ 4 := by positivity
  norm_num at h1 ⊢
  nlinarith

/-- Markov at the eighth moment: `Pr(|u − Eu| ≥ g) ≤ (C₄ a)⁴/g⁸`, `C₄ = 1609/100`,
`a ≥ Ξ₄`, `a ≥ Ξ₈`. -/
theorem lipD_markov8 (hn : 10 ≤ n) {F : (Fin m → ℝ) → ℝ} (hF : EuLip F 1)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {a : ℝ} (ha4 : Xi4 A₁ A₂ c τ ≤ a)
    (ha8 : Xi8 A₁ A₂ c τ ≤ a) {g : ℝ} (hg : 0 < g) :
    (stdGauss (Fin n)).real
      {ξ | g ≤ |uD F A₁ A₂ c τ ξ - ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n)|} ≤
      (1609 / 100 * a) ^ 4 / g ^ 8 := by
  have hi := (lipD_eighth_core hn hF A₁ A₂ c hτ).1
  have hv := lipD_eighth hn hF A₁ A₂ c hτ ha4 ha8
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ, m₀ = ∫ ζ, uD F A₁ A₂ c τ ζ ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← hm₀] at hv hi ⊢
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := stdGauss (Fin n))
    (Filter.Eventually.of_forall fun ξ =>
      (by positivity : 0 ≤ (uD F A₁ A₂ c τ ξ - m₀) ^ 8)) hi (g ^ 8)
  have hsub : {ξ | g ≤ |uD F A₁ A₂ c τ ξ - m₀|} ⊆
      {ξ | g ^ 8 ≤ (uD F A₁ A₂ c τ ξ - m₀) ^ 8} := fun ξ hξ => by
    have : g ^ 8 ≤ |uD F A₁ A₂ c τ ξ - m₀| ^ 8 := pow_le_pow_left₀ hg.le hξ 8
    rwa [Even.pow_abs (by decide)] at this
  have hmono := measureReal_mono (μ := stdGauss (Fin n)) hsub
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact (mul_le_mul_of_nonneg_left hmono (by positivity)).trans (hM.trans hv)

/-- The eighth-moment tail for `σ = √t·|res b h|`:
`Pr(|σ − Eσ| ≥ g) ≤ (C₄ a)⁴/g⁸`, `C₄ = 1609/100`, `a ≥ Ξ₄`, `a ≥ Ξ₈`. -/
theorem sigD_markov8 (hn : 10 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {b : Fin m → ℝ}
    (hb : 0 < normSq b) {a : ℝ} (ha4 : Xi4 A₁ A₂ c τ ≤ a) (ha8 : Xi8 A₁ A₂ c τ ≤ a)
    {g : ℝ} (hg : 0 < g) :
    (stdGauss (Fin n)).real
      {ξ | g ≤ |sigD A₁ A₂ c τ b ξ - ∫ ζ, sigD A₁ A₂ c τ b ζ ∂stdGauss (Fin n)|} ≤
      (1609 / 100 * a) ^ 4 / g ^ 8 := by
  rw [sigD_eq]; exact lipD_markov8 hn (eulip_phi2D hb) A₁ A₂ c hτ ha4 ha8 hg

end gen

/-! ## The event of `Ξ₈` -/

section event

variable {n : ℕ}

/-- `Ξ₈^P ≤ (t·τ²)^P·E_ξ X^P` for `P ≥ 4`. -/
lemma ofReal_Xi8_pow_le {P : ℕ} (hP : 4 ≤ P)
    (θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ)
    (τ : ℝ) :
    ENNReal.ofReal (Xi8 θ.1 θ.2 c τ) ^ P ≤ ENNReal.ofReal (2 / ((mA n : ℕ) : ℝ) * τ ^ 2) ^ P *
      ∫⁻ ξ, ENNReal.ofReal (Xq θ c τ ξ ^ P) ∂stdGauss (Fin n) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hmeas : Measurable (fun ξ : Fin n → ℝ => Xq θ c τ ξ) := by
    have hf : Measurable (fun ξ : Fin n → ℝ => (θ, ξ)) := measurable_const.prodMk measurable_id
    have h := (BstLean.Part153.measurable_Xq_joint c τ).comp hf
    simpa only [Function.comp_def] using h
  have e : (fun ξ : Fin n → ℝ => opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 8 *
      (normSq (c + τ • ξ))⁻¹ ^ 4) = fun ξ => Xq θ c τ ξ ^ 4 := by
    funext ξ; unfold Xq; ring
  unfold Xi8
  rw [e, ENNReal.ofReal_mul (by positivity), mul_pow]
  refine mul_le_mul_right ?_ _
  have h0 : 0 ≤ ∫ ξ, Xq θ c τ ξ ^ 4 ∂stdGauss (Fin n) :=
    integral_nonneg fun ξ => by positivity
  have h1 : ENNReal.ofReal (∫ ξ, Xq θ c τ ξ ^ 4 ∂stdGauss (Fin n)) ≤
      ∫⁻ ξ, ENNReal.ofReal (Xq θ c τ ξ ^ 4) ∂stdGauss (Fin n) :=
    BstLean.Part153.ofReal_integral_le_lintegral fun ξ => by positivity
  have h2 := BstLean.Part153.lp_mono_nat (μ := stdGauss (Fin n)) hmeas
    (BstLean.Part153.Xq_nonneg θ c τ) (q := 4) (P := P) (by norm_num) hP
  simp only [Nat.cast_ofNat] at h2
  have h3 : ENNReal.ofReal (√(√(∫ ξ, Xq θ c τ ξ ^ 4 ∂stdGauss (Fin n)))) ≤
      (∫⁻ ξ, ENNReal.ofReal (Xq θ c τ ξ ^ P) ∂stdGauss (Fin n)) ^ (1 / (P : ℝ)) := by
    have e4 : √(√(∫ ξ, Xq θ c τ ξ ^ 4 ∂stdGauss (Fin n))) =
        (∫ ξ, Xq θ c τ ξ ^ 4 ∂stdGauss (Fin n)) ^ ((1 : ℝ) / 4) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul h0]
      norm_num
    rw [e4, ← ENNReal.ofReal_rpow_of_nonneg h0 (by norm_num)]
    exact (ENNReal.rpow_le_rpow h1 (by norm_num)).trans h2
  calc ENNReal.ofReal (√(√(∫ ξ, Xq θ c τ ξ ^ 4 ∂stdGauss (Fin n)))) ^ P
      ≤ ((∫⁻ ξ, ENNReal.ofReal (Xq θ c τ ξ ^ P) ∂stdGauss (Fin n)) ^ (1 / (P : ℝ))) ^ P :=
        pow_le_pow_left' h3 P
    _ = _ := BstLean.Part152.enn_root_pow _ (by omega)

/-- **The Markov step for `Ξ₈`** (`P ≥ 4`, constant `jS`). -/
theorem Xi8_markov {P : ℕ} (hP : 4 ≤ P) (hnP : 2 * P + 1 < n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) {M : ℝ} (hM : 0 < M) {η : ℝ} (hη : 0 ≤ η) :
    (nuA n).real {θ | M * (2 / (n : ℝ)) / n < Xi8 θ.1 θ.2 c τ} ≤
      (jS n P η ^ 2 * n / (((n : ℝ) - 1 - 2 * P) * M)) ^ P :=
  BstLean.Part153.markov_Xi (by omega) hnP c hτ (BstLean.Part153.jS_nonneg n P η)
    (fun _ hx => BstLean.Part153.lemmaPP_i_sharp (by omega) (by omega) hη hx)
    (fun θ => Xi8 θ.1 θ.2 c τ) (fun θ => ofReal_Xi8_pow_le hP θ c τ) hM

/-- **The numeric form**: for `n ≥ 16384`, `Pr(Ξ₈ > (11911/10000)·γ_A/n) ≤ 5·10⁻⁵`
(`P = 200`, `η = 6/1000`, as `lemmaPP_numeric_16384`). -/
theorem Xi8_numeric_16384 (hn : 16384 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real {θ | (11911 / 10000 : ℝ) * (2 / (n : ℝ)) / n < Xi8 θ.1 θ.2 c τ} ≤
      5 / 100000 := by
  have hnr : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have h := Xi8_markov (n := n) (P := 200) (by norm_num) (by omega) c hτ
    (M := 11911 / 10000) (by norm_num) (η := 6 / 1000) (by norm_num)
  refine h.trans ?_
  rw [show ((200 : ℕ) : ℝ) = 200 by norm_num]
  have hj := BstLean.Part153.jS_200_le_16384 hn
  have hj0 := BstLean.Part153.jS_nonneg n 200 (6 / 1000)
  have hj2 : jS n 200 (6 / 1000) ^ 2 ≤ (10488 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hj0 hj 2
  have hd : (0 : ℝ) < ((n : ℝ) - 1 - 2 * 200) * (11911 / 10000) := by
    have : (0 : ℝ) < (n : ℝ) - 1 - 2 * 200 := by linarith
    positivity
  have hratio : jS n 200 (6 / 1000) ^ 2 * n / (((n : ℝ) - 1 - 2 * 200) * (11911 / 10000)) ≤
      951 / 1000 := by
    rw [div_le_iff₀ hd]
    refine (mul_le_mul_of_nonneg_right hj2 (by linarith)).trans ?_
    norm_num
    linarith
  have hr0 : 0 ≤ jS n 200 (6 / 1000) ^ 2 * n / (((n : ℝ) - 1 - 2 * 200) * (11911 / 10000)) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) hd.le
  exact (pow_le_pow_left₀ hr0 hratio 200).trans BstLean.Part153.pow_951_le

/-- The good set of `Ξ₈`, as a set of `((c, τ), (A₁, A₂))`. -/
def SXi8 (n : ℕ) : Set (AgFam n) :=
  {x | Xi8 x.2.1 x.2.2 x.1.1 x.1.2 ≤ 11911 / 10000 * (2 / (n : ℝ)) / n}

/-- `((c, τ), (A₁, A₂)) ↦ Ξ₈` is measurable. -/
lemma measurable_Xi8_joint :
    Measurable (fun x : AgFam n => Xi8 x.2.1 x.2.2 x.1.1 x.1.2) := by
  have hy : Measurable (fun q : AgFam n × (Fin n → ℝ) => q.1.1.1 + q.1.1.2 • q.2) :=
    (measurable_fst.comp (measurable_fst.comp measurable_fst)).add
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).smul measurable_snd)
  have hJ : Measurable (fun q : AgFam n × (Fin n → ℝ) =>
      opN (jacT q.1.2.1 q.1.2.2 (sphPt (q.1.1.1 + q.1.1.2 • q.2)))) := by
    have h := (BstLean.Part153.measurable_opN_jacT_joint (n := n) (m := mA n)
      (m₂ := mA n)).comp
      ((measurable_snd.comp measurable_fst).prodMk (measurable_sphPt.comp hy))
    simpa only [Function.comp_def] using h
  have hF : Measurable (fun q : AgFam n × (Fin n → ℝ) =>
      opN (jacT q.1.2.1 q.1.2.2 (sphPt (q.1.1.1 + q.1.1.2 • q.2))) ^ 8 *
        (normSq (q.1.1.1 + q.1.1.2 • q.2))⁻¹ ^ 4) :=
    (hJ.pow_const 8).mul (((measurable_normSq.comp hy).inv).pow_const 4)
  unfold Xi8
  exact (((measurable_snd.comp measurable_fst).pow_const 2).const_mul _).mul
    ((hF.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable.sqrt.sqrt)

theorem measurableSet_SXi8 (n : ℕ) : MeasurableSet (SXi8 n) :=
  measurableSet_le measurable_Xi8_joint measurable_const

/-- **The charge of the event of `Ξ₈`**: `≤ 5·10⁻⁵` for every `(c, τ)` with `τ > 0`,
`n ≥ 16384`. -/
theorem SXi8_charge (hn : 16384 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SXi8 n} ≤ 5 / 100000 := by
  have h := Xi8_numeric_16384 hn c hτ
  have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      ((c, τ), θ) ∉ SXi8 n} =
      {θ | (11911 / 10000 : ℝ) * (2 / (n : ℝ)) / n < Xi8 θ.1 θ.2 c τ} := by
    ext θ
    show ¬ (Xi8 θ.1 θ.2 c τ ≤ 11911 / 10000 * (2 / (n : ℝ)) / n) ↔ _
    exact not_le
  rw [e]; exact h

lemma mem_SXi8 {c : Fin n → ℝ} {τ : ℝ} {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ}
    {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ} (h : ((c, τ), (A₁, A₂)) ∈ SXi8 n) :
    Xi8 A₁ A₂ c τ ≤ 11911 / 10000 * (2 / (n : ℝ)) / n := h

end event

end BstLean.Part160

open BstLean.Part160 in
#print axioms integrable_Xi8
open BstLean.Part160 in
#print axioms lipD_eighth_core
open BstLean.Part160 in
#print axioms lipD_eighth
open BstLean.Part160 in
#print axioms lipD_markov8
open BstLean.Part160 in
#print axioms sigD_markov8
open BstLean.Part160 in
#print axioms Xi8_markov
open BstLean.Part160 in
#print axioms Xi8_numeric_16384
open BstLean.Part160 in
#print axioms measurableSet_SXi8
open BstLean.Part160 in
#print axioms SXi8_charge
