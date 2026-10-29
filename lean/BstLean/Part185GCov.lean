import BstLean.Part185GW
import BstLean.Part182Cov21

/-!
# Part 185 (file `GCov`): the covariance bound at `n ≥ 17 000` for `λ = 0.645` (copy of Part 182
`Cov21` and `Cov21M`)

No proof is left open; no `native_decide` or `axiom` is used.

* `rminus_ltF17`, `Ew_le_F17` (`τ²E|y|⁻² ≤ 1.0207 θ/n`).
* `GeoT17 n`, **`geoT17_holds`**: for `n ≥ 17 000` every pair of `Γ(5, 14, 8)` in the window has
  `0.370 ≤ x·x' ≤ 0.655` (margins ≈ 0.004 at the crude bounds).
* `SCovT17 n`, **`SCovT17_ret_charge`** (charge `10⁻⁵` given `TI_hyp n 0.370 0.655 0.645 10⁻¹⁸`).
* **`Dq_TI17`**, **`cov_TI17`**: `N_cov = 0.645·1.0207·θ_hi + 1.116·1.0207·θ_hi·0.003711` on
  `SXM17 ∩ SCovT17`.
-/

namespace BstLean.Part183.F17

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152 BstLean.Part157 BstLean.Part160
open BstLean.Part153 (nrm jacT Xi4 nuA)
open BstLean.Part182

variable {n : ℕ}

/-- `r₋ < 1` (indeed `≤ 0.061`) on the window, for the wide parameters `(t₀, z₀) = (5, 14)`. -/
lemma rminus_ltF17 (hn : 17000 ≤ n) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 528 / 1000) :
    2 * 5 * √(θ * (1 - θ) / n) + 2 * θ * √(14 / n) < 1 := by
  have hnR : (17000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 : √(θ * (1 - θ) / n) ≤ 1 / 260 := by
    refine sqrt_le_of_sq' (by norm_num) ?_
    rw [div_le_iff₀ hn0]
    have hq : θ * (1 - θ) ≤ 1 / 4 := by nlinarith [sq_nonneg (θ - 1 / 2)]
    nlinarith
  have h2 : √((14 : ℝ) / n) ≤ 287 / 10000 := by
    refine sqrt_le_of_sq' (by norm_num) ?_
    rw [div_le_iff₀ hn0]
    nlinarith
  have h3 : 0 ≤ √((14 : ℝ) / n) := Real.sqrt_nonneg _
  nlinarith

/-- **`τ²·E|y|⁻² ≤ 1.0186·θ/n`** for `n ≥ 22 000` and `0.46 ≤ θ ≤ 0.528`. -/
theorem Ew_le_F17 (hn : 17000 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000) :
    τ ^ 2 * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ∂stdGauss (Fin n) ≤ 10207 / 10000 * (thetaC c τ / n) := by
  have hP : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hnR : (17000 : ℝ) ≤ n := by exact_mod_cast hn
  set B := 10207 / 10000 * (thetaC c τ / n) with hB
  have hB0 : 0 < B := by
    rw [hB]; have : (0 : ℝ) < n := by linarith
    have : 0 < thetaC c τ := by linarith
    positivity
  have hW := W20_le_F17 hn c hτ hθ0 hθ1
  rw [← hB] at hW
  -- integrability
  obtain ⟨hi1, -⟩ := BstLean.Part153.invMoment_one_le (by omega) c hτ
  obtain ⟨hi20, -⟩ := BstLean.Part153.invMoment_le (p := 20) (by omega) c hτ
  have hf1 : Integrable (fun ξ : Fin n → ℝ => τ ^ 2 * (normSq (c + τ • ξ))⁻¹) (stdGauss (Fin n)) :=
    hi1.const_mul _
  have hf20 : Integrable (fun ξ : Fin n → ℝ => (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ 20)
      (stdGauss (Fin n)) := by
    have := hi20.const_mul ((τ ^ 2) ^ 20)
    refine this.congr (ae_of_all _ fun ξ => ?_)
    show (τ ^ 2) ^ 20 * (normSq (c + τ • ξ))⁻¹ ^ 20 = (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ 20
    rw [mul_pow]
  -- pointwise: w ≤ B·((w/B)²⁰/20 + 19/20)
  have hpt : ∀ ξ : Fin n → ℝ, τ ^ 2 * (normSq (c + τ • ξ))⁻¹ ≤
      (1 / 20 / B ^ 19) * (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ 20 + 19 / 20 * B := by
    intro ξ
    have hw0 : 0 ≤ τ ^ 2 * (normSq (c + τ • ξ))⁻¹ :=
      mul_nonneg (sq_nonneg _) (inv_nonneg.2 (Finset.sum_nonneg fun i _ => sq_nonneg _))
    have h := BstLean.Part181.xq_pt (q := 1) (by norm_num) (div_nonneg hw0 hB0.le)
    simp only [pow_one, Nat.cast_one] at h
    have e : (1 / 20 / B ^ 19) * (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ 20 + 19 / 20 * B =
        B * (1 / 20 * ((τ ^ 2 * (normSq (c + τ • ξ))⁻¹) / B) ^ 20 + (1 - 1 / 20)) := by
      field_simp
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h hB0.le
    rwa [mul_div_cancel₀ _ hB0.ne'] at this
  have hint := integral_mono hf1 ((hf20.const_mul _).add (integrable_const _)) hpt
  simp only [Pi.add_apply] at hint
  rw [integral_add (hf20.const_mul _) (integrable_const _), integral_const_mul, integral_const,
    probReal_univ, one_smul, integral_const_mul] at hint
  have hW' : ∫ ξ, (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ 20 ∂stdGauss (Fin n) ≤ B ^ 20 := hW
  have h2 : (1 / 20 / B ^ 19) * ∫ ξ, (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ 20 ∂stdGauss (Fin n) ≤
      B / 20 := by
    calc (1 / 20 / B ^ 19) * ∫ ξ, (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ 20 ∂stdGauss (Fin n)
        ≤ (1 / 20 / B ^ 19) * B ^ 20 := mul_le_mul_of_nonneg_left hW' (by positivity)
      _ = B / 20 := by field_simp
  linarith

/-- The geometry hypothesis of the window: every pair of `Γ(5, 14, 8)` has `0.383 ≤ x·x' ≤ 0.641`. -/
def GeoT17 (n : ℕ) : Prop :=
  ∀ (c : Fin n → ℝ) (τ : ℝ), 0 < τ → winT c τ → ∀ p ∈ GammaS c 5 14 8,
    370 / 1000 ≤ sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ∧
      sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ≤ 655 / 1000

/-- The arithmetic core: upper and lower window bounds in the variables
`θ`, `u = 1/√n`, `R1 = √(θ(1−θ)/n)`, `R2 = √(14/n)`, `B = √(θ/((1−θ)n))`, `g = g₊`. -/
lemma gt_coreF17 {θ u R1 R2 B g N : ℝ} (hθ0 : 46 / 100 ≤ θ) (hθ1 : θ ≤ 528 / 1000)
    (hu0 : 0 < u) (hu : u ≤ 7670 / 10 ^ 6) (hN : N = u ^ 2)
    (hR1 : R1 ≤ u / 2) (_hR10 : 0 ≤ R1) (hR2 : R2 ≤ 37417 / 10000 * u) (_hR20 : 0 ≤ R2)
    (hB1 : (1 - θ) * B = R1) (hB2 : (1 - θ) * B ^ 2 = θ * N)
    (hg : θ * N * 8 * g ≤ 8 * θ * (u + 385 / 100 * u ^ 2)) :
    ((1 - θ) * (1 + 5 * B) ^ 2 + θ * N * 8 * g) ≤
        655 / 1000 * (1 - (2 * 5 * R1 + 2 * θ * R2)) ∧
      370 / 1000 * (1 + (2 * 5 * R1 + 2 * θ * R2 + 2 * θ * 14 * N)) ≤
        (1 - θ) * (1 - 5 * B) ^ 2 - θ * N * 8 * g := by
  have e1 : (1 - θ) * (1 + 5 * B) ^ 2 = (1 - θ) + 10 * ((1 - θ) * B) + 25 * ((1 - θ) * B ^ 2) := by
    ring
  have e2 : (1 - θ) * (1 - 5 * B) ^ 2 = (1 - θ) - 10 * ((1 - θ) * B) + 25 * ((1 - θ) * B ^ 2) := by
    ring
  rw [hB1, hB2] at e1 e2
  rw [e1, e2]
  have hθ0' : 0 ≤ θ := by linarith
  have hθu : θ * u ≤ θ * (7670 / 10 ^ 6) := mul_le_mul_of_nonneg_left hu hθ0'
  have hu2 : u ^ 2 ≤ (7670 / 10 ^ 6) ^ 2 := pow_le_pow_left₀ hu0.le hu 2
  have hθu2 : θ * u ^ 2 ≤ θ * (7670 / 10 ^ 6) ^ 2 := mul_le_mul_of_nonneg_left hu2 hθ0'
  have hθR2 : θ * R2 ≤ θ * (37417 / 10000 * u) := mul_le_mul_of_nonneg_left hR2 hθ0'
  have hθu20 : 0 ≤ θ * u ^ 2 := mul_nonneg hθ0' (sq_nonneg u)
  subst hN
  constructor
  · nlinarith
  · nlinarith

lemma gt_u_leF17 (hn : 17000 ≤ n) : (√(n : ℝ))⁻¹ ≤ 7670 / 10 ^ 6 := by
  have hnR : (17000 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (10 ^ 6 / 7670 : ℝ) ≤ √(n : ℝ) := by
    apply Real.le_sqrt_of_sq_le; nlinarith
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  refine le_trans ?_ hs
  norm_num

/-- **The window geometry**: for `n ≥ 22 000`, every pair of `Γ(5, 14, 8)` in the window
`0.46 ≤ θ ≤ 0.528` has `0.386 ≤ x·x' ≤ 0.638`. -/
theorem geoT17_holds (hn : 17000 ≤ n) : GeoT17 n := by
  intro c τ hτ hw p hp
  obtain ⟨hθ0, hθ1⟩ := hw
  have hn0 : 0 < n := by omega
  have hnR : (17000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  set θ := thetaC c τ with hθd
  have hθlt : θ < 1 := by linarith
  have hc : c ≠ 0 := ne_zero_of_thetaC_lt hn0 hτ hθlt
  have h1θ : 0 < 1 - θ := by linarith
  -- the variables
  set u := (√(n : ℝ))⁻¹ with hud
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hnp
  have hu0 : 0 < u := inv_pos.mpr hs0
  have hu := gt_u_leF17 hn
  have hu2 : u ^ 2 = 1 / (n : ℝ) := by
    rw [hud, inv_pow, Real.sq_sqrt hnp.le, one_div]
  have hsu : √(n : ℝ) = 1 / u := by rw [hud, one_div, inv_inv]
  set R1 := √(θ * (1 - θ) / n) with hR1d
  set R2 := √((14 : ℝ) / n) with hR2d
  set B := √(θ / ((1 - θ) * n)) with hBd
  set g := gPlus n 14 with hgd
  have hR10 : 0 ≤ R1 := Real.sqrt_nonneg _
  have hR20 : 0 ≤ R2 := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hR1 : R1 ≤ u / 2 := by
    refine sqrt_le_of_sq' (by positivity) ?_
    have e : θ * (1 - θ) / n = θ * (1 - θ) * u ^ 2 := by rw [hu2]; ring
    rw [e]
    have hq : θ * (1 - θ) ≤ 1 / 4 := by nlinarith [sq_nonneg (θ - 1 / 2)]
    nlinarith [sq_nonneg u]
  have hR2 : R2 ≤ 37417 / 10000 * u := by
    refine sqrt_le_of_sq' (by positivity) ?_
    have e : (14 : ℝ) / n = 14 * u ^ 2 := by rw [hu2]; ring
    rw [e]
    nlinarith [sq_nonneg u]
  have hBsq : B ^ 2 = θ / ((1 - θ) * n) := Real.sq_sqrt (by positivity)
  have hR1sq : R1 ^ 2 = θ * (1 - θ) / n := Real.sq_sqrt (by
    have : 0 ≤ θ * (1 - θ) := mul_nonneg (by linarith) h1θ.le
    positivity)
  have hB2 : (1 - θ) * B ^ 2 = θ * u ^ 2 := by
    rw [hBsq, hu2]; field_simp
  have hB1 : (1 - θ) * B = R1 := by
    have hsq : ((1 - θ) * B) ^ 2 = R1 ^ 2 := by
      rw [mul_pow, hBsq, hR1sq]; field_simp
    exact (pow_left_inj₀ (mul_nonneg h1θ.le hB0) hR10 two_ne_zero).1 hsq
  have h14 : √(14 : ℝ) ≤ 37417 / 10000 := sqrt_le_of_sq' (by norm_num) (by norm_num)
  have hgle : g ≤ √(n : ℝ) + 385 / 100 := by
    refine sqrt_le_of_sq' (by positivity) ?_
    have e : √((n : ℝ) * 14) = √(n : ℝ) * √14 := Real.sqrt_mul hnp.le 14
    rw [e]
    have hs136 : (130 : ℝ) ≤ √(n : ℝ) := by
      apply Real.le_sqrt_of_sq_le; nlinarith
    have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hnp.le
    nlinarith [mul_le_mul_of_nonneg_left h14 hs0.le]
  have hg : θ * u ^ 2 * 8 * g ≤ 8 * θ * (u + 385 / 100 * u ^ 2) := by
    have hθ0' : 0 ≤ θ := by linarith
    have h1 : θ * u ^ 2 * 8 * g ≤ θ * u ^ 2 * 8 * (1 / u + 385 / 100) := by
      rw [← hsu]
      exact mul_le_mul_of_nonneg_left hgle (by positivity)
    refine h1.trans (le_of_eq ?_)
    field_simp
  obtain ⟨hup, hlo⟩ := gt_coreF17 hθ0 hθ1 hu0 hu rfl hR1 hR10 hR2 hR20 hB1 hB2 hg
  -- gamma_dot
  have hb : 5 * B < 1 := by
    by_contra hcon
    have : (1 - θ) * 1 ≤ (1 - θ) * (5 * B) := mul_le_mul_of_nonneg_left (not_lt.mp hcon) h1θ.le
    nlinarith
  have hr := rminus_ltF17 hn (by linarith : (0 : ℝ) ≤ θ) hθ1
  have hG := gamma_dot hn0 hc hτ (t0 := 5) (z0 := 14) (t1 := 8) (by norm_num) (by norm_num)
    (by norm_num) hθlt (ξ := p.1) (ξ' := p.2) hp hb hr
  have eθn : θ / (n : ℝ) = θ * u ^ 2 := by rw [hu2]; ring
  have e14 : 2 * θ * 14 / (n : ℝ) = 2 * θ * 14 * u ^ 2 := by rw [hu2]; ring
  rw [eθn, e14] at hG
  obtain ⟨hG1, hG2⟩ := hG
  have hden : 0 < 1 - (2 * 5 * R1 + 2 * θ * R2) := by linarith
  have hθ0' : 0 ≤ θ := by linarith
  have hrp : 0 < 1 + (2 * 5 * R1 + 2 * θ * R2 + 2 * θ * 14 * u ^ 2) := by positivity
  constructor
  · have hL0 : 0 ≤ (1 - θ) * (1 - 5 * B) ^ 2 - θ * u ^ 2 * 8 * g := by
      have : 0 ≤ 370 / 1000 * (1 + (2 * 5 * R1 + 2 * θ * R2 + 2 * θ * 14 * u ^ 2)) := by positivity
      linarith
    refine le_trans ?_ (hG2 hL0)
    rw [le_div_iff₀ hrp]
    exact hlo
  · refine hG1.trans ?_
    rw [div_le_iff₀ hden]
    exact hup

/-! ## The covariance bound -/



/-- **The covariance event of the window**: outside the window, or the pair mass of the bad pairs
(wide sets `(5, 14, 8)`, `λ = 0.72`) is at most `10⁻¹³`. -/
def SCovT17 (n : ℕ) : Set (AgFam n) :=
  {k | ¬ winT k.1.1 k.1.2} ∪ SCov n 5 14 8 (645 / 1000) (1 / 10 ^ 13)

theorem measurableSet_SCovT17 (n : ℕ) : MeasurableSet (SCovT17 n) := by
  have hw : MeasurableSet {k : AgFam n | winT k.1.1 k.1.2} :=
    (measurableSet_le measurable_const BstLean.Part182.measurable_thetaC_key21).inter
      (measurableSet_le BstLean.Part182.measurable_thetaC_key21 measurable_const)
  exact hw.compl.union (measurableSet_SCov _ _ _ _ _)

/-- **The charge of `SCovT17` at one `(c, τ)`**, given the two-input hypothesis. -/
theorem SCovT17_charge (hn : 1 ≤ n) (hgeo : GeoT17 n)
    (hTI : TI_hyp n (370 / 1000) (655 / 1000) (645 / 1000) (1 / 10 ^ 18))
    (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SCovT17 n} ≤ 1 / 10 ^ 5 := by
  by_cases hw : winT c τ
  · have h := SCov_charge (t0 := 5) (z0 := 14) (t1 := 8) (lam := 645 / 1000) hn c τ
      (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 18) (by norm_num : (0 : ℝ) < 1 / 10 ^ 5)
      (hgeo c τ hτ hw) hTI
    have e : (1 / 10 ^ 18 : ℝ) / (1 / 10 ^ 5) = 1 / 10 ^ 13 := by norm_num
    rw [e] at h
    refine le_trans (measureReal_mono (fun θ hθ => ?_) (measure_ne_top _ _)) h
    intro hS
    exact hθ (Or.inr hS)
  · have e : {θ | ((c, τ), θ) ∉ SCovT17 n} = ∅ := by
      ext θ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact Or.inl hw
    rw [e, measureReal_empty]
    norm_num

/-- **The charge of `SCovT17` for the retained data** of the paper's design. -/
theorem SCovT17_ret_charge (hn : 17000 ≤ n) (hgeo : GeoT17 n)
    (hTI : TI_hyp n (370 / 1000) (655 / 1000) (645 / 1000) (1 / 10 ^ 18))
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real (agentEv (paperDesign n fT wT hf hw) (SCovT17 n))ᶜ ≤
      1 / 10 ^ 5 := by
  rw [agentEv_compl]
  exact retDist_agent_charge (paperDesign n fT wT hf hw) (paperDesign_tauWorld fT wT hf hw)
    (measurableSet_SCovT17 n) (by norm_num)
    (fun c τ hτ => SCovT17_charge (by omega) hgeo hTI c τ hτ)

/-- **The quadratic form of `D` on `SXM22 ∩ SCovT17`** (single-level weighted Schur test):
`Dq v ≤ (0.585·1.0186·θ_hi + 1.102·1.0186·θ_hi·0.003711)·(γ_A/n)·|v|²` for `n ≥ 22 000` and
`0.46 ≤ θ ≤ θ_hi ≤ 0.528`. -/
theorem Dq_TI17 (hn : 17000 ≤ n) {c : Fin n → ℝ} {τ θh : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θh) (hθh : θh ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (hX : ((c, τ), (A₁, A₂)) ∈ SXM17 n) (hC : ((c, τ), (A₁, A₂)) ∈ SCovT17 n)
    (v : Fin (mA n) → ℝ) :
    Dq A₁ A₂ c τ v ≤ (645 / 1000 * (10207 / 10000) * θh +
      1116 / 1000 * (10207 / 10000) * θh * (3711 / 10 ^ 6)) * (2 / (n : ℝ)) / n * normSq v := by
  have hP : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn0 : 0 < n := by omega
  have hnR : (17000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR0 : (0 : ℝ) < n := by linarith
  have hθlt : thetaC c τ < 1 := by linarith
  have hc : c ≠ 0 := ne_zero_of_thetaC_lt hn0 hτ hθlt
  set μ := stdGauss (Fin n) with hμ
  set Ω := OmegaS c 5 14 with hΩd
  set Γ := GammaS c 5 14 8 with hΓd
  set key : AgFam n := ((c, τ), (A₁, A₂)) with hkey
  set Bx : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    {p | (key, p) ∈ badSet n 5 14 8 (645 / 1000)} with hBxd
  have hBxm : MeasurableSet Bx := measurable_prodMk_left (measurableSet_badSet 5 14 8 (645 / 1000))
  have hΩm : MeasurableSet Ω := measurableSet_OmegaS c 5 14
  have hΓm : MeasurableSet Γ := measurableSet_GammaS c 5 14 8
  set G := Γ \ (Bx ∪ Prod.swap ⁻¹' Bx) with hGd
  have hGm : MeasurableSet G := hΓm.diff (hBxm.union (measurable_swap hBxm))
  have hGs : ∀ a b, (a, b) ∈ G → (b, a) ∈ G := by
    intro a b h
    obtain ⟨h1, h2⟩ := h
    refine ⟨gammaS_swap h1, ?_⟩
    rintro (h3 | h3)
    · exact h2 (Or.inr h3)
    · exact h2 (Or.inl h3)
  have hpair : ∀ a b, (a, b) ∈ G → opN ((BJ A₁ A₂ c τ a)ᵀ * BJ A₁ A₂ c τ b) ≤
      (n : ℝ) * (645 / 1000) := by
    intro a b h
    obtain ⟨h1, h2⟩ := h
    have hnb : ¬ pairBad A₁ A₂ (645 / 1000) (sphPt (c + τ • a)) (sphPt (c + τ • b)) := by
      intro hb
      exact h2 (Or.inl ⟨h1, hb⟩)
    unfold pairBad at hnb
    exact not_lt.mp hnb
  have hpair₁ : ∀ a b, (a, b) ∈ G → opN ((BJ A₁ A₂ c τ a)ᵀ * BJ A₁ A₂ c τ b) ≤
      kern Set.univ ((n : ℝ) * (645 / 1000)) ((n : ℝ) * (645 / 1000)) a b := by
    intro a b h
    rw [kern_of_mem (Set.mem_univ _)]
    exact hpair a b h
  -- the weight bounds
  have hr := rminus_ltF17 hn (by linarith) (hθ1.trans hθh)
  set rm := 2 * 5 * √(thetaC c τ * (1 - thetaC c τ) / n) + 2 * thetaC c τ * √(14 / n) with hrm
  have hWb : ∀ ξ ∈ Ω, BstLean.Part182.wN c τ ξ ≤ thetaC c τ / n / (1 - rm) := by
    intro ξ hξ
    have h := omega_weight hn0 hc hτ (t0 := 5) (z0 := 14) (by norm_num) (by norm_num) hξ
      (by simpa only [hrm, mul_assoc] using hr)
    simpa only [BstLean.Part182.wN, hrm, mul_assoc] using h
  have hWb0 : 0 ≤ thetaC c τ / n / (1 - rm) := by
    have : 0 < 1 - rm := by linarith
    have : 0 ≤ thetaC c τ := by linarith
    positivity
  have hEw : ∫ ξ, BstLean.Part182.wN c τ ξ ∂μ ≤ 10207 / 10000 * (thetaC c τ / n) := by
    have h := Ew_le_F17 hn c hτ hθ0 (hθ1.trans hθh)
    simpa only [BstLean.Part182.wN, integral_const_mul] using h
  have hPp : ∀ ξ, μ.real {ξ' | ξ' ∈ Ω ∧ (ξ, ξ') ∉ (Set.univ : Set ((Fin n → ℝ) × (Fin n → ℝ)))} ≤
      0 := by
    intro ξ
    have e : {ξ' | ξ' ∈ Ω ∧ (ξ, ξ') ∉ (Set.univ : Set ((Fin n → ℝ) × (Fin n → ℝ)))} = ∅ := by
      ext ξ'; simp
    rw [e, measureReal_empty]
  have hPs : μ.real (Ω \ Ω) ≤ 0 := by rw [Set.diff_self, measureReal_empty]
  have hmain := Dq_le_kern A₁ A₂ c (by omega) hτ (subset_refl Ω) hΩm hΩm
    (lam₁ := 645 / 1000) (lam₀ := 645 / 1000) (by norm_num) (by norm_num)
    Set.univ MeasurableSet.univ (fun _ _ _ => Set.mem_univ _) G hGm hGs hpair₁ G hGm hGs hpair
    hEw hWb0 hWb hPp hPs v
  -- the exceptional masses
  have hH0 : ((μ.prod μ).real (Gᶜ ∩ (Ω \ Ω) ×ˢ (Ω \ Ω))) = 0 := by
    rw [Set.diff_self, Set.empty_prod, Set.inter_empty, measureReal_empty]
  have hwin : winT c τ := ⟨hθ0, hθ1.trans hθh⟩
  have hbad : badMass n 5 14 8 (645 / 1000) key ≤ 1 / 10 ^ 13 := by
    rcases hC with h | h
    · exact absurd hwin h
    · exact h
  have hBxr : (μ.prod μ).real Bx ≤ 1 / 10 ^ 13 := hbad
  have hBxs : (μ.prod μ).real (Prod.swap ⁻¹' Bx) = (μ.prod μ).real Bx := by
    rw [Measure.real, Measure.real,
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).measure_preimage hBxm.nullMeasurableSet]
  have hout := pairs_out_gamma hn0 c (t0 := 5) (z0 := 14) (t1 := 8) (by norm_num) (by norm_num)
  have hH1 : (μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω) ≤ 26 / 10 ^ 15 + 2 / 10 ^ 13 := by
    have hsub : Gᶜ ∩ Ω ×ˢ Ω ⊆ ((Ω ×ˢ Ω) \ Γ) ∪ Bx ∪ Prod.swap ⁻¹' Bx := by
      rintro p ⟨hp1, hp2⟩
      by_cases hpΓ : p ∈ Γ
      · have : p ∈ Bx ∪ Prod.swap ⁻¹' Bx := by
          by_contra hn'
          exact hp1 ⟨hpΓ, hn'⟩
        rcases this with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · exact Or.inl (Or.inl ⟨hp2, hpΓ⟩)
    calc (μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω)
        ≤ (μ.prod μ).real (((Ω ×ˢ Ω) \ Γ) ∪ Bx ∪ Prod.swap ⁻¹' Bx) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ (μ.prod μ).real (((Ω ×ˢ Ω) \ Γ) ∪ Bx) + (μ.prod μ).real (Prod.swap ⁻¹' Bx) :=
          measureReal_union_le _ _
      _ ≤ (μ.prod μ).real ((Ω ×ˢ Ω) \ Γ) + (μ.prod μ).real Bx +
            (μ.prod μ).real (Prod.swap ⁻¹' Bx) :=
          add_le_add (measureReal_union_le _ _) le_rfl
      _ ≤ 26 / 10 ^ 15 + 2 / 10 ^ 13 := by
          rw [hBxs]
          have := two_exp_neg32
          linarith
  have hq1 : √(√((μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω))) ≤ 690 / 10 ^ 6 :=
    sqrt_sqrt_le_of (by norm_num) (hH1.trans (by norm_num))
  have hPo : μ.real Ωᶜ ≤ 9126 / 10 ^ 9 := by
    have h := omega_compl_le hn0 c (t0 := 5) (z0 := 14) (by norm_num) (by norm_num)
    exact h.trans Po_le
  have hq2 : √(μ.real Ωᶜ) ≤ 3021 / 10 ^ 6 :=
    sqrt_le_of_sq' (by norm_num) (hPo.trans (by norm_num))
  have hX4 := Xi4_SXM17 hn hτ hθ0 hθ1 hθh hX
  have hX40 : 0 ≤ Xi4 A₁ A₂ c τ := by
    unfold Xi4; positivity
  rw [hH0, Real.sqrt_zero, Real.sqrt_zero, add_zero] at hmain
  have hmR : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hS0 : 0 ≤ normSq v := normSq_nonneg v
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ hS0)
  -- the scalar inequality
  have hf : √(√((μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω))) + √(μ.real Ωᶜ) ≤ 3711 / 10 ^ 6 := by linarith
  have hf0 : 0 ≤ √(√((μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω))) + √(μ.real Ωᶜ) := by positivity
  have hXf : Xi4 A₁ A₂ c τ * (√(√((μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω))) + √(μ.real Ωᶜ)) ≤
      1116 / 1000 * (10207 / 10000) * θh * (2 / (n : ℝ)) / n * (3711 / 10 ^ 6) :=
    mul_le_mul hX4 hf hf0 (by
      have : 0 ≤ θh := by linarith
      positivity)
  have hE : 2 / ((mA n : ℕ) : ℝ) * ((n : ℝ) * (645 / 1000) * (10207 / 10000 * (thetaC c τ / n)) +
      (n : ℝ) * (645 / 1000) * (thetaC c τ / n / (1 - rm)) * 0 +
      (n : ℝ) * (645 / 1000) * (thetaC c τ / n / (1 - rm)) * 0) ≤
      645 / 1000 * (10207 / 10000) * θh * (2 / (n : ℝ)) / n := by
    rw [hmR]; simp only [mul_zero, add_zero]
    have e : 2 / (n : ℝ) ^ 2 * ((n : ℝ) * (645 / 1000) * (10207 / 10000 * (thetaC c τ / n))) =
        645 / 1000 * (10207 / 10000) * thetaC c τ * (2 / (n : ℝ)) / n := by
      field_simp
    rw [e]
    have : 0 < (2 / (n : ℝ)) / n := by positivity
    have h2 : 645 / 1000 * (10207 / 10000) * thetaC c τ ≤ 645 / 1000 * (10207 / 10000) * θh := by
      nlinarith
    calc 645 / 1000 * (10207 / 10000) * thetaC c τ * (2 / (n : ℝ)) / n
        = 645 / 1000 * (10207 / 10000) * thetaC c τ * ((2 / (n : ℝ)) / n) := by ring
      _ ≤ 645 / 1000 * (10207 / 10000) * θh * ((2 / (n : ℝ)) / n) :=
          mul_le_mul_of_nonneg_right h2 this.le
      _ = 645 / 1000 * (10207 / 10000) * θh * (2 / (n : ℝ)) / n := by ring
  calc 2 / ((mA n : ℕ) : ℝ) * ((n : ℝ) * (645 / 1000) * (10207 / 10000 * (thetaC c τ / n)) +
        (n : ℝ) * (645 / 1000) * (thetaC c τ / n / (1 - rm)) * 0 +
        (n : ℝ) * (645 / 1000) * (thetaC c τ / n / (1 - rm)) * 0) +
        Xi4 A₁ A₂ c τ * (√(√((μ.prod μ).real (Gᶜ ∩ Ω ×ˢ Ω))) + √(μ.real Ωᶜ))
      ≤ 645 / 1000 * (10207 / 10000) * θh * (2 / (n : ℝ)) / n +
        1116 / 1000 * (10207 / 10000) * θh * (2 / (n : ℝ)) / n * (3711 / 10 ^ 6) := add_le_add hE hXf
    _ = (645 / 1000 * (10207 / 10000) * θh +
        1116 / 1000 * (10207 / 10000) * θh * (3711 / 10 ^ 6)) * (2 / (n : ℝ)) / n := by ring

/-- **The covariance hypothesis `COV_at D c N` on `SXM22 ∩ SCovT17`**, for every `N` at least
`0.585·1.0186·θ_hi + 1.102·1.0186·θ_hi·0.003711`. -/
theorem cov_TI17 (hn : 17000 ≤ n) (D : Design n) (c : Ret n) (hτ : 0 < D.tau0 c) {θh N : ℝ}
    (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c)) (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ θh)
    (hθh : θh ≤ 528 / 1000)
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM17 n)
    (hC : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SCovT17 n)
    (hN : 645 / 1000 * (10207 / 10000) * θh + 1116 / 1000 * (10207 / 10000) * θh * (3711 / 10 ^ 6) ≤ N) :
    COV_at D c N := by
  refine cov_at_of_Dq (by omega) D c hτ fun w => ?_
  refine (Dq_TI17 hn hτ hθ0 hθ1 hθh hX hC w).trans ?_
  have hnR : (0 : ℝ) < n := by
    have : (17000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h0 : 0 ≤ (2 / (n : ℝ)) / n * normSq w := by
    have := normSq_nonneg w
    positivity
  calc (645 / 1000 * (10207 / 10000) * θh + 1116 / 1000 * (10207 / 10000) * θh * (3711 / 10 ^ 6)) *
        (2 / (n : ℝ)) / n * normSq w
      = (645 / 1000 * (10207 / 10000) * θh + 1116 / 1000 * (10207 / 10000) * θh * (3711 / 10 ^ 6)) *
        ((2 / (n : ℝ)) / n * normSq w) := by ring
    _ ≤ N * ((2 / (n : ℝ)) / n * normSq w) := mul_le_mul_of_nonneg_right hN h0
    _ = N * (2 / (n : ℝ)) / n * normSq w := by ring

end BstLean.Part183.F17

open BstLean.Part183.F17 in
#print axioms cov_TI17
open BstLean.Part183.F17 in
#print axioms SCovT17_ret_charge
open BstLean.Part183.F17 in
#print axioms geoT17_holds
