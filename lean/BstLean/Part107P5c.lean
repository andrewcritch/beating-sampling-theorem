import BstLean.Part107P5b

/-!
# Part 107 (P5), part (i): `E κ(x·x′) ≤ v̄`
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part105

lemma measurable_kap {dA : ℕ} (hder : ∀ a : ℝ, HasDerivAt (kap dA) (kap' dA a) a) :
    Measurable (kap dA) :=
  (continuous_iff_continuousAt.mpr fun a => (hder a).continuousAt).measurable

lemma kap_clamp_BM {dA : ℕ} (hder : ∀ a : ℝ, HasDerivAt (kap dA) (kap' dA a) a)
    (hrange : ∀ a : ℝ, |a| ≤ 1 → 0 ≤ kap dA a ∧ kap dA a ≤ (dA : ℝ) + 1) :
    BM (clampF (kap dA)) :=
  clampF_BM (measurable_kap hder) ((dA : ℝ) + 1) fun a ha => by
    obtain ⟨h0, h1⟩ := hrange a ha
    rw [abs_of_nonneg h0]; exact h1

lemma kap_aR_integrable {dA : ℕ} (hder : ∀ a : ℝ, HasDerivAt (kap dA) (kap' dA a) a)
    (hrange : ∀ a : ℝ, |a| ≤ 1 → 0 ≤ kap dA a ∧ kap dA a ≤ (dA : ℝ) + 1) (n : ℕ) (r : ℝ) :
    Integrable (fun p => kap dA (aR (n := n) r p)) (gg n) :=
  ((BM_aR (kap_clamp_BM hder hrange) r (n := n)).integrable (gg n)).congr
    (Filter.Eventually.of_forall fun p => clampF_eq _ (abs_aR_le r p))

lemma rW_sq_integrable {n : ℕ} (hN : 1 ≤ 2 * n) (d : ℕ) (c : ℝ) :
    Integrable (fun z : (Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ) => (rW d (dot z.1 z.2) - c) ^ 2)
      ((uniformSphere (2 * n)).prod (uniformSphere (2 * n))) := by
  refine int_of_unit_bdd hN ((((measurable_rW d).comp measurable_dot2).sub_const c).pow_const 2)
    ((1 + |c|) ^ 2) fun z h1 h2 => ?_
  have h := abs_rW_le d (abs_dot_le_one _ _ h1 h2)
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by linarith)) 2

theorem p5_part1 (hT : TwoPoint107) (h1 : P1_107) (hS : SphStat107) (hK : KapFacts107)
    (n dA : ℕ) (σ : ℝ) (hn : 3 ≤ n) (hd : dA = 3 ∨ dA = 4) (hσ : σ ≠ 0) :
    twoPt (2 * n) n (2 * dA) σ (kap dA) ≤ vbar dA n := by
  obtain ⟨hder, hrange, hquad, -, -⟩ := hK dA hd
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hκB := kap_clamp_BM hder hrange
  have hsqB : BM (clampF (fun a : ℝ => a ^ 2)) :=
    clampF_BM (measurable_id.pow_const 2) 1 fun a ha => by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) ha
  have hdel := delN_nonneg dA (2 * n)
  have hE : 0 < Ea2 dA n := by
    unfold Ea2
    have h1 : 0 < 1 / (2 * (dA : ℝ) + 1) ^ 2 := by positivity
    have h2 : 0 < 3 / (n : ℝ) := by apply div_pos <;> linarith
    linarith
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (Ea2 dA n) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hE
  have hss : s ^ 2 = Ea2 dA n := by rw [hs]; exact Real.sq_sqrt hE.le
  have hdA1 : (0 : ℝ) ≤ (dA : ℝ) - 1 := by rcases hd with rfl | rfl <;> norm_num
  obtain ⟨c1, hc1d⟩ : ∃ c1 : ℝ, c1 = 1 / (2 * s) + ((dA : ℝ) - 1) := ⟨_, rfl⟩
  have hc1 : 0 ≤ c1 := by rw [hc1d]; positivity
  have hpt : ∀ r : ℝ, |r| ≤ 1 →
      Mr n (clampF (kap dA)) r ≤ (1 + s / 2 + c1 * (3 / (n : ℝ))) + c1 * r ^ 2 := by
    intro r hr
    rw [Mr_clamp]
    have hI : ∫ p, aR r p ^ 2 ∂gg n ≤ r ^ 2 + 3 / (n : ℝ) := h1 n r (by omega) hr
    have hint2 : Integrable (fun p => aR (n := n) r p ^ 2) (gg n) :=
      ((BM_aR hsqB r (n := n)).integrable (gg n)).congr
        (Filter.Eventually.of_forall fun p => clampF_eq _ (abs_aR_le r p))
    have hintk := kap_aR_integrable hder hrange n r
    have hstep : Mr n (kap dA) r ≤ ∫ p, ((1 + s / 2) + c1 * aR r p ^ 2) ∂gg n := by
      refine integral_mono hintk ((integrable_const _).add (hint2.const_mul c1)) fun p => ?_
      have ha := abs_aR_le r p
      have hq := hquad _ ha
      generalize aR r p = a at ha hq ⊢
      have h2 : a ≤ s / 2 + 1 / (2 * s) * a ^ 2 := by
        have : s / 2 + 1 / (2 * s) * a ^ 2 = (s ^ 2 + a ^ 2) / (2 * s) := by
          field_simp
        rw [this, le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (a - s)]
      show kap dA a ≤ (1 + s / 2) + c1 * a ^ 2
      rw [hc1d]
      nlinarith
    rw [integral_affine (gg n) hint2] at hstep
    nlinarith [mul_le_mul_of_nonneg_left hI hc1]
  rw [← twoPt_clamp]
  have hrint := rW_sq_integrable hN (2 * dA) 0
  simp only [sub_zero] at hrint
  have hle := twoPt_le hT hN hσ hκB
    (fun z => (1 + s / 2 + c1 * (3 / (n : ℝ))) + c1 * rW (2 * dA) (dot z.1 z.2) ^ 2)
    ((integrable_const _).add (hrint.const_mul c1))
    (fun z h1 h2 => hpt _ (abs_rW_le _ (abs_dot_le_one _ _ h1 h2)))
  rw [integral_affine _ hrint] at hle
  obtain ⟨hS1, -, -⟩ := hS (2 * n) dA hN hd
  have hS1' : ∫ z : (Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ), rW (2 * dA) (dot z.1 z.2) ^ 2
      ∂(uniformSphere (2 * n)).prod (uniformSphere (2 * n)) ≤
      1 / (2 * (dA : ℝ) + 1) ^ 2 + delN dA (2 * n) :=
    (integral_prod _ hrint).trans_le hS1
  have e1 : 1 / (2 * s) * Ea2 dA n = s / 2 := by rw [← hss]; field_simp
  have e2 : c1 * Ea2 dA n = s / 2 + ((dA : ℝ) - 1) * Ea2 dA n := by rw [hc1d, add_mul, e1]
  have e3 : c1 * Ea2 dA n =
      c1 * (1 / (2 * (dA : ℝ) + 1) ^ 2 + delN dA (2 * n)) + c1 * (3 / (n : ℝ)) := by
    unfold Ea2; ring
  have h4 := mul_le_mul_of_nonneg_left hS1' hc1
  unfold vbar
  rw [← hs]
  linarith

end BstLean.Part107
