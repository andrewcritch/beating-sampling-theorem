import BstLean.Part277Centre
import BstLean.Part264Centre

/-! Part 277, energy: the lower-energy data of `Part264.energy_lower_data` on a base `n0 ≥ 8000`
and a window `[.46, θhi]` with `θhi ≤ .54`. The cap `(s2 - 2 t2/n0 - F/r)²` is an explicit
rational function of `n0` and the rational witnesses; each witness has one rational hypothesis.
`kappa_lower_rational` (generic) supplies the `κ` lower bounds `K0`, `K1`. -/
namespace BstLean.Part277
open Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part182 BstLean.Part206
  BstLean.Part211

theorem energy_lower_dataP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {θhi θ : ℝ}
    (hθhi : θhi ≤ 54 / 100) (hw : θ ∈ Icc (46 / 100 : ℝ) θhi)
    {t t2 s1 s2 K0 K1 q1 G g0 F r s0 : ℝ}
    (ht : √(12 : ℝ) ≤ t)
    (hK0 : K0 ≤ kappa (1 - θhi))
    (hs1 : s1 ^ 2 ≤ K0 - 8 * θhi / n0 - 2 / (n0 : ℝ) ^ 2) (hM0 : 0 ≤ s1 - 2 * t / n0)
    (hG : (1 + 2 * t / n0) ^ 2 ≤ G)
    (hq10 : 0 ≤ q1) (hq1 : q1 ≤ 3 / 4) (hq1M : q1 * G ≤ (s1 - 2 * t / n0) ^ 2)
    (hK1 : K1 ≤ kappa q1) (hK1p : 0 ≤ K1 - 2 / (n0 : ℝ) ^ 2)
    (hs0 : s0 ≤ √(1 - 2 / (n0 : ℝ) ^ 2)) (hst : 2 * t / n0 ≤ s0)
    (hg0 : g0 ≤ (s0 - 2 * t / n0) ^ 2)
    (hs2 : s2 ^ 2 ≤ g0 * (K1 - 2 / (n0 : ℝ) ^ 2))
    (ht2 : √(12 * G) ≤ t2)
    (hr0 : 0 < r) (hr : r ^ 2 ≤ n0) (hF : finiteEnergy n n (11 / 1000) ≤ F) :
    0 ≤ meanLowerRoot n θ ∧
    0 ≤ kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) - 2 / (n : ℝ) ^ 2 ∧
    s2 - 2 * t2 / n0 - F / r ≤ √(gMinus n *
      (kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) - 2 / (n : ℝ) ^ 2)) -
      2 * √(12 * BstLean.Part211.gPlus n) / n - finiteEnergy n n (11 / 1000) / √(n : ℝ) ∧
    (0 ≤ s2 - 2 * t2 / n0 - F / r →
      (s2 - 2 * t2 / n0 - F / r) ^ 2 ≤ energyLower n (gMinus n) (BstLean.Part211.gPlus n)
        (finiteEnergy n n (11 / 1000)) θ) := by
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hn00 : (0 : ℝ) < n0 := by linarith
  have hnp : (0 : ℝ) < n := by linarith
  have hθ0 : 0 ≤ θ := by linarith [hw.1]
  have ht0 : 0 ≤ t := (sqrt_nonneg _).trans ht
  have hi : 2 / (n : ℝ) ^ 2 ≤ 2 / (n0 : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hn00.le hnn 2)
  have h8θ : 8 * θ / (n : ℝ) ≤ 8 * θhi / n0 := by
    have h1 : 8 * θ / (n : ℝ) ≤ 8 * θhi / n := by gcongr; exact hw.2
    have h2 : 8 * θhi / (n : ℝ) ≤ 8 * θhi / n0 :=
      div_le_div_of_nonneg_left (by linarith [hw.1, hw.2]) hn00 hnn
    linarith
  have hmem0 : (1 - θhi) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith [hw.1, hw.2]⟩
  have hmem : (1 - θ) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hw.2], by linarith [hw.1]⟩
  have hκm := kappa_monotoneOn hmem0 hmem (by linarith [hw.2])
  have hk1 := (kappa_mem (by linarith [hw.2] : -1 ≤ 1 - θ) (by linarith [hw.1] : 1 - θ ≤ 1)).2
  have htail : 2 * √(12 : ℝ) / n ≤ 2 * t / n0 := by
    calc 2 * √(12 : ℝ) / n ≤ 2 * t / n := by gcongr
      _ ≤ 2 * t / n0 := div_le_div_of_nonneg_left (by positivity) hn00 hnn
  have hsq : s1 ≤ √(kappa (1 - θ) - 8 * θ / n - 2 / (n : ℝ) ^ 2) :=
    le_sqrt_of_sq_le (by linarith)
  have hmlo : s1 - 2 * t / n0 ≤ meanLowerRoot n θ := by unfold meanLowerRoot; linarith
  have hmhi : meanLowerRoot n θ ≤ 1 := by
    have h0 : 0 ≤ 8 * θ / (n : ℝ) := by positivity
    have h1 : 0 ≤ 2 / (n : ℝ) ^ 2 := by positivity
    have h2 : 0 ≤ 2 * √(12 : ℝ) / n := by positivity
    have : √(kappa (1 - θ) - 8 * θ / n - 2 / (n : ℝ) ^ 2) ≤ 1 :=
      sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
    unfold meanLowerRoot
    linarith
  have hgp : BstLean.Part211.gPlus n ≤ G := (gPlus_upperP h8 hn ht).trans hG
  have hgp1 := BstLean.Part264.gPlus_lower n
  have hgm : g0 ≤ gMinus n := hg0.trans (gMinus_lowerP h8 hn ht hs0 hst)
  have hm0 : 0 ≤ meanLowerRoot n θ := hM0.trans hmlo
  have hgpp : 0 < BstLean.Part211.gPlus n := by linarith
  have hr_ : q1 ≤ meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n := by
    apply (le_div_iff₀ hgpp).mpr
    calc q1 * BstLean.Part211.gPlus n ≤ q1 * G := mul_le_mul_of_nonneg_left hgp hq10
      _ ≤ (s1 - 2 * t / n0) ^ 2 := hq1M
      _ ≤ _ := pow_le_pow_left₀ hM0 hmlo 2
  have hr1 : meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n ≤ 1 := by
    apply (div_le_iff₀ hgpp).mpr
    nlinarith
  have hκ2 := kappa_monotoneOn (show q1 ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, by linarith⟩)
    (show meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n ∈ Icc (-1 : ℝ) 1 from
      ⟨by linarith, hr1⟩) hr_
  have hbr : K1 - 2 / (n0 : ℝ) ^ 2 ≤
      kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) - 2 / (n : ℝ) ^ 2 := by linarith
  have hgm0 : 0 ≤ gMinus n := by unfold gMinus; exact sq_nonneg _
  have hs2' : s2 ≤ √(gMinus n *
      (kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) - 2 / (n : ℝ) ^ 2)) := by
    apply le_sqrt_of_sq_le
    exact hs2.trans (mul_le_mul hgm hbr hK1p hgm0)
  have ht2' : √(12 * BstLean.Part211.gPlus n) ≤ t2 :=
    (sqrt_le_sqrt (by linarith)).trans ht2
  have ht20 : 0 ≤ t2 := (sqrt_nonneg _).trans ht2'
  have htail2 : 2 * √(12 * BstLean.Part211.gPlus n) / n ≤ 2 * t2 / n0 := by
    calc 2 * √(12 * BstLean.Part211.gPlus n) / n ≤ 2 * t2 / n := by gcongr
      _ ≤ 2 * t2 / n0 := div_le_div_of_nonneg_left (by positivity) hn00 hnn
  have hnr : r ≤ √(n : ℝ) := le_sqrt_of_sq_le (hr.trans hnn)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy n n (11 / 1000) / √(n : ℝ) ≤ F / r :=
    div_le_div₀ (hf0.trans hF) hF hr0 hnr
  have hmain : s2 - 2 * t2 / n0 - F / r ≤ √(gMinus n *
      (kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) - 2 / (n : ℝ) ^ 2)) -
      2 * √(12 * BstLean.Part211.gPlus n) / n - finiteEnergy n n (11 / 1000) / √(n : ℝ) := by
    linarith
  refine ⟨hm0, le_trans hK1p (by linarith), hmain, ?_⟩
  intro hpos
  unfold energyLower
  exact pow_le_pow_left₀ hpos hmain 2

end BstLean.Part277
