import BstLean.Part277Energy
import BstLean.Part264bUniformFull
import BstLean.Part264bUniformEnergy

/-! Part 277, uniform schemes: the scheme lemmas of `Part264bUniformFull` and
`Part264bUniformEnergy` (`uniform_deviation_upper`, `uniform_energy_upper_from_kappas`,
`uniform_n22_upper`, `uniform_radial_centre_bound`, `uniform_full_formula_bound`) on a base
`n0 ≥ 8000`. The 12227 constants become rational witnesses with one hypothesis each.
The per-cell and per-group data lemmas (`uniformS*`, `uniformE*`, `uniformFullGroup*`,
`normalized*`) hold numbers from generated certificates. They need the generator to be re-run
at a new base; this part does not re-base them. -/
namespace BstLean.Part277
open Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part182 BstLean.Part211
  BstLean.Part206
open BstLean.Part253 (cs_lower)

theorem deviation_upperP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {Θ : ℝ} (hΘ : 0 ≤ Θ)
    {r w a1 T cap : ℝ} (hr0 : 0 < r) (hr : r ^ 2 ≤ n0) (hw : (1 + 2 / r) ^ 2 ≤ w)
    (hΘ1 : Θ ≤ 0.525) (ha1 : 2 * (1 + 0.011 - 1.29521 * 0.46 / 2) / n0 ≤ a1 ^ 2)
    (ha10 : 0 ≤ a1) (hT : w * 0.525 ≤ T ^ 2) (hT0 : 0 ≤ T)
    (hcap : 4.89898 * (a1 + 2 * T / n0) ≤ cap) :
    sharpDeviation n csC 0.011 0.46 Θ ≤ cap := by
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n0 := by linarith
  have hnp : (0 : ℝ) < n := by linarith
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hwn := wn_upperP h8 hn hr0 hr hw
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ a1 := by
    apply sqrt_le_iff.mpr
    refine ⟨ha10, ?_⟩
    refine le_trans ?_ ha1
    have hnum : 2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) ≤ 2 * (1 + 0.011 - 1.29521 * 0.46 / 2) := by
      linarith
    have hnum0 : 0 ≤ 2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) := by
      have := cs_lower
      have : csC ≤ 2 := by
        have h1 : 0 ≤ 1 / π := by positivity
        unfold csC; linarith
      linarith
    calc 2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n ≤
        2 * (1 + 0.011 - 1.29521 * 0.46 / 2) / n := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hn0 hnn
  have h2 : √(wn n * Θ) ≤ T := by
    apply sqrt_le_iff.mpr
    refine ⟨hT0, ?_⟩
    have h := mul_le_mul hwn hΘ1 hΘ (by linarith [hwn, (by unfold wn; positivity : 0 ≤ wn n)])
    linarith
  have h3 : 2 * √(wn n * Θ) / n ≤ 2 * T / n0 := by
    calc 2 * √(wn n * Θ) / n ≤ 2 * T / n := by gcongr
      _ ≤ 2 * T / n0 := div_le_div_of_nonneg_left (by positivity) hn0 hnn
  unfold sharpDeviation
  calc
    _ ≤ (4.89898 : ℝ) * (a1 + 2 * T / n0) := by gcongr <;> linarith
    _ ≤ _ := hcap

theorem n22_upperP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {t c : ℝ}
    (ht : √(12 : ℝ) ≤ t) (hc : (2.236068 + 2 * t) / n0 ≤ c) (hc0 : c ≤ 1)
    {cap : ℝ} (hcap : c * (2 + c) ≤ cap) : N22bar n 12 ≤ cap := by
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n0 := by linarith
  have hnp : (0 : ℝ) < n := by linarith
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have ht0 : 0 ≤ t := (sqrt_nonneg _).trans ht
  have h1 : N12bar n 12 ≤ c := by
    unfold N12bar
    refine le_trans ?_ hc
    calc (√5 + 2 * √12) / (n : ℝ) ≤ (2.236068 + 2 * t) / n := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hn0 hnn
  have h10 : 0 ≤ N12bar n 12 := by unfold N12bar; positivity
  have hc00 : 0 ≤ c := h10.trans h1
  unfold N22bar
  refine le_trans ?_ hcap
  gcongr

theorem radial_centre_boundP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {Θ T R r c : ℝ}
    (hΘ : 0 ≤ Θ) (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2) (hr0 : 0 < r) (hr : r ^ 2 ≤ n0)
    {t : ℝ} (ht : √(12 : ℝ) ≤ t) (hc : (2.236068 + 2 * t) / n0 ≤ c) (hc0 : c ≤ 1)
    (hcc : c * (2 + c) ≤ 0.0015)
    (hR : (Θ * 1.0015 + T) / r ≤ R) : xiNr n Θ 1.22 ≤ R := by
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hNr := n22_upperP h8 hn ht hc hc0 hcc
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hN : r ≤ √n := le_sqrt_of_sq_le (hr.trans hnn)
  unfold xiNr
  apply le_trans ?_ hR
  gcongr
  linarith

/-- The scheme of `Part264b.uniform_full_formula_bound` on a base `n0`. -/
theorem full_formula_boundP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n)
    {Θ S X T R B r w a1 Td t c Fc : ℝ}
    (hMoment : momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + 0.004138 + 0.0034293 * Θ)
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.004138 + 0.0034293 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hr0 : 0 < r) (hr : r ^ 2 ≤ n0) (hwr : (1 + 2 / r) ^ 2 ≤ w)
    (ha1 : 2 * (1 + 0.011 - 1.29521 * 0.46 / 2) / n0 ≤ a1 ^ 2) (ha10 : 0 ≤ a1)
    (hTd : w * 0.525 ≤ Td ^ 2) (hTd0 : 0 ≤ Td)
    (ht : √(12 : ℝ) ≤ t) (hc : (2.236068 + 2 * t) / n0 ≤ c) (hc0 : c ≤ 1)
    (hcc : c * (2 + c) ≤ 0.0015)
    (hR : (Θ * 1.0015 + T) / r ≤ R)
    (hFc : finiteEnergy n n 0.011 ≤ Fc)
    (hB : (X + 4.89898 * (a1 + 2 * Td / n0) + R + Fc) ^ 2 ≤ B) :
    fullFormula n n 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance n csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, hMoment.trans hXsq⟩
  have hd := deviation_upperP h8 hn hΘ hr0 hr hwr hw.2 ha1 ha10 hTd hTd0 le_rfl
  have hrr := radial_centre_boundP h8 hn hΘ hT hTsq hr0 hr ht hc hc0 hcc hR
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hr0' : 0 ≤ xiNr n Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

/-- The scheme of `Part264b.uniform_energy_upper_from_kappas` on a base `n0`. -/
theorem energy_upper_from_kappasP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n)
    {q K1 U R Q2 K2 T B t t2 g0 s0 G r F : ℝ}
    (ht : √(12 : ℝ) ≤ t) (hs0 : s0 ≤ √(1 - 2 / (n0 : ℝ) ^ 2)) (hst : 2 * t / n0 ≤ s0)
    (hg0 : g0 ≤ (s0 - 2 * t / n0) ^ 2) (hg0p : 0 < g0)
    (hG : (1 + 2 * t / n0) ^ 2 ≤ G) (ht2 : √(12 * G) ≤ t2)
    (hr0 : 0 < r) (hr : r ^ 2 ≤ n0) (hF : finiteEnergy n n (11 / 1000) ≤ F)
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / (n0 : ℝ) ≤ U ^ 2)
    (hR : U + 2 * t / n0 ≤ R)
    (hQ2 : R ^ 2 / g0 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : G * K2 ≤ T ^ 2)
    (hB : (T + 2 * t2 / n0 + F / r) ^ 2 ≤ B) :
    energyRatio n (gMinus n) q ≤ Q2 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) q ≤ B := by
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hn00 : (0 : ℝ) < n0 := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have ht0 : 0 ≤ t := (sqrt_nonneg _).trans ht
  have hs : √(kappa q + 5 / (n : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by
      have h : (5 : ℝ) / n ≤ 5 / n0 := div_le_div_of_nonneg_left (by norm_num) hn00 hnn
      linarith⟩
  have h12d : 2 * √(12 : ℝ) / n ≤ 2 * t / n0 := by
    calc 2 * √(12 : ℝ) / n ≤ 2 * t / n := by gcongr
      _ ≤ 2 * t / n0 := div_le_div_of_nonneg_left (by positivity) hn00 hnn
  have hm : meanRoot n q ≤ R := by
    unfold meanRoot
    linarith
  have hm0 : 0 ≤ meanRoot n q := by unfold meanRoot; positivity
  have hR0 : 0 ≤ R := hm0.trans hm
  have hg := (gMinus_lowerP h8 hn ht hs0 hst)
  have hgm : g0 ≤ gMinus n := hg0.trans hg
  have hg0' : 0 < gMinus n := lt_of_lt_of_le hg0p hgm
  have hratio : energyRatio n (gMinus n) q ≤ Q2 := by
    unfold energyRatio
    apply le_trans ?_ hQ2
    calc meanRoot n q ^ 2 / gMinus n ≤ meanRoot n q ^ 2 / g0 := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) hg0p hgm
      _ ≤ R ^ 2 / g0 := by gcongr
  have hr0' : 0 ≤ energyRatio n (gMinus n) q := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) hg0'.le
  have hQ20 : 0 ≤ Q2 := hr0'.trans hratio
  have hk := kappa_monotoneOn
    (show energyRatio n (gMinus n) q ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, by linarith⟩)
    (show Q2 ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, by linarith⟩) hratio
  have hk' := hk.trans hK2
  have hk0 := (kappa_mem (by linarith : -1 ≤ energyRatio n (gMinus n) q)
    (by linarith : energyRatio n (gMinus n) q ≤ 1)).1
  have hgp : BstLean.Part211.gPlus n ≤ G := (gPlus_upperP h8 hn ht).trans hG
  have hgp0 : 0 ≤ BstLean.Part211.gPlus n := le_trans zero_le_one (BstLean.Part264.gPlus_lower n)
  have hG0 : 0 ≤ G := hgp0.trans hgp
  have hT1 : √(BstLean.Part211.gPlus n * kappa (energyRatio n (gMinus n) q)) ≤ T := by
    apply sqrt_le_iff.mpr
    refine ⟨hT, ?_⟩
    exact (mul_le_mul hgp hk' hk0 hG0).trans hTsq
  have ht2' : √(12 * BstLean.Part211.gPlus n) ≤ t2 :=
    (sqrt_le_sqrt (by linarith)).trans ht2
  have ht20 : 0 ≤ t2 := (sqrt_nonneg _).trans ht2'
  have ht2d : 2 * √(12 * BstLean.Part211.gPlus n) / n ≤ 2 * t2 / n0 := by
    calc 2 * √(12 * BstLean.Part211.gPlus n) / n ≤ 2 * t2 / n := by gcongr
      _ ≤ 2 * t2 / n0 := div_le_div_of_nonneg_left (by positivity) hn00 hnn
  have hnr : r ≤ √(n : ℝ) := le_sqrt_of_sq_le (hr.trans hnn)
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  have hfd : finiteEnergy n n (11 / 1000) / √(n : ℝ) ≤ F / r :=
    div_le_div₀ (hf0.trans hF) hF hr0 hnr
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  apply le_trans ?_ hB
  have hbase : 0 ≤ √(BstLean.Part211.gPlus n * kappa (energyRatio n (gMinus n) q)) +
      2 * √(12 * BstLean.Part211.gPlus n) / n + finiteEnergy n n (11 / 1000) / √(n : ℝ) := by
    positivity
  exact pow_le_pow_left₀ hbase (by linarith) 2

end BstLean.Part277
