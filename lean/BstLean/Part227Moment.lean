import BstLean.Part227Window
import BstLean.Part210All

/-! Part 227: the restricted World moment with the computed centre and scale. -/
namespace BstLean.Part227
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 BstLean.Part140 BstLean.Part157 BstLean.Part159

noncomputable def momentValue (n : ℕ) (Alo Ahi ζ : ℝ) : ℝ :=
  vPert n (√(perturbation n)) (BstLean.Part210.Rnew n / √(mW n : ℝ))
    Alo Ahi (1001 / 1000) ζ

/-- Every measurable restriction keeps the same unnormalized moment formula. -/
theorem hidden_moment {n : ℕ} (hn : 4096 ≤ n) {eB Alo Ahi ζ : ℝ}
    {G : Set (WHid n)} (mG : MeasurableSet G)
    (hG : G ⊆ (goodB n eB ∩ goodS n) ∩ goodAo n)
    (hL : 0 ≤ kap1 (2 * n) - eB)
    (hLE : √(perturbation n) ≤ √(kap1 (2 * n) - eB))
    (hk : kernelError n < kap1 (2 * n))
    (hAlo : 1 < Alo) (hlo : Alo ≤ productLower n eB)
    (hhi : productUpper n eB ≤ Ahi) (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ K : WHid n → ℝ, Integrable (G.indicator K) (hidGauss (2 * n) (mW n)) ∧
      (∀ θ ∈ G, hellHid bWp tau0p θ ≤ K θ) ∧
      (∫ θ, G.indicator K θ ∂hidGauss (2 * n) (mW n)) ≤ momentValue n Alo Ahi ζ := by
  have hpert : 0 ≤ perturbation n := by unfold perturbation; positivity
  have hρ : 0 ≤ BstLean.Part210.Rnew n / √(mW n : ℝ) := by
    unfold BstLean.Part210.Rnew; positivity
  have hwin : ∀ θ ∈ G, Alo ≤ 2 / (mW n : ℝ) * normSq (bWp θ) * ccP n θ ∧
      2 / (mW n : ℝ) * normSq (bWp θ) * ccP n θ ≤ Ahi := by
    intro θ hθ
    have hp := hG hθ
    obtain ⟨hl, hu⟩ := product_window hn hp.1.1 hp.1.2 hp.2 hL hLE hk
    exact ⟨hlo.trans hl, hu.trans hhi⟩
  exact pert_moment hn measurable_bWp measurable_ccP mG
    (Real.sqrt_nonneg _) hρ hAlo (by norm_num) hζ0 hζ1
    (fun θ hθ => by
      rw [Real.sq_sqrt hpert]
      exact BstLean.Part204.bWp_dist hn (BstLean.Part201.constC hn) (hG hθ).1.2 (hG hθ).2)
    (fun θ hθ => ⟨by
      have hs : 0 ≤ SWp θ := SWp_nonneg θ
      unfold ccP
      positivity,
      (BstLean.Part204.pap_q hn (BstLean.Part201.constK hn) (hG hθ).1.2).1⟩)
    hwin (fun θ hθ => tau0p_of (hAlo.trans_le (hwin θ hθ).1))
    (BstLean.Part210.restricted_calibration hn mG (fun _ h => (hG h).1.2))

/-- The scale identity follows from the certified product lower bound. -/
theorem scale_identity {n : ℕ} (hn : 4096 ≤ n) {θ : WHid n} {eB Alo : ℝ}
    (hB : θ ∈ goodB n eB) (hS : θ ∈ goodS n) (hA : θ ∈ goodAo n)
    (hL : 0 ≤ kap1 (2 * n) - eB)
    (hLE : √(perturbation n) ≤ √(kap1 (2 * n) - eB))
    (hk : kernelError n < kap1 (2 * n)) (hAlo : 1 < Alo)
    (hlo : Alo ≤ productLower n eB) :
    0 < tau0p θ ∧ tau0p θ ^ 2 = 2 / (mW n : ℝ) * normSq (bWp θ) *
      (2 / (mW n : ℝ) * normSq (bWp θ) * ccP n θ - 1) := by
  have h := tau0p_of (hAlo.trans_le (hlo.trans (product_window hn hB hS hA hL hLE hk).1))
  exact ⟨h.2, h.1⟩

/-- The transfer uses exactly the design centre and scalar, including all retained coordinates. -/
theorem retained_moment {n : ℕ} (hn : 4096 ≤ n) (D : Design n)
    (hD : D.bW = bWp) (hτ : ∀ c, D.tau0 c = tau0p c.1.1)
    {eB Alo Ahi ζ : ℝ} {G : Set (WHid n)} (mG : MeasurableSet G)
    (hG : G ⊆ (goodB n eB ∩ goodS n) ∩ goodAo n)
    (hL : 0 ≤ kap1 (2 * n) - eB)
    (hLE : √(perturbation n) ≤ √(kap1 (2 * n) - eB))
    (hk : kernelError n < kap1 (2 * n))
    (hAlo : 1 < Alo) (hlo : Alo ≤ productLower n eB)
    (hhi : productUpper n eB ≤ Ahi) (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    IntegrableOn (fun c => HbarW D c ^ 2) (Hof G) (retDist D.toCentres) ∧
      (∫ c in Hof G, HbarW D c ^ 2 ∂retDist D.toCentres) ≤ momentValue n Alo Ahi ζ := by
  obtain ⟨K, iK, hK, hI⟩ := hidden_moment hn mG hG hL hLE hk hAlo hlo hhi hζ0 hζ1
  refine ⟨integrableOn_HbarW_sq (by omega) D _, (moment_of_hid (by omega) D mG iK ?_).trans hI⟩
  intro c hc
  rw [HbarW2_eq_hellHid D c (hτ c), hD]
  exact hK c.1.1 hc

/-- The hidden event supplies the formula on every measurable subset. -/
theorem hidden_event_moment {n : ℕ} (hn : 4096 ≤ n) (D : Design n)
    (hD : D.bW = bWp) (hτ : ∀ c, D.tau0 c = tau0p c.1.1)
    {sp p₂ Xc dT eB Alo Ahi ζ : ℝ}
    (hL : 0 ≤ kap1 (2 * n) - eB)
    (hLE : √(perturbation n) ≤ √(kap1 (2 * n) - eB))
    (hk : kernelError n < kap1 (2 * n))
    (hAlo : 1 < Alo) (hlo : Alo ≤ productLower n eB)
    (hhi : productUpper n eB ≤ Ahi) (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    (∫ c in Hof (hidden n sp p₂ Xc dT eB), HbarW D c ^ 2 ∂retDist D.toCentres) ≤
      momentValue n Alo Ahi ζ :=
  (retained_moment hn D hD hτ (hidden_meas (by omega) _ _ _ _ _)
    (fun _ h => ⟨⟨h.2, h.1.1.2⟩, h.1.2⟩) hL hLE hk hAlo hlo hhi hζ0 hζ1).2

end BstLean.Part227
#print axioms BstLean.Part227.hidden_moment
#print axioms BstLean.Part227.scale_identity
#print axioms BstLean.Part227.retained_moment
#print axioms BstLean.Part227.hidden_event_moment
