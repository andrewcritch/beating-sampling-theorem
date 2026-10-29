import BstLean.Part292Geometry

/-! The actual conditional table-node measure has order-twelve latitude cap .533. -/
namespace BstLean.Part292
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170
open BstLean.Part280 (nodeMeasureN nodeIndexN_measurable)

theorem latitude_coefficient_low {n : ℕ} (hn : 8000 ≤ n) :
    BstLean.Part212.latitudeCoefficient n 12 (528/1000) ≤ 53273/100000 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hd : 0 < 1-50*(528/1000 : ℝ)/n := by
    rw [sub_pos, div_lt_one hn0]
    linarith
  have he : BstLean.Part212.latitudeCoefficient n 12 (528/1000) =
      (528/1000 : ℝ)/(1-50*(528/1000)/n)*((n : ℝ)+45)/n := by
    unfold BstLean.Part212.latitudeCoefficient BstLean.Part212.inverseLatitudeCoefficient
    push_cast
    ring
  rw [he, div_mul_eq_mul_div, div_div, div_le_iff₀ (mul_pos hd hn0)]
  have hden : (1-50*(528/1000 : ℝ)/n)*(n : ℝ) = n-132/5 := by
    rw [sub_mul, div_mul_cancel₀ _ hn0.ne']
    ring
  rw [hden]
  linarith

theorem deltaP_low {n : ℕ} (hn : 8000 ≤ n) : DeltaP n ≤ 25/10^9 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : sqrt (55/100/(n : ℝ)) ≤ 83/10000 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ hn0]
    nlinarith
  unfold DeltaP
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem nodeMeasure_moment12_low {n : ℕ} (hn : 8000 ≤ n) {wr : WRet n}
    (hw : tableWorldGuard wr) :
    ∫⁻ g, ENNReal.ofReal ((1-nodeS (mkR wr (0,0)) g.val^2)^12)
      ∂nodeMeasureN (by omega) wr ≤ ENNReal.ofReal ((533/1000 : ℝ)^12) := by
  have hn1 : 1 ≤ n := by omega
  have htw : BstLean.Part276.tightW wr := ⟨hw.1, by linarith [hw.2]⟩
  have hW := BstLean.Part276.window_of_tightW hn1 htw (0 : AHid n)
  rw [nodeMeasureN, lintegral_map (measurable_of_finite _) (nodeIndexN_measurable hn1 wr)]
  have hδ : (0 : ℝ) < 1/10000 := by norm_num
  have h := BstLean.Part276.node_latitude_moment12 hn (mkR wr 0) hW hδ
  refine (le_of_eq_of_le ?_ h).trans (ENNReal.ofReal_le_ofReal ?_)
  · rfl
  have ht := BstLean.Part276.bulkTailMass_small hn (mkR wr 0) hW
  have hθ := BstLean.Part276.window_theta hn1 (mkR wr 0) hW
  have hθ0 : (0 : ℝ) ≤ BstLean.Part150.thetaC (mkR wr 0).1.2
      ((paperDesignP n).tau0 (mkR wr 0)) := by
    change (0 : ℝ) ≤ BstLean.Part150.thetaC (mkR wr 0).1.2 (tauR (mkR wr 0))
    linarith [hθ.1]
  have hθ1 : BstLean.Part150.thetaC (mkR wr 0).1.2 ((paperDesignP n).tau0 (mkR wr 0)) ≤
      528/1000 := hw.2
  have hmono := BstLean.Part212.latitudeCoefficient_mono (n := n) (p := 12) (by norm_num)
    (by omega) hθ0 hθ1 (by norm_num)
  have hpos := BstLean.Part212.latitudeCoefficient_pos (n := n) (p := 12) (by norm_num)
    (by omega) (mkR wr 0).1.2 hW.2.1
  have hL12 := pow_le_pow_left₀ hpos.le (hmono.trans (latitude_coefficient_low hn)) 12
  obtain ⟨hLH, _, hwidth⟩ := bulk_of_window (by omega) (mkR wr 0) hW.2.1 hθ.1
    (by linarith [hθ.2])
  have hD := hwidth.trans (deltaP_low hn)
  have hD0 : 0 ≤ nodeD (mkR wr 0) := by
    unfold nodeD Js
    have : 0 < nodeH (mkR wr 0)-nodeL (mkR wr 0) := by linarith
    positivity
  have hD12 : (nodeD (mkR wr 0)/(1/10000))^12 ≤ (25/10^5 : ℝ)^12 := by
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have hnum : (1+1/10000 : ℝ)^12*(53273/100000)^12+
      (1+1/10000 : ℝ)^12*(25/10^5)^12+5/10^17 ≤ (533/1000)^12 := by norm_num
  have h1 := mul_le_mul_of_nonneg_left hL12 (by positivity : (0 : ℝ) ≤ (1+1/10000)^12)
  have h2 := mul_le_mul_of_nonneg_left hD12 (by positivity : (0 : ℝ) ≤ (1+1/10000)^12)
  linarith

end BstLean.Part292
