import BstLean.Part293SYPass
import BstLean.Part252Pass
import BstLean.Part248Network

/-! Actual paper-split moments enter the positive-floor SY interface without new integrability premises. -/
namespace BstLean.Part293
open Real MeasureTheory Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part242 BstLean.Part252

theorem paper_bias_reciprocal {n : ℕ} (hn : 1 ≤ n) (c : Ret n)
    {wl ws sigma eta d mu X4 X8 X12 Gamma : ℝ}
    (heta : 0 < eta) (heta1 : eta < 1) (hsigma : 0 ≤ sigma)
    (hd : 0 < d) (hY : 0 < 1 - mu ^ 2)
    (hscale : 2 / (n : ℝ) * d ≤ (1 - eta) * sigma ^ 2)
    (hdef : BstLean.Part248.DeficitOrders (muI n)
      (fun a => (dP c).Sb a / (2 / (n : ℝ))) (1 - mu ^ 2) X4 X8 X12)
    (hcap : BstLean.Part248.bound3 d (1 - mu ^ 2) X4 X8 X12 ≤ Gamma) :
    LBound ((muI n).restrict
      (keptIx (paperDesignP n) c
        (BstLean.Part162.dPaper (paperDesignP n) c wl ws sigma eta heta heta1))) 4
      (fun a => 1 / ((BstLean.Part162.dPaper (paperDesignP n) c wl ws sigma eta heta heta1).Sb a /
        (2 / (n : ℝ)))) Gamma := by
  let split := BstLean.Part162.dPaper (paperDesignP n) c wl ws sigma eta heta heta1
  let K := keptIx (paperDesignP n) c split
  have hK : MeasurableSet K := measurableSet_keptSet _ split.mgood (measurableSet_bulkIx _ c) _
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfloor : ∀ a ∈ K, d ≤ (dP c).Sb a / (2 / (n : ℝ)) := by
    intro a ha
    have h := hscale.trans (paper_scale_lower hn c hsigma heta heta1 ha)
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 / n)).mpr
    rw [mul_comm d (2 / (n : ℝ))]
    simpa only [dP, BstLean.Part162.dPaper] using h
  have h := BstLean.Part248.R_best hK (by simp) ((dP c).mSb.div_const _)
    hd hY hfloor hdef
  have hG : BstLean.Part248.bestBound d (1 - mu ^ 2) X4 X8 X12 ≤ Gamma :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans hcap
  exact ⟨h.measurable, h.nonneg.trans hG, h.bound.trans (ENNReal.ofReal_le_ofReal hG)⟩

structure PaperBiasMoments {n : ℕ} (c : Ret n) (K : Set (Ix n))
    (vmax aw af F8 F24 Cv : ℝ) : Prop where
  variance_max : ∀ a ∈ K, |VR c a| ≤ vmax
  energy_error : LBound ((muI n).restrict K) 8
    (fun a => (n : ℝ) * (wbR c a - wtR c a)) aw
  location_error : LBound ((muI n).restrict K) 8
    (fun a => (n : ℝ) * (fbR c a - ftR c a)) af
  location8 : LBound ((muI n).restrict K) 8 (fbR c) F8
  location24 : LBound ((muI n).restrict K) 24 (fbR c) F24
  variance_norm : LBound ((muI n).restrict K) 2 (fun a => (n : ℝ) * VR c a) Cv

theorem syInputs_of_paperMoments {n : ℕ} (hn : 1 ≤ n) (c : Ret n)
    {wl ws sigma eta floor chi d eps vmax aw af F8 F24 Gamma Cv : ℝ}
    (heta : 0 < eta) (heta1 : eta < 1) (hsigma : 0 ≤ sigma)
    (hfloor0 : 0 < floor) (he : 0 < eR c) (hd : floor ≤ d)
    (heps : eps < 1) (hthreshold : 0 < eps - vmax / d)
    (haw : 0 < aw) (haf : 0 < af) (hF24 : 0 < F24) (hCv : 0 < Cv)
    (hchi : 0 ≤ chi)
    (hscale : 2 / (n : ℝ) * d ≤ (1 - eta) * sigma ^ 2)
    (hcentre : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * chi)
    (P : PaperBiasMoments c
      (keptIx (paperDesignP n) c
        (BstLean.Part162.dPaper (paperDesignP n) c wl ws sigma eta heta heta1))
      vmax aw af F8 F24 Cv)
    (hreciprocal : LBound ((muI n).restrict
      (keptIx (paperDesignP n) c
        (BstLean.Part162.dPaper (paperDesignP n) c wl ws sigma eta heta heta1))) 4
      (fun a => 1 / ((BstLean.Part162.dPaper (paperDesignP n) c wl ws sigma eta heta heta1).Sb a /
        (2 / (n : ℝ)))) Gamma) :
    SYPassInputsFloor floor c
      (BstLean.Part162.dPaper (paperDesignP n) c wl ws sigma eta heta heta1)
      chi d eps vmax aw af F8 F24 Gamma Cv := by
  refine {
    floor_pos := hfloor0
    he := he
    hd := hd
    hε := heps
    hT := hthreshold
    haw := haw
    haf := haf
    hF24 := hF24
    hCv := hCv
    hχ := hchi
    hSbd := fun a ha => hscale.trans (paper_scale_lower hn c hsigma heta heta1 ha)
    hc := hcentre
    hVm := ?_
    hW := P.energy_error
    hF := ?_
    hf8 := ?_
    hf24 := ?_
    hR := hreciprocal
    hV := ?_ }
  · simpa only [BstLean.Part241.varianceTerm_dPaper] using P.variance_max
  · simpa only [BstLean.Part241.fullF_dPaper] using P.location_error
  · simpa only [BstLean.Part241.fullF_dPaper] using P.location8
  · simpa only [BstLean.Part241.fullF_dPaper] using P.location24
  · simpa only [BstLean.Part241.varianceTerm_dPaper] using P.variance_norm

end BstLean.Part293

/-- info: 'BstLean.Part293.syInputs_of_paperMoments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.syInputs_of_paperMoments
