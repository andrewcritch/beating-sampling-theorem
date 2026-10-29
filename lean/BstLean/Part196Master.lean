import BstLean.Part192Packages
import BstLean.Part158Final

/-! Part 196: the network master with variable parameters.
All input averages use the same stand-in distribution. -/
namespace BstLean.Part196
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part156

/-- The network master retains every scalar guard and charges the retained complement once. -/
theorem network_master {n : ℕ} (hn : 1 ≤ n) (D : Design n) (t : ℝ) (k : ℕ)
    {cW cf hW hA ds a τp τm δhid vW δextra : ℝ}
    (hcW : 0 < cW) (hcf : 0 < cf) (hhW : 0 < hW)
    (hhA : 0 ≤ hA) (hds : 0 < ds) (ha : 1 < a)
    (hτp : 0 < τp) (hτm : τm < 0)
    (hside1 : hA + ds + hW < √(1 / 100 / a))
    (hside2 : 2 * (hA + ds) ≤ √(1 / 100 / a))
    (hEp : Eplus a (hA + ds) hW cW cf τp ≤ 0)
    (hEm : Eminus a (hA + ds) hW cW cf τm ≤ 0)
    {H E₁ : Set (Ret n)}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hFW : FRAME_W_hyp D.toCentres (cW / n) (goodSet H E₁ (HbarW D) hW))
    (hFA : FRAME_A_hyp D (cf / n) (goodSet H E₁ (HbarW D) hW))
    (hRA : REPLA_mix_hyp D t hA (goodSet H E₁ (HbarW D) hW)) :
    ((mlpTriple 2 n).prod (sampMeas k n)).real (failNet D t a k) ≤
      δhid + vW / hW ^ 2 + δextra + Bplus n a (hA + ds) hW cW cf τp +
        Bminus n a (hA + ds) hW cW cf τm + 2 * exp (-(k : ℝ) * ds ^ 2) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hLW : 0 < cW / (n : ℝ) := div_pos hcW hnpos
  have hLA : 0 < cf / (n : ℝ) := div_pos hcf hnpos
  have hG := BstLean.Part158.gaussFrameMGF
  have hGPW := gpw_of_frame hn hG D.toCentres t hLW hFW
  have hGPA := gpa_of_frame hn hG D t hLA hFA
  have hRW := replw_of_test hn D t (replw_test_of_Hbar hn D hW H E₁)
  have hRA' := repla_of_mix D t hRA
  obtain ⟨hH, hE₁, hHm, hhid, hHint, hvW, hextra⟩ := hEv
  have mr := measurable_retVal D.toCentres
  have hmap := noise_retVal D.toCentres
  have mpair : Measurable (fun x : Ret n × (ResW n × ResA n) => (retVal D.toCentres x.1, x.2)) :=
    (mr.comp measurable_fst).prodMk measurable_snd
  have hpm : Measurable (fun x : Ret n × (ResW n × ResA n) =>
      pRes D.toCentres t (retVal D.toCentres x.1) x.2) := by
    have h := (measurable_pRes D.toCentres t).comp mpair
    exact h
  have hp0 : ∀ x : Ret n × (ResW n × ResA n),
      0 ≤ pRes D.toCentres t (retVal D.toCentres x.1) x.2 := fun x => pRes_nonneg _ _ _ _
  have hp1 : ∀ x : Ret n × (ResW n × ResA n),
      pRes D.toCentres t (retVal D.toCentres x.1) x.2 ≤ 1 := fun x => pRes_le_one hn _ _ _ _
  have hPm : ∀ c : Ret n, Measurable (PStand D t (retVal D.toCentres c)) :=
    fun c => measurable_PStand D t _
  have hP0 : ∀ (c : Ret n) (x : ResA n), 0 ≤ PStand D t (retVal D.toCentres c) x :=
    fun c x => PStand_nonneg _ _ _ _
  have hP1 : ∀ (c : Ret n) (x : ResA n), PStand D t (retVal D.toCentres c) x ≤ 1 :=
    fun c x => PStand_le_one _ _ _ _
  have hXm : ∀ i : Fin k, Measurable (fun x : Ret n × (Fin k → DrawSp n) =>
      hits D t k i (retVal D.toCentres x.1, x.2)) := by
    intro i
    have h1 : Measurable (fun x : Ret n × (Fin k → DrawSp n) =>
        (retVal D.toCentres x.1, x.2)) := (mr.comp measurable_fst).prodMk measurable_snd
    have h2 := (measurable_hits D t k i).comp h1
    exact h2
  have hX01 : ∀ (i : Fin k) (x : Ret n × (Fin k → DrawSp n)),
      hits D t k i (retVal D.toCentres x.1, x.2) = 0 ∨
        hits D t k i (retVal D.toCentres x.1, x.2) = 1 :=
    fun i x => hits_01 D t k i _
  have hH' : MeasurableSet (retVal D.toCentres ⁻¹' H) := mr hH
  have hE₁' : MeasurableSet (retVal D.toCentres ⁻¹' E₁) := mr hE₁
  have hHm' : Measurable (fun c => HbarW D (retVal D.toCentres c)) := hHm.comp mr
  have hhid' : (noiseC n).real (retVal D.toCentres ⁻¹' H)ᶜ ≤ δhid := by
    have e : (retVal D.toCentres ⁻¹' H)ᶜ = retVal D.toCentres ⁻¹' Hᶜ := rfl
    rw [e, ← map_measureReal_apply mr hH.compl, hmap]
    exact hhid
  have hHint' : IntegrableOn (fun c => HbarW D (retVal D.toCentres c) ^ 2)
      (retVal D.toCentres ⁻¹' H) (noiseC n) := by
    have h1 : Integrable (fun c => HbarW D c ^ 2) ((retDist D.toCentres).restrict H) := hHint
    rw [← hmap, Measure.restrict_map mr hH] at h1
    exact (integrable_map_measure ((hHm.pow_const 2).aestronglyMeasurable) mr.aemeasurable).1 h1
  have hvW' : ∫ c in retVal D.toCentres ⁻¹' H, HbarW D (retVal D.toCentres c) ^ 2 ∂noiseC n ≤
      vW := by
    have h1 := setIntegral_map (μ := noiseC n) hH
      (f := fun c => HbarW D c ^ 2) (g := retVal D.toCentres)
      ((hHm.pow_const 2).aestronglyMeasurable) mr.aemeasurable
    rw [hmap] at h1
    rw [← h1]
    exact hvW
  have hextra' : (noiseC n).real (retVal D.toCentres ⁻¹' H ∩ (retVal D.toCentres ⁻¹' E₁)ᶜ) ≤
      δextra := by
    have e : retVal D.toCentres ⁻¹' H ∩ (retVal D.toCentres ⁻¹' E₁)ᶜ =
        retVal D.toCentres ⁻¹' (H ∩ E₁ᶜ) := rfl
    rw [e, ← map_measureReal_apply mr (hH.inter hE₁.compl), hmap]
    exact hextra
  have key := master_sampling (noiseC n) (resW n) (resA n) (sampMeas k n)
    (p := fun x : Ret n × (ResW n × ResA n) => pRes D.toCentres t (retVal D.toCentres x.1) x.2)
    hpm hp0 hp1
    (P := fun c => PStand D t (retVal D.toCentres c)) hPm hP0 hP1
    (X := fun i (x : Ret n × (Fin k → DrawSp n)) =>
      hits D t k i (retVal D.toCentres x.1, x.2)) hXm hX01
    (qt := fun c => qTilde D t (retVal D.toCentres c))
    (H := retVal D.toCentres ⁻¹' H) (E₁ := retVal D.toCentres ⁻¹' E₁) hH' hE₁'
    (Hbar := fun c => HbarW D (retVal D.toCentres c)) hHm'
    (n := (n : ℝ)) (cW := cW) (cf := cf) (hW := hW) (hA := hA) (ds := ds) (a := a)
    (τp := τp) (τm := τm) (δhid := δhid) (δextra := δextra) (vW := vW)
    hnpos hcW hcf hhW
    hhA hds ha
    hτp hτm hside1 hside2
    hEp hEm hhid' hHint' hvW' hextra'
    (fun c hc ωA s => hGPW (retVal D.toCentres c) hc ωA s)
    (fun c hc u => hGPA (retVal D.toCentres c) hc u)
    (fun c hc ωA => hRW (retVal D.toCentres c) hc ωA)
    (fun c hc => hRA' (retVal D.toCentres c) hc)
    (fun c _ => hits_indep D t k (retVal D.toCentres c))
    (fun c _ i => hits_mean D t k (retVal D.toCentres c) i)

  rw [failNet_eq]
  exact key

end BstLean.Part196
