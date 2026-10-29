import BstLean.Part293FullMoments
import BstLean.Part293PaperPass
import BstLean.Part293Stored

/-! Fixed bias inputs from the same WF, latitude and stored-table records. -/
namespace BstLean.Part293
open Real MeasureTheory Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part188 BstLean.Part242 BstLean.Part248 BstLean.Part289
open BstLean.Part293.Model

noncomputable def biasSplit {n : ℕ} (c : Ret n) : SplitData n :=
  dPaper (paperDesignP n) c (lowMixtureWidth n / √(eR c))
    (√(2 / (n : ℝ)) * lowMixtureWidth n) (√((2 / (n : ℝ)) * 0.18))
    0.0045 (by norm_num) (by norm_num)

theorem biasInputs_of_model {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882) (c : Ret n)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP n).tau0 c) (hb : 0 < normSq (bR c))
    (hI : WFInterfaces (paperDesignP n) c agentDirectionCap
      (agentEnergyMomentCap / n) agentParallelCap)
    (hE : centreEnergy (paperDesignP n) c ≤ agentEnergyCap)
    (hk : BstLean.Part160.agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (3.042 / n)))
    (hcentre : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * 1.081)
    (hV : ∀ a ∈ keptIx (paperDesignP n) c (biasSplit c), |VR c a| ≤ 0.00411)
    (S : StoredInputs c (keptIx (paperDesignP n) c (biasSplit c)) 0.1802 0.05125) :
    SYPassInputsFloor (scaleFloor n) c (biasSplit c)
      1.081 0.17919 0.028 0.00411 0.1802 0.05125 0.85428 0.86139 3.721 0.0003804 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have he : 0 < eR c := div_pos hb (by linarith)
  have hx0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have hx1 : 1 / (n : ℝ) ≤ 1 / 8000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have hscale : 2 / (n : ℝ) * 0.17919 ≤
      (1 - 0.0045) * √((2 / (n : ℝ)) * 0.18) ^ 2 := by
    rw [sq_sqrt (by positivity)]
    norm_num <;> ring_nf <;> rfl
  have hY : 0 < 1 - lowMixtureMean n ^ 2 := by
    rw [lowMean_normalized, ← Envelope.Y0_formula]
    exact lt_of_lt_of_le (by norm_num) (Envelope.Y0_bounds _ hx0 hx1).1
  have hdef := D1_from_WF (by omega) c hc hτ hb hI hE
  have hGamma : bound3 0.17919 (lowMixtureY n) (lowMixtureX n 4)
      (lowMixtureX n 8) (lowMixtureX n 12) ≤ (3.721 : ℝ) := by
    rw [lowBiasReciprocal_normalized]
    exact (Envelope.Gamma_bounds _ hx0 hx1).2.trans (by norm_num)
  have hreciprocal := paper_bias_reciprocal (by omega) c
    (wl := lowMixtureWidth n / √(eR c)) (ws := √(2 / (n : ℝ)) * lowMixtureWidth n)
    (by norm_num : (0 : ℝ) < 0.0045) (by norm_num : (0.0045 : ℝ) < 1)
    (sqrt_nonneg ((2 / (n : ℝ)) * 0.18)) (by norm_num : (0 : ℝ) < 0.17919)
    hY hscale hdef hGamma
  obtain ⟨hW, hF⟩ := stored_norms_of_table hn c S
  obtain ⟨hf8, hf24⟩ := full_location_caps hn c hc hτ hb hI hE
    (keptIx (paperDesignP n) c (biasSplit c))
  have hv := full_variance_cap hn c he hk (keptIx (paperDesignP n) c (biasSplit c))
  have hfloor : scaleFloor n = (0.17 : ℝ) := by
    rw [scaleFloor_low (by omega)]
    norm_num
  apply syInputs_of_paperMoments (by omega) c (by norm_num) (by norm_num)
    (sqrt_nonneg _) (by rw [hfloor]; norm_num) he (by rw [hfloor]; norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hscale hcentre
    ⟨hV, hW, hF, hf8, hf24, hv⟩ hreciprocal

end BstLean.Part293
