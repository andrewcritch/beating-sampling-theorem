import BstLean.Part285IntervalTable
import BstLean.Part285IntervalPilotA
import BstLean.Part285Root
import BstLean.Part280Cert12224

/-! The interval sharp-table transfer and root constructor. -/
namespace BstLean.Part285.Interval
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part162
open BstLean.Part252 BstLean.Part275
open BstLean.Part276 (tableF tableW)
open BstLean.Part280
open BstLean.Part150 (c1F c2F)

variable {n : ℕ}

theorem bulk_radius (hn : 12000 ≤ n) : (63 / 100 : ℝ) ≤ √(qB n) := by
  have hl : (12000 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 := sqrt_le_iff.mpr (by norm_num)
  have h2 : √(55 / 100 / (n : ℝ)) ≤ 678 / 100000 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ hp]
    nlinarith
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) := by positivity
  apply le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem bulk_positive (hn : 12000 ≤ n) : 0 < qB n :=
  sqrt_pos.mp (lt_of_lt_of_le (by norm_num) (bulk_radius hn))

/-- Scalar bounds for one entire band. These fields contain no network data. -/
structure SharpNumerics (n : ℕ) (aw af : ℝ) where
  dimension : 12000 ≤ n ∧ n ≤ 16199
  O : ℝ
  sigma : ℝ
  er : ℝ
  eg : ℝ
  lr : ℝ
  lg : ℝ
  operator_pos : 0 < O
  sigma_pos : 0 < sigma
  operator : firstOp n ≤ O
  variance : 2 / (n : ℝ) ^ 2 * ((n : ℝ) * O ^ 2 / ((n : ℝ) - 1)) ≤ sigma ^ 2
  location_grid : ∀ d : ℝ, d ≤ DeltaP n →
    (n : ℝ) * (283 / 100 * O * (d / 2) / (√(n : ℝ) * √(qB n))) ≤ lg
  energy_grid : ∀ d : ℝ, d ≤ DeltaP n →
    (n : ℝ) * (2 * (283 / 100 * O) ^ 2 * (d / 2) / (n * √(qB n))) ≤ eg
  location_rule : (n : ℝ) * (√(n : ℝ) *
    (c1F (exp (1 / 2) / 12) (Jz n) * sigma / Jz n)) ≤ lr
  energy_rule : (n : ℝ) * (n *
    (c2F (exp (1 / 2) / 12) (Jz n) * sigma ^ 2 / Jz n)) ≤ er
  location_total : tableF + lr + lg ≤ af
  energy_total : tableW + er + eg ≤ aw

theorem node_variance {aw af : ℝ} (S : SharpNumerics n aw af)
    (c : Ret n) (hc : A1 c ∈ BstLean.Part153.Eop n) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ S.sigma ^ 2 := by
  have hn := S.dimension.1
  have hl : (12000 : ℝ) ≤ n := by exact_mod_cast hn
  have hop : BstLean.Part152.opN (A1 c) ≤ S.O := hc.trans S.operator
  have hop2 := pow_le_pow_left₀ (BstLean.Part152.opN_nonneg (A1 c)) hop 2
  have hm : (1 - s ^ 2) * ((n : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      n * S.O ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (Nat.cast_nonneg n)) (by positivity) (by norm_num)
    simpa only [one_mul] using hh
  refine (vsig2_le (by omega) c hs).trans ?_
  have hb := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hm (by linarith : (0 : ℝ) ≤ n - 1))
    (by positivity : (0 : ℝ) ≤ 2 / (mA n : ℝ))
  norm_num only [mA, Nat.cast_pow] at hb ⊢
  exact hb.trans S.variance

theorem stored_moments {aw af : ℝ} (S : SharpNumerics n aw af)
    (c : Ret n) (hw : WINDOW (paperDesignP n) c)
    (hθ : m2Guard n c) (ht : c ∈ sharpTableN n)
    (hfirst : A1 c ∈ BstLean.Part153.Eop n) (hsecond : c ∈ BstLean.Part164.Eop2 n)
    {K : Set (Ix n)} (hK : MeasurableSet K) (hsub : K ⊆ bulkIx (paperDesignP n) c) :
    (∫ a in K, ((n : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI n ≤ aw ^ 8) ∧
    (∫ a in K, ((n : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI n ≤ af ^ 8) := by
  have hn := S.dimension.1
  letI : Fact (12000 ≤ n ∧ n ≤ 16199) := ⟨S.dimension⟩
  have h1 := first_matrix_exact c S.operator hfirst
  have h2 := PilotA.second_matrix_row c hsecond
  have hwin := BstLean.Part276.tightW_of_window (by omega) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by omega) c hwin.1.1 hwin.1.2.1 hwin.1.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ S.sigma ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by omega) (latC (paperDesignP n) c a))
    have hs := hbulk _ hs1 hs2
    exact node_variance S c hfirst (by change _ ≤ 1; unfold sgR; linarith [bulk_positive hn])
  obtain ⟨MF, bF⟩ := bdd_exF (by omega) c
  obtain ⟨MW, bW⟩ := bdd_exW (by omega) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8) (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8) (bdd_pow bW 8) K
  have iFu := intOn_of_bdd ((measurable_exF c).pow_const 8) (bdd_pow bF 8) Set.univ
  have iWu := intOn_of_bdd ((measurable_exW c).pow_const 8) (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at iFu iWu
  have ht' := ht (tightG_of_window (by omega) c hw hθ)
  have hF := (setIntegral_le_integral (s := K) iFu
    (Filter.Eventually.of_forall fun a => by positivity)).trans ht'.1
  have hW := (setIntegral_le_integral (s := K) iWu
    (Filter.Eventually.of_forall fun a => by positivity)).trans ht'.2
  have hf := location_error_of_exact (by omega) c hK hsub h1 h2
    S.operator_pos (by norm_num) (bulk_positive hn) S.sigma_pos hLH hbulk hvs
    (by norm_num [tableF] : (0 : ℝ) < tableF) iF hF
  have he := energy_error_of_exact (by omega) c hK hsub h1 h2
    S.operator_pos (by norm_num) (bulk_positive hn) S.sigma_pos hLH hbulk hvs
    (by norm_num [tableW] : (0 : ℝ) < tableW) iW hW
  have hfg := S.location_grid _ hwidth
  have heg := S.energy_grid _ hwidth
  have hO0 := S.operator_pos.le
  have hs0 := S.sigma_pos.le
  have htF0 : 0 ≤ tableF := by norm_num [tableF]
  have htW0 : 0 ≤ tableW := by norm_num [tableW]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by positivity)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz n)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz n)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    linarith [S.energy_rule, S.energy_total]
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    linarith [S.location_rule, S.location_total]

noncomputable def pilotSplit (c : Ret n) : SplitData n :=
  PilotA.rowSplit c (PilotA.splitLocationWidth c) (PilotA.splitResidualWidth (n := n))

def PilotLowMass (c : Ret n) : Prop :=
  ∫ a, (BstLean.Part29.stdGauss (Fin (n - 1))).real
    {v | sgA (paperDesignP n) c a v < √(2 / (n : ℝ) * PilotA.mixtureFloor)}
    ∂muI n ≤ PilotA.lowMassBudget

noncomputable def intervalCaps (tb : ℝ) : RootCaps :=
  {m2Caps with sourceCharge := 601 / 10 ^ 6, tableCharge := tb}

theorem sharp_passes {aw af : ℝ} (S : SharpNumerics n aw af)
    (haw : 0 < aw) (haw1 : aw ≤ PilotA.energyError)
    (haf : 0 < af) (haf1 : af ≤ PilotA.locationError)
    {c : Ret n} (hw : WINDOW (paperDesignP n) c) (hθ : m2Guard n c)
    (hc : c ∈ sharpSourceBase n (sharpTableN n)) :
    BstLean.Part241.PassInputs c (pilotSplit c) PilotA.chi PilotA.biasFloor
      PilotA.epsilon PilotA.varianceMax aw af PilotA.locationNorm PilotA.varianceNorm := by
  letI : Fact (12000 ≤ n ∧ n ≤ 16199) := ⟨S.dimension⟩
  have hn := S.dimension.1
  have ha : c ∈ PilotA.analyticBase := hc.1.1.1
  have he : 0 < eR c := by linarith [(PilotA.centre_energy_range hw ha).1]
  have hp := PilotA.analyticBaseCertificate.pass_fields ha
  have hK : MeasurableSet (keptIx (paperDesignP n) c (pilotSplit c)) :=
    measurableSet_keptSet _ (pilotSplit c).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP n) c (pilotSplit c) ⊆ bulkIx (paperDesignP n) c := fun _ h => h.1
  have htab := stored_moments S c hw hθ hc.2 (hp.1.1.2 hw.2.1) hp.1.2 hK hsub
  have hpm := PilotA.pass_moments_of_events c hw he hp _
    (htab.1.trans (pow_le_pow_left₀ haw.le haw1 8))
    (htab.2.trans (pow_le_pow_left₀ haf.le haf1 8))
  have hm : PaperMoments c (keptIx (paperDesignP n) c (pilotSplit c))
      PilotA.varianceMax aw af PilotA.locationNorm PilotA.varianceNorm :=
    ⟨hpm.variance, htab.1, htab.2, hpm.location4, hpm.location24, hpm.variance2⟩
  exact passInputs_of_paperMoments (by omega) c PilotA.eta_pos PilotA.eta_lt_one
    (sqrt_nonneg _) he (by norm_num [PilotA.biasFloor, PilotA.eta, PilotA.mixtureFloor])
    (by norm_num [PilotA.epsilon])
    (by norm_num [PilotA.epsilon, PilotA.varianceMax, PilotA.biasFloor, PilotA.eta, PilotA.mixtureFloor])
    haw haf (by norm_num [PilotA.locationNorm]) (by norm_num [PilotA.varianceNorm])
    PilotA.row_split_floor.le (PilotA.pass_centre_of_events c hp) hm

/-- A complete certificate once the scalar band and the proved HQ bound are supplied. -/
noncomputable def intervalCertificate {aw af hq bias root tb : ℝ}
    (S : SharpNumerics n aw af)
    (haw : 0 < aw) (haw1 : aw ≤ PilotA.energyError)
    (haf : 0 < af) (haf1 : af ≤ PilotA.locationError)
    (hprice : (retDist (paperCentres n)).real (sharpTableN n)ᶜ ≤ tb)
    (hbias : BstLean.Part241.biasRoot n PilotA.chi PilotA.biasFloor PilotA.epsilon
      PilotA.varianceMax aw af PilotA.locationNorm PilotA.varianceNorm ≤ bias)
    (hroot : hq + bias + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ root)
    (hHQ : ∀ (t : ℝ) (c : Ret n), WINDOW (paperDesignP n) c →
      c ∈ PilotA.analyticBase → c ∈ positiveOutputEvent (paperCentres n) →
      PilotLowMass c → FLUCT_hyp (paperDesignP n) t c (pilotSplit c) hq) :
    SharpRootCertificate n root (intervalCaps tb) (sharpTableN n) (m2Guard n) where
  dimension := by have := S.dimension; omega
  table_measurable := sharpTableN_measurable
  source_charge := sourceChargeFn_le_m2 (by have := S.dimension; omega)
  table_payment := hprice
  inputs := by
    intro t c hw hθ hc I hE
    letI : Fact (12000 ≤ n ∧ n ≤ 16199) := ⟨S.dimension⟩
    have hn := S.dimension.1
    have ha : c ∈ PilotA.analyticBase := hc.1.1.1
    have hp : c ∈ positiveOutputEvent (paperCentres n) := hc.1.1.2
    have he : 0 < eR c := by linarith [(PilotA.centre_energy_range hw ha).1]
    have hlm : LowMassNumerics n (intervalCaps tb).Mcap ((intervalCaps tb).Hcap n)
        (intervalCaps tb).xiCap (intervalCaps tb).Ecap (intervalCaps tb).u
        PilotA.mixtureFloor (intervalCaps tb).lowMassBudget (414 / 10000) := by
      simpa [intervalCaps, m2Caps, pilotCaps, part262Caps, PilotA.mixtureFloor]
        using lowMass_m2 (n := n) (by omega)
    have hm := low_mass_of_interfacesP (by omega) hlm hw he I hE
    refine ⟨pilotSplit c, PilotA.chi, PilotA.biasFloor, PilotA.epsilon, PilotA.varianceMax,
      aw, af, PilotA.locationNorm, PilotA.varianceNorm, 0, hq, 0, hw,
      sharp_passes S haw haw1 haf haf1 hw hθ hc, ?_, ?_⟩
    · simpa [PilotLowMass, intervalCaps, m2Caps, pilotCaps, part262Caps, PilotA.lowMassBudget]
        using hHQ t c hw ha hp hm
    · simp only [mul_zero, sqrt_zero, zero_add, add_zero]
      linarith

end BstLean.Part285.Interval
