import BstLean.Part280Root12224
import BstLean.Part280World
import BstLean.Part280Window

/-! Part 280: the 12224 certificate on the M2 route. The table event is the generic
M2 sharp table `sharpTableN 12224` (guard `θ ≤ .524`), paid by `sharpTableN_ret_charge`;
the row supplies the guard from its World package (`theta_le_of_noise`). -/
namespace BstLean.Part280
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169 BstLean.Part188
open BstLean.Part275

/-- The row guard of M2: the World angle bound. -/
def m2Guard (n : ℕ) (c : Ret n) : Prop :=
  BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ≤ 524 / 1000

theorem exactTableMoments_of_N {c : Ret 12224} (hw : WINDOW (paperDesignP 12224) c)
    (hθ : m2Guard 12224 c) (hc : c ∈ sharpTableN 12224) (K : Set (Ix 12224)) :
    BstLean.Part276.Row12224.ExactTableMoments c K := by
  have h := hc (tightG_of_window (by norm_num) c hw hθ)
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF
      (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE
      (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

/-- The M2-route certificate at 12224: root .0074488, table charge 9/10000. -/
noncomputable def m2Certificate12224 :
    SharpRootCertificate 12224 Row12224.rootTarget sharpCaps12224
      (sharpTableN 12224) (m2Guard 12224) where
  dimension := by norm_num
  table_measurable := sharpTableN_measurable
  source_charge := sourceChargeFn_le_part262 (le_refl _)
  table_payment := by
    change _ ≤ (9 / 10000 : ℝ)
    exact sharpTableN_ret_charge (by norm_num) (by norm_num)
  inputs := by
    intro t c hw hθ hc I hE
    have ha : c ∈ BstLean.Part275.Row12224.analyticBase := hc.1.1.1
    have hp : c ∈ BstLean.Part252.positiveOutputEvent (paperCentres 12224) := hc.1.1.2
    have he : 0 < eR c := by
      linarith [(BstLean.Part275.Row12224.centre_energy_range hw ha).1]
    have hm := low_mass_of_interfacesP (by norm_num) pilot_lowMass hw he I hE
    exact Row12224.sharpRootInputs t hw ha (exactTableMoments_of_N hw hθ hc.2) hp hm

/-- The M2 caps: the pilot caps with the M2 source charge .000601. -/
noncomputable def m2Caps : RootCaps := { pilotCaps with sourceCharge := 601 / 10 ^ 6 }

theorem m2Caps_charge : m2Caps.sourceCharge + m2Caps.tableCharge = 1501 / 10 ^ 6 := by
  norm_num [m2Caps, pilotCaps, part262Caps]

/-- For every n in 11883–12224, the M2 certificate needs only the pointwise root inputs:
dimension, source charge and the sharp table payment are proved here. -/
noncomputable def m2Certificate {n : ℕ} (hn : 11883 ≤ n) (hn2 : n ≤ 12224) {root : ℝ}
    (inputs : ∀ (t : ℝ) (c : Ret n), WINDOW (paperDesignP n) c → m2Guard n c →
      c ∈ sharpSourceBase n (sharpTableN n) →
      WFInterfaces (paperDesignP n) c m2Caps.Mcap (m2Caps.Hcap n) m2Caps.xiCap →
      centreEnergy (paperDesignP n) c ≤ m2Caps.Ecap →
      BstLean.Part243.RootInputs n t c root) :
    SharpRootCertificate n root m2Caps (sharpTableN n) (m2Guard n) where
  dimension := by omega
  table_measurable := sharpTableN_measurable
  source_charge := sourceChargeFn_le_m2 hn
  table_payment := by
    change _ ≤ (9 / 10000 : ℝ)
    exact sharpTableN_ret_charge hn hn2
  inputs := inputs

/-- The 12224 instance of the M2 constructor. -/
noncomputable def m2Certificate12224' :
    SharpRootCertificate 12224 Row12224.rootTarget m2Caps (sharpTableN 12224) (m2Guard 12224) :=
  m2Certificate (by norm_num) (by norm_num) m2Certificate12224.inputs

end BstLean.Part280
