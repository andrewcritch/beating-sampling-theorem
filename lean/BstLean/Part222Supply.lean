import BstLean.Part222CentreBounds

/-! The scalar S12 certificate and the sharp events supply the Agent mass formula. -/
namespace BstLean.Part222
open MeasureTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part188 BstLean.Part215
open BstLean.Part150 (thetaC)
open BstLean.Part211
open BstLean.Part154 (csC bN)

/-- All network-dependent conclusions follow from the source events.
The scalar certificate, the retained window and the selected cutoff remain explicit. -/
theorem agent_mass_of_certified_centre {n J : ℕ}
    (hn : 4096 ≤ n) (hn1 : n ≤ 16384) (hJ : 1 ≤ J) (D : Design n) (c : Ret n)
    (hc : 0 < normSq c.1.2) (hτ : 0 < D.tau0 c)
    (hb : D.bA c.1 c.2.1.1 = hiddenCentre (J := J)
      c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c))
    {δe k k3 θlo Θ S MP qWorld e xiF xiP E η u d : ℝ}
    (he : 0 < e) (hxiF : 0 ≤ xiF) (hxiP : 0 ≤ xiP) (hMP : 0 ≤ MP)
    (v : ℝ → ℝ) (C : CentreCertificate n J δe k k3 θlo Θ S MP qWorld v)
    (hθ : thetaC c.1.2 (D.tau0 c) ∈ Set.Icc θlo Θ)
    (hWorld : 1-thetaC c.1.2 (D.tau0 c) ≤ qWorld)
    (hq : 1-thetaC c.1.2 (D.tau0 c) ∈ Set.Icc (0 : ℝ) (27/50))
    (hfull : fullFormula n J δe k k3 θlo Θ S MP ≤ xiF)
    (hpar : parallelFormula n J δe (momentAllowance n csC δe k k3 Θ S)
      (bN n csC Θ) (√(momentAllowance n csC δe k k3 Θ S)+sharpDeviation n csC δe θlo Θ)
      Θ MP ≤ xiP)
    (hlow : e ≤ energyLower n (BstLean.Part211.gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n J δe) (thetaC c.1.2 (D.tau0 c)))
    (hup : BstLean.Part206.energyUpper n (BstLean.Part211.gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n J δe) qWorld ≤ E)
    (hopScalar : BstLean.Part219.operatorAllowance c.1.2 (D.tau0 c) η
      (ENNReal.ofReal (1/20000))^2 ≤ MP)
    (hbase : c.2.1.1 ∈ centreBase n J c.1.2 (D.tau0 c))
    (herr : c.2.1.1 ∈ sharpErrorEvent c.1.2 (D.tau0 c))
    (hop : c.2.1.1 ∈ operatorEvent c.1.2 (D.tau0 c) η (ENNReal.ofReal (1/20000)))
    (hen : c.2.1.1 ∈ energyEvent c.1.2 (D.tau0 c))
    (hu : 0 < u) (hu1 : u < 1) (hd : d < (1-u)^2)
    (hgap : 0 < √((1-u)^2-d)-(√E+√(xiP/n))) :
    WFInterfaces D c (BstLean.Part219.paperDirectionBudget c.1.2 (D.tau0 c) e xiF η
      (ENNReal.ofReal (1/20000))) (energyAllowance n) xiP ∧
    BstLean.Part160.CENTRE_at D c xiF ∧
    centreEnergy D c ≤ E ∧
    BstLean.Part160.MASS_at D c d
      (massBound n (BstLean.Part219.paperDirectionBudget c.1.2 (D.tau0 c) e xiF η
        (ENNReal.ofReal (1/20000))) (energyAllowance n) xiP E u d) := by
  have hδ : ENNReal.ofReal (1/20000 : ℝ) ≠ 0 := by norm_num
  have hSource := centreSource_on_operator_event c.1.2 (D.tau0 c) η MP hδ hbase hop
    (operatorXiAllowance_le c.1.2 (D.tau0 c) η MP _ hopScalar)
  have hC := centre_formula_junction hn hn1 hJ c.1.2 hc hτ hMP v C hθ hWorld hSource
  have hF := hC.1.trans hfull
  rw [fullError_normalization (by omega) D c hb] at hF
  have hP := hC.2.1.trans hpar
  have hEL : e ≤ centreEnergy D c := by
    rw [energy_normalization (by omega) D c hτ hb]
    exact hlow.trans hC.2.2.1
  have hEU : centreEnergy D c ≤ E := by
    rw [energy_normalization (by omega) D c hτ hb]
    exact hC.2.2.2.1.trans hup
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbn : (n : ℝ)*e ≤ normSq (D.bA c.1 c.2.1.1) := by
    simpa only [mul_comm] using (le_div_iff₀ hnR).mp hEL
  have hbpos : 0 < normSq (D.bA c.1 c.2.1.1) := (mul_pos hnR he).trans_le hbn
  have hI : WFInterfaces D c (BstLean.Part219.paperDirectionBudget c.1.2 (D.tau0 c) e xiF η
      (ENNReal.ofReal (1/20000))) (energyAllowance n) xiP :=
    ⟨BstLean.Part219.directionMoment_paper (by omega) D c hτ he hxiF hδ hq hbn hF herr hop,
      energyMoment_on_event (by omega) D c hen,
      parallelCentre_of_s12 (by omega) D c hb hbpos hxiP hP⟩
  have hb0 : ∀ j, 0 ≤ D.bA c.1 c.2.1.1 j := by
    intro j
    rw [hb]
    exact hiddenCentre_nonneg _ _ _ _ j
  exact ⟨hI,centre_at_of_raw_bound D c hF,hEU,
    sharp_residual_mass (by omega) D c hτ hbpos hb0 hI hEU hu hu1 hd hgap⟩

#print axioms agent_mass_of_certified_centre
end BstLean.Part222
