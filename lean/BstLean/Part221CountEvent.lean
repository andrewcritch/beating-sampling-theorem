import BstLean.Part221PlaneMoment
import BstLean.Part221EigenEvent
import BstLean.Part221Automatic

/-! Actual retained events use the count-dependent gated-plane moment. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part212

theorem count_latitudeMoment160 {n : ℕ} (hn : 8000 ≤ n)
    {R2 : ℝ} (hR0 : 0 < R2) (hR : ActiveRadialMoment160 n R2) :
    LatitudeMoment160 n (eigenJacobianSquared160 n R2 (countPlaneSquared160 n)) :=
  eigenLatitudeMoment160 hn hR0 hR (countPlaneSquared160_pos n)
    (planeEigenMoment160_count (by omega))

theorem count_retained_charge160 {n : ℕ} (hn : 8000 ≤ n)
    {R2 : ℝ} (hR0 : 0 < R2) (hR : ActiveRadialMoment160 n R2)
    (D : Design n) (hτ : TauWorld D) :
    (retDist D.toCentres).real
      (agentEv D (eigenRetainedEvent160 n R2 (countPlaneSquared160 n)))ᶜ ≤ 1 / 10000 :=
  eigen_retained_charge160 hn hR0 hR (countPlaneSquared160_pos n)
    (planeEigenMoment160_count (by omega)) D hτ

noncomputable def bestPlaneSquared160 (n : ℕ) : ℝ :=
  min (planeEnvelope80 (mA n)) (countPlaneSquared160 n)

lemma bestPlaneSquared160_pos (n : ℕ) : 0 < bestPlaneSquared160 n := by
  apply lt_min
  · unfold planeEnvelope80; positivity
  · exact countPlaneSquared160_pos n

lemma bestPlaneSquared160_le_old (n : ℕ) :
    bestPlaneSquared160 n ≤ planeEnvelope80 (mA n) := min_le_left _ _

theorem planeEigenMoment160_best {n : ℕ} (hn : 8000 ≤ n) :
    PlaneEigenMoment160 (mA n) (bestPlaneSquared160 n) := by
  have hm : (16000 : ℝ) ≤ (mA n : ℝ) := by
    exact_mod_cast (show 16000 ≤ mA n by
      unfold mA
      calc 16000 ≤ 8000 ^ 2 := by norm_num
        _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2)
  unfold bestPlaneSquared160
  rcases le_total (planeEnvelope80 (mA n)) (countPlaneSquared160 n) with h | h
  · rw [min_eq_left h]
    exact planeEigenMoment160_old hm
  · rw [min_eq_right h]
    exact planeEigenMoment160_count (by omega)

theorem best_retained_charge160 {n : ℕ} (hn : 8000 ≤ n)
    {R2 : ℝ} (hR0 : 0 < R2) (hR : ActiveRadialMoment160 n R2)
    (D : Design n) (hτ : TauWorld D) :
    (retDist D.toCentres).real
      (agentEv D (eigenRetainedEvent160 n R2 (bestPlaneSquared160 n)))ᶜ ≤ 1 / 10000 :=
  eigen_retained_charge160 hn hR0 hR (bestPlaneSquared160_pos n)
    (planeEigenMoment160_best hn) D hτ

theorem automatic_activeRadialMoment160 {n : ℕ} (hn : 8000 ≤ n) :
    ActiveRadialMoment160 n (automaticRadiusSquared160 n) := by
  have hm : 0 < mA n := by
    unfold mA
    exact pow_pos (by omega : 0 < n) 2
  obtain ⟨ha, ha2, hcal⟩ := automaticRadius_guards hm (by omega : 1 ≤ n - 1 - 1)
  obtain ⟨_, hR⟩ := automaticRadiusSquared160_properties hn
  exact activeRadialMoment160_factorial (by omega) ha ha2 hcal hR.le

/-- Both the radial and plane moment premises have proved analytic suppliers. -/
theorem automatic_best_retained_charge160 {n : ℕ} (hn : 8000 ≤ n)
    (D : Design n) (hτ : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (eigenRetainedEvent160 n
      (automaticRadiusSquared160 n) (bestPlaneSquared160 n)))ᶜ ≤ 1 / 10000 :=
  best_retained_charge160 hn (automaticRadiusSquared160_properties hn).1
    (automatic_activeRadialMoment160 hn) D hτ

end BstLean.Part221
