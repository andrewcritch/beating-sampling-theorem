import BstLean.Part211Source

/-! TL with the retained World signal cap and the local noise cell. -/
namespace BstLean.Part211
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130
open BstLean.Part150 (rhoC thetaC gO sO2 bT)
open BstLean.Part154 (csC)
open BstLean.Part206 (energyRatio energyUpper)

theorem upper_energy_on_source {n J : ℕ} (hn : 2 ≤ n) (hJ : 1 ≤ J)
    (c : Fin n → ℝ) {τ δe q : ℝ} (hτ : 0 < τ) (hδe : 0 ≤ δe)
    (hq : q ∈ Icc (-1) 1) (hcap : 1 - thetaC c τ ≤ q)
    (hGroot : 2 * √12 / (n : ℝ) < √(1 - 2 / (n : ℝ) ^ 2))
    (hGupper : gPlus n ≤ 1 + δe) (hDomain : energyRatio n (gMinus n) q ≤ 1)
    {A : Matrix (Fin (mA n)) (Fin n) ℝ} {M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (hSource : (A, M) ∈ EnergySource n J c τ) :
    (2 / (mA n : ℝ)) * normSq (bT J J A M c τ) / (2 / n * rhoC c τ ^ 2) ≤
      energyUpper n (gMinus n) (gPlus n) (finiteEnergy n J δe) q := by
  have hn0 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hg : 0 < gMinus n := sq_pos_of_pos (sub_pos.mpr hGroot)
  have hu : 0 ≤ gPlus n := sq_nonneg _
  have hA : A ∈ BstLean.Part153.Eop n ∧ csC * τ ^ 2 ≤ sO2 A c τ ∧
      A ∉ BstLean.Part153.BadE n c τ ∧ A ∈ FirstUpper n c τ := by
    have h := hSource.1
    simp only [FirstEnergyBad, mem_union, mem_compl_iff, mem_setOf_eq, not_or,
      not_not, not_lt] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2.1⟩
  have hM : M ∉ BstLean.Part153.BadBe n c τ A ∧
      M ∉ BstLean.Part154.BadChi n J A c τ 12 := by
    have h := hSource.2
    simp only [SecondEnergyBad, mem_union, not_or] at h
    exact ⟨h.1.1, h.2⟩
  obtain ⟨hLo, hHi⟩ := energy_on_source hn c τ hA.2.2.1 hGroot.le
  have hEe : gO A c τ ≤ (1 + δe) * (2 / n) * rhoC c τ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hGupper
      (show 0 ≤ 2 / (n : ℝ) * rhoC c τ ^ 2 by positivity)
    nlinarith only [hHi, h]
  exact TL_from_first_source hn0 A c hτ M (bT J J A M c τ) hg hu
    (finiteEnergy_nonneg n J hδe) hq hcap hLo hHi hDomain hA.2.2.2
    (upper_second_on_source A c τ hM.1)
    (finite_energy_on_source hn0 hJ A M c hτ csC_positive hδe hA.1 hA.2.1 hEe hM.2)

/-- The local TL bound retains both the cell's lower endpoint and the World signal cap. -/
theorem TL_local_on_source {n J : ℕ} (hn : 2 ≤ n) (hJ : 1 ≤ J)
    (c : Fin n → ℝ) {τ δe θlo qWorld : ℝ} (hτ : 0 < τ) (hδe : 0 ≤ δe)
    (hθlo : θlo ∈ Icc 0 1) (hθ : θlo ≤ thetaC c τ)
    (hq : qWorld ∈ Icc (-1) 1) (hWorld : 1 - thetaC c τ ≤ qWorld)
    (hGroot : 2 * √12 / (n : ℝ) < √(1 - 2 / (n : ℝ) ^ 2))
    (hGupper : gPlus n ≤ 1 + δe) (hDomain : energyRatio n (gMinus n) qWorld ≤ 1)
    {A : Matrix (Fin (mA n)) (Fin n) ℝ} {M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (hSource : (A, M) ∈ EnergySource n J c τ) :
    (2 / (mA n : ℝ)) * normSq (bT J J A M c τ) / (2 / n * rhoC c τ ^ 2) ≤
        energyUpper n (gMinus n) (gPlus n) (finiteEnergy n J δe) (min (1 - θlo) qWorld) ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n J δe) (min (1 - θlo) qWorld) ≤
        energyUpper n (gMinus n) (gPlus n) (finiteEnergy n J δe) qWorld := by
  have hg : 0 < gMinus n := sq_pos_of_pos (sub_pos.mpr hGroot)
  have hq' : min (1 - θlo) qWorld ∈ Icc (-1) 1 :=
    ⟨le_min (by linarith [hθlo.2]) hq.1, (min_le_right _ _).trans hq.2⟩
  have hd := (BstLean.Part206.energyRatio_mono (by omega : 1 ≤ n) hg hq' hq
    (min_le_right _ _)).trans hDomain
  exact ⟨upper_energy_on_source hn hJ c hτ hδe hq' (le_min (by linarith) hWorld)
      hGroot hGupper hd hSource,
    BstLean.Part206.TL_mono (by omega) hg (sq_nonneg _) (finiteEnergy_nonneg n J hδe)
      hq' hq (min_le_right _ _) hDomain⟩

#print axioms upper_energy_on_source
#print axioms TL_local_on_source
end BstLean.Part211
