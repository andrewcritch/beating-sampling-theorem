import BstLean.Part292TraceFrame
import BstLean.Part292TraceNumbers
import BstLean.Part292SourceNumbers
import BstLean.Part172SBnd

/-! Paid transverse trace events, common to all latitude nodes. -/
namespace BstLean.Part292
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part171 BstLean.Part172 BstLean.Part153

noncomputable def traceLow {n : ℕ} (u : Fin n → ℝ) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ) :=
  {A | (2/(n : ℝ))*(999/2000)*(mA n : ℝ)*(n-1 : ℕ) ≤ ∑ i, sg_phi1 u (A i)}

noncomputable def traceHigh {n : ℕ} (u : Fin n → ℝ) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ) :=
  {A | ∑ i, sg_phi2 u (A i) ≤ (2/(n : ℝ))*(1001/1000)*(mA n : ℝ)*(n-1 : ℕ)}

theorem traceLow_measurable {n : ℕ} (u : Fin n → ℝ) : MeasurableSet (traceLow u) := by
  apply measurableSet_le measurable_const
  exact Finset.measurable_sum _ fun i _ => (sg_meas_phi1 u).comp (measurable_pi_apply i)

theorem traceHigh_measurable {n : ℕ} (u : Fin n → ℝ) : MeasurableSet (traceHigh u) := by
  apply measurableSet_le _ measurable_const
  exact Finset.measurable_sum _ fun i _ => (sg_meas_phi2 u).comp (measurable_pi_apply i)

theorem traceLow_paid {n : ℕ} (hn : 8000 ≤ n) {u : Fin n → ℝ} (hu : normSq u = 1) :
    (gaussMat (mA n) n (2/(n : ℝ))).real (traceLow u)ᶜ ≤ 2*exp (-12) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [← traceFrame_distribution (by omega : 1 ≤ n) (2/(n : ℝ)) u,
    map_measureReal_apply (traceFrame_measurable _ _) (traceLow_measurable u).compl]
  apply (measureReal_mono ?_).trans (activeEnergy_band hn)
  intro p hp
  have ht := traceFrame_energy_lower (by omega : 1 ≤ n) hu (by positivity : 0 < 2/(n : ℝ)) p
  simp only [Set.mem_preimage, Set.mem_compl_iff, traceLow, Set.mem_setOf_eq, not_le] at hp
  change activeEnergy p.1 p.2 < _
  apply (mul_lt_mul_iff_right₀ (show 0 < 2/(n : ℝ) by positivity)).mp
  exact ht.trans_lt (by simpa only [mul_assoc] using hp)

theorem traceHigh_paid {n : ℕ} (hn : 8000 ≤ n) {u : Fin n → ℝ} (hu : normSq u = 1) :
    (gaussMat (mA n) n (2/(n : ℝ))).real (traceHigh u)ᶜ ≤ exp (-18) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [← traceFrame_distribution (by omega : 1 ≤ n) (2/(n : ℝ)) u,
    map_measureReal_apply (traceFrame_measurable _ _) (traceHigh_measurable u).compl]
  have h := totalEnergy_band hn
  have hp : ((BstLean.Part29.stdGauss (Fin (mA n))).prod (gaussMat (mA n) (n-1) 1)).real
      {p | (1001/1000 : ℝ)*(mA n : ℝ)*(n-1 : ℕ) < ∑ i, normSq (p.2 i)} ≤ exp (-18) := by
    let S : Set (Matrix (Fin (mA n)) (Fin (n-1)) ℝ) :=
      {G | (1001/1000 : ℝ)*(mA n : ℝ)*(n-1 : ℕ) < ∑ i, normSq (G i)}
    have he : {p : (Fin (mA n) → ℝ) × Matrix (Fin (mA n)) (Fin (n-1)) ℝ |
        (1001/1000 : ℝ)*(mA n : ℝ)*(n-1 : ℕ) < ∑ i, normSq (p.2 i)} =
        Set.univ ×ˢ S := by ext p; simp [S]
    rw [he, measureReal_def, Measure.prod_prod, measure_univ, one_mul]
    simpa only [measureReal_def] using h
  apply (measureReal_mono ?_).trans hp
  intro p hp
  simp only [Set.mem_preimage, Set.mem_compl_iff, traceHigh, Set.mem_setOf_eq, not_le] at hp
  have he : ∑ i, sg_phi2 u (traceFrame (2/(n : ℝ)) u p i) =
      (2/(n : ℝ))*∑ i, normSq (p.2 i) := by
    simp only [traceFrame, sg_phi2_smul, sq_sqrt (by positivity : 0 ≤ 2/(n : ℝ)),
      (traceRow_read (by omega : 1 ≤ n) hu _ _).2, Finset.mul_sum]
  rw [he] at hp
  simp only [Set.mem_setOf_eq]
  apply (mul_lt_mul_iff_right₀ (show 0 < 2/(n : ℝ) by positivity)).mp
  simpa only [mul_assoc] using hp

end BstLean.Part292
