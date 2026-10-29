import BstLean.Part290Bounds
import BstLean.Part253EnergyUpper

namespace BstLean.Part290
open Real Set BstLean.Part130 BstLean.Part140 BstLean.Part159 BstLean.Part218
open BstLean.Part228

theorem kernel_window {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (kap1 (2*n)) (4937293/10^7) (493739/10^6) := by
  have hr := ratio_window ha
  have hlo : (4937293/10^7 : ℝ) ≤ kappa (31830988618379067153/10^20) := by
    apply BstLean.Part253.kappa_lower_rational (s := 94798671739/10^11)
    <;> norm_num
  have hmon := kappa_monotoneOn
    (by norm_num : (31830988618379067153/10^20 : ℝ) ∈ Icc (-1) 1)
    (show firstRatio (2*n) ∈ Icc (-1 : ℝ) 1 from
      ⟨by linarith [hr.1], by linarith [hr.2]⟩) hr.1
  have hhi : kappa (firstRatio (2*n)) ≤ (493739/10^6 : ℝ) := by
    apply BstLean.Part253.kappa_upper_rational (Q := 318319834/10^9)
      (s := 9479833776/10^10) (by linarith [hr.1]) hr.2
    <;> norm_num
  have he : kap1 (2*n) = kappa (firstRatio (2*n)) := by
    unfold kap1
    rw [q1_eq_cN (by omega : 1 ≤ 2*n)]
    rfl
  rw [he]
  exact ⟨hlo.trans hmon, hhi⟩

end BstLean.Part290
