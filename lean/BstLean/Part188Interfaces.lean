import BstLean.Part160Split
import BstLean.Part151Poinc

namespace BstLean.Part188

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160
open BstLean.Part153 (nrm nrm_sq nrm_nonneg)

variable {n : ℕ}

/-- The energy of the computed centre in the paper's units. -/
noncomputable def centreEnergy (D : Design n) (c : Ret n) : ℝ :=
  normSq (D.bA c.1 c.2.1.1) / n

/-- The hidden-vector energy under the stand-in input distribution. -/
noncomputable def inputEnergy (D : Design n) (c : Ret n) (ξ : Fin n → ℝ) : ℝ :=
  normSq (hStand D c ξ) / n

/-- The scalar coordinate in the direction of the computed centre. -/
noncomputable def centreCoordinate (D : Design n) (c : Ret n) (ξ : Fin n → ℝ) : ℝ :=
  (∑ j, hStand D c ξ j * D.bA c.1 c.2.1.1 j) /
    (√(n : ℝ) * nrm (D.bA c.1 c.2.1.1))

/-- The directional interface includes integrability of the actual input gradient moment. -/
def DirectionMoment (D : Design n) (c : Ret n) (M : ℝ) : Prop :=
  0 ≤ M ∧
  Integrable (fun ξ => BstLean.Part151.gradSq (centreCoordinate D c) ξ ^ 12)
    (stdGauss (Fin n)) ∧
  ∫ ξ, BstLean.Part151.gradSq (centreCoordinate D c) ξ ^ 12 ∂stdGauss (Fin n) ≤
    (M / n) ^ 12

/-- The energy interface is the order-32 moment of sqrt(omega) minus one. -/
def EnergyMoment (D : Design n) (c : Ret n) (H : ℝ) : Prop :=
  0 ≤ H ∧
  Integrable (fun ξ => (√(inputEnergy D c ξ) - 1) ^ 32) (stdGauss (Fin n)) ∧
  ∫ ξ, (√(inputEnergy D c ξ) - 1) ^ 32 ∂stdGauss (Fin n) ≤ H ^ 32

/-- The parallel interface uses the computed centre and the same input distribution. -/
def ParallelCentre (D : Design n) (c : Ret n) (xi : ℝ) : Prop :=
  0 ≤ xi ∧ |(∫ ξ, centreCoordinate D c ξ ∂stdGauss (Fin n)) - √(centreEnergy D c)| ≤
    √(xi / n)

/-- All three bounds are at one fixed retained value; this structure asserts no event charge. -/
structure WFInterfaces (D : Design n) (c : Ret n) (M H xi : ℝ) : Prop where
  direction : DirectionMoment D c M
  energy : EnergyMoment D c H
  parallel : ParallelCentre D c xi

lemma centreCoordinate_mean (hn : 1 ≤ n) (D : Design n) (c : Ret n) :
    ∫ ξ, centreCoordinate D c ξ ∂stdGauss (Fin n) =
      (∑ j, muStand D c j * D.bA c.1 c.2.1.1 j) /
        (√(n : ℝ) * nrm (D.bA c.1 c.2.1.1)) := by
  unfold centreCoordinate
  rw [integral_div, hStand_mean hn]

/-- A full centre bound supplies a valid, possibly weaker, parallel centre bound. -/
theorem parallelCentre_of_full (hn : 1 ≤ n) (D : Design n) (c : Ret n) {xi : ℝ}
    (hxi : 0 ≤ xi) (hb : 0 < normSq (D.bA c.1 c.2.1.1))
    (hc : CENTRE_at D c xi) : ParallelCentre D c xi := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set b := D.bA c.1 c.2.1.1
  have hbN : 0 < nrm b := Real.sqrt_pos.mpr hb
  have hsN : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hnR
  have hn2 : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have he : √(centreEnergy D c) = nrm b / √(n : ℝ) := by
    unfold centreEnergy
    rw [Real.sqrt_div (normSq_nonneg b)]
    rfl
  have hd : normSq (muStand D c - b) ≤ xi := by
    unfold CENTRE_at at hc
    rw [hn2] at hc
    have e : xi * (2 / (n : ℝ)) / n = 2 / (n : ℝ) ^ 2 * xi := by field_simp
    rw [e] at hc
    exact le_of_mul_le_mul_left hc (by positivity)
  refine ⟨hxi, ?_⟩
  rw [centreCoordinate_mean hn, he]
  have hdot : (∑ j, muStand D c j * b j) - normSq b =
      ∑ j, (muStand D c - b) j * b j := by
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have e : (∑ j, muStand D c j * b j) / (√(n : ℝ) * nrm b) - nrm b / √(n : ℝ) =
      (∑ j, (muStand D c - b) j * b j) / (√(n : ℝ) * nrm b) := by
    rw [← hdot, ← nrm_sq b]
    field_simp
    <;> ring
  change |(∑ j, muStand D c j * b j) / (√(n : ℝ) * nrm b) - nrm b / √(n : ℝ)| ≤ _
  rw [e, abs_div, abs_of_pos (mul_pos hsN hbN), div_le_iff₀ (mul_pos hsN hbN)]
  have hCS := sum_mul_sq_le (muStand D c - b) b
  have hbound : (∑ j, (muStand D c - b) j * b j) ^ 2 ≤ xi * normSq b :=
    hCS.trans (mul_le_mul_of_nonneg_right hd (normSq_nonneg b))
  have hs : (√(xi / (n : ℝ)) * (√(n : ℝ) * nrm b)) ^ 2 = xi * normSq b := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hnR.le, nrm_sq]
    field_simp
  have hAbs : |∑ j, (muStand D c - b) j * b j| ^ 2 ≤
      (√(xi / (n : ℝ)) * (√(n : ℝ) * nrm b)) ^ 2 := by
    rw [sq_abs, hs]
    exact hbound
  nlinarith [abs_nonneg (∑ j, (muStand D c - b) j * b j),
    show 0 ≤ √(xi / (n : ℝ)) * (√(n : ℝ) * nrm b) by positivity]

end BstLean.Part188
