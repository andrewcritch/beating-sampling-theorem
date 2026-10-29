import BstLean.Part195Network

/-! The sharp order-24 rotation constant supplies the residual cutoff mass. -/
namespace BstLean.Part222
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part188

noncomputable def massBound (n : ℕ) (M H xi E u d : ℝ) : ℝ :=
  (n : ℝ) * ((H / u) ^ 32 +
    (BstLean.Part195.rotationConstant 12 ^ 24 * (M / n) ^ 12) /
      (√((1-u)^2-d) - (√E + √(xi / n))) ^ 24)

/-- The input mass has no additional network-event payment. -/
theorem sharp_good_mass {n : ℕ} (hn : 50 ≤ n) (D : Design n) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hb : 0 < normSq (D.bA c.1 c.2.1.1))
    (hb0 : ∀ j, 0 ≤ D.bA c.1 c.2.1.1 j) {M H xi E u d : ℝ}
    (hI : WFInterfaces D c M H xi) (hE : centreEnergy D c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : d < (1-u)^2)
    (hgap : 0 < √((1-u)^2-d) - (√E + √(xi / n))) :
    (n : ℝ) * (stdGauss (Fin n)).real
      {ξ | ¬ goodInput ((1-u)^2) d (inputEnergy D c ξ) (centreCoordinate D c ξ)} ≤
      massBound n M H xi E u d := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have he : (fun ξ => |√(inputEnergy D c ξ)-1|^32) =
      (fun ξ => (√(inputEnergy D c ξ)-1)^32) := by
    funext ξ
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hiE : Integrable (fun ξ => |√(inputEnergy D c ξ)-1|^32)
      (stdGauss (Fin n)) := by rw [he]; exact hI.energy.2.1
  have hmE : (∫ ξ, |√(inputEnergy D c ξ)-1|^32 ∂stdGauss (Fin n)) ≤ H^32 := by
    rw [he]; exact hI.energy.2.2
  have hm : (∫ ξ, centreCoordinate D c ξ ∂stdGauss (Fin n)) ≤ √E + √(xi/n) := by
    have hp := (abs_le.mp hI.parallel.2).2
    have hs := Real.sqrt_le_sqrt hE
    linarith
  have hiF := (centreCoordinate_moment24 hn D c hτ hb hI.direction).1
  have hmF := BstLean.Part195.direction_moment24 (by omega) D c hτ hb hI.direction
  exact mul_le_mul_of_nonneg_left
    (good_complement_mass (stdGauss (Fin n)) (inputEnergy D c) (centreCoordinate D c)
      (inputEnergy_nonneg D c) (centreCoordinate_nonneg D c hb0)
      hu hu1 hd hgap hm hiE hmE hiF hmF) (Nat.cast_nonneg _)

/-- The sharp mass supplies the existing residual-mass interface. -/
theorem sharp_residual_mass {n : ℕ} (hn : 50 ≤ n) (D : Design n) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hb : 0 < normSq (D.bA c.1 c.2.1.1))
    (hb0 : ∀ j, 0 ≤ D.bA c.1 c.2.1.1 j) {M H xi E u d : ℝ}
    (hI : WFInterfaces D c M H xi) (hE : centreEnergy D c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : d < (1-u)^2)
    (hgap : 0 < √((1-u)^2-d) - (√E + √(xi / n))) :
    MASS_at D c d (massBound n M H xi E u d) :=
  MASS_at_of_good_complement (by omega) D c (ne_of_gt hb)
    (sharp_good_mass hn D c hτ hb hb0 hI hE hu hu1 hd hgap)

/-- A downward cutoff rounding decreases the same mass bound. -/
theorem massBound_cutoff_mono {n : ℕ} {M H xi E u d d0 : ℝ}
    (hM : 0 ≤ M) (hd : d ≤ d0)
    (hgap : 0 < √((1-u)^2-d0) - (√E + √(xi/n))) :
    massBound n M H xi E u d ≤ massBound n M H xi E u d0 := by
  have hs : √((1-u)^2-d0) ≤ √((1-u)^2-d) := Real.sqrt_le_sqrt (by linarith)
  have hg : 0 < √((1-u)^2-d) - (√E + √(xi/n)) := by linarith
  unfold massBound
  gcongr

#print axioms sharp_good_mass
#print axioms sharp_residual_mass
#print axioms massBound_cutoff_mono
end BstLean.Part222
