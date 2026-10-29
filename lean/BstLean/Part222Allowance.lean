import BstLean.Part222Mass

/-! The excluded-mass allowance and the mixture cutoff stay separate. -/
namespace BstLean.Part222
open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part188

/-- The free allowance uses the full error in the covariance numerator and the parallel
error in the mass denominator. It adds no event payment. -/
theorem freeAllowance_frame {n : ℕ} (hn : 50 ≤ n) (D : Design n) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hb : 0 < normSq (D.bA c.1 c.2.1.1))
    (hb0 : ∀ j, 0 ≤ D.bA c.1 c.2.1.1 j) {M H xiP E u d N xiF β cf : ℝ}
    (hI : WFInterfaces D c M H xiP) (hE : centreEnergy D c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd0 : 0 < d) (hd : d < (1-u)^2)
    (hgap : 0 < √((1-u)^2-d) - (√E + √(xiP/n)))
    (hN : 0 ≤ N) (hcov : COV_at D c N) (hcen : CENTRE_at D c xiF)
    (hmass : massBound n M H xiP E u d ≤ β)
    (hframe : (N+xiF)/d+β ≤ cf) (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, BstLean.Part134.eDir (D.bA c.1 c.2.1.1)
      (hStand D c ξ) j*w j)^2 ∂stdGauss (Fin n) ≤ cf/n * ∑ j, w j^2 := by
  have hm := sharp_residual_mass hn D c hτ hb hb0 hI hE hu hu1 hd hgap
  have hm' : MASS_at D c d β := hm.trans hmass
  exact frameA_at (by omega) D c hd0 hN hcov hcen hm' hframe w

/-- A scalar mass certificate at an unrounded cutoff also covers its downward rounding. -/
theorem rounded_mass_certificate {n : ℕ} {M H xi E u d d0 β : ℝ}
    (hM : 0 ≤ M) (hd : d ≤ d0)
    (hgap : 0 < √((1-u)^2-d0) - (√E + √(xi/n)))
    (hcert : massBound n M H xi E u d0 ≤ β) :
    massBound n M H xi E u d ≤ β :=
  (massBound_cutoff_mono hM hd hgap).trans hcert

noncomputable def cutoffForGap (n : ℕ) (E xi u z : ℝ) : ℝ :=
  (1-u)^2 - (√E + (√xi+z)/√(n : ℝ))^2

/-- The positive target gap defines an exact cutoff before rational rounding. -/
theorem cutoffForGap_identity {n : ℕ} (hn : 1 ≤ n) {E xi u z : ℝ}
    (hxi : 0 ≤ xi) (hz : 0 ≤ z) :
    √((1-u)^2-cutoffForGap n E xi u z) - (√E+√(xi/n)) = z/√(n : ℝ) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (1-u)^2-cutoffForGap n E xi u z =
      (√E+(√xi+z)/√(n : ℝ))^2 := by unfold cutoffForGap; ring
  rw [he, sqrt_sq (by positivity)]
  rw [sqrt_div hxi]
  ring

#print axioms freeAllowance_frame
#print axioms rounded_mass_certificate
#print axioms cutoffForGap_identity
end BstLean.Part222
