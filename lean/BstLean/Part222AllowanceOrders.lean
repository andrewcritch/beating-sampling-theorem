import BstLean.Part222Cutoff
import BstLean.Part222MassOrders

/-! Free allowance B applies to every mass order from one through twelve. -/
namespace BstLean.Part222
open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part188 BstLean.Part160

theorem massBoundOrder_formula {n p : ℕ} (hn : 1 ≤ n) {M H xi E u d : ℝ}
    (hM : 0 ≤ M) (hxi : 0 ≤ xi)
    (hg : 0 < √((1-u)^2-d)-(√E+√(xi/n))) :
    massBoundOrder n p M H xi E u d =
      (n : ℝ)*(H/u)^32+(n : ℝ)*
        (BstLean.Part195.rotationConstant p*√M/massGap n xi E u d)^(2*p) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : √(n : ℝ) ≠ 0 := (sqrt_pos.mpr hnR).ne'
  have hsP : √(n : ℝ)^(2*p) = (n : ℝ)^p := by rw [pow_mul, sq_sqrt hnR.le]
  have hmP : √M^(2*p) = M^p := by rw [pow_mul, sq_sqrt hM]
  rw [massGap_identity hn hxi]
  unfold massBoundOrder
  rw [mul_add]
  congr 1
  simp only [div_pow, mul_pow, hmP, hsP]
  field_simp
  <;> ring

theorem massBoundOrder_cutoff_mono {n p : ℕ} {M H xi E u d d0 : ℝ}
    (hM : 0 ≤ M) (hd : d ≤ d0)
    (hgap : 0 < √((1-u)^2-d0)-(√E+√(xi/n))) :
    massBoundOrder n p M H xi E u d ≤ massBoundOrder n p M H xi E u d0 := by
  have hs : √((1-u)^2-d0) ≤ √((1-u)^2-d) := sqrt_le_sqrt (by linarith)
  have hg : 0 < √((1-u)^2-d)-(√E+√(xi/n)) := by linarith
  have hcp := BstLean.Part195.rotationConstant_nonneg p
  unfold massBoundOrder
  gcongr <;> positivity

noncomputable def allowanceGapOrder (n p : ℕ) (M R : ℝ) : ℝ :=
  BstLean.Part195.rotationConstant p*√M*((n : ℝ)/R)^(((2*p : ℕ) : ℝ)⁻¹)

lemma allowanceGapOrder_pos {n p : ℕ} (hn : 1 ≤ n) {M R : ℝ} (hM : 0 < M) (hR : 0 < R) :
    0 < allowanceGapOrder n p M R := by
  unfold allowanceGapOrder
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos (mul_pos (rotationConstant_pos _) (sqrt_pos.mpr hM))
    (rpow_pos_of_pos (div_pos hnR hR) _)

lemma allowanceGapOrder_power {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    {M R : ℝ} (hM : 0 ≤ M) (hR : 0 < R) :
    allowanceGapOrder n p M R^(2*p) =
      BstLean.Part195.rotationConstant p^(2*p)*M^p*((n : ℝ)/R) := by
  unfold allowanceGapOrder
  rw [mul_pow, mul_pow, rpow_inv_natCast_pow (by positivity : 0 ≤ (n : ℝ)/R)
    (by omega : 2*p ≠ 0), pow_mul √M, sq_sqrt hM]

lemma allowanceGapOrder_target {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    {M R : ℝ} (hM : 0 < M) (hR : 0 < R) :
    (n : ℝ)*(BstLean.Part195.rotationConstant p*√M/allowanceGapOrder n p M R)^(2*p) = R := by
  have hsm : √M^(2*p) = M^p := by rw [pow_mul, sq_sqrt hM.le]
  simp only [div_pow, mul_pow, hsm]
  rw [allowanceGapOrder_power hn hp hM.le hR]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : BstLean.Part195.rotationConstant p ≠ 0 := (rotationConstant_pos _).ne'
  field_simp [hM.ne', hR.ne', hc, hnR.ne']

theorem freeAllowance_exact_mass_order {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    {M H xi E u β : ℝ} (hM : 0 < M) (hxi : 0 ≤ xi)
    (hR : 0 < β-(n : ℝ)*(H/u)^32) :
    massBoundOrder n p M H xi E u
      (cutoffForGap n E xi u (allowanceGapOrder n p M (β-(n : ℝ)*(H/u)^32))) = β := by
  let R := β-(n : ℝ)*(H/u)^32
  let z := allowanceGapOrder n p M R
  have hz : 0 < z := allowanceGapOrder_pos hn hM hR
  have hg : 0 < √((1-u)^2-cutoffForGap n E xi u z)-(√E+√(xi/n)) := by
    rw [cutoffForGap_identity hn hxi hz.le]
    exact div_pos hz (sqrt_pos.mpr (by exact_mod_cast hn))
  rw [massBoundOrder_formula hn hM.le hxi hg, massGap_at_cutoff hn hxi hz.le,
    allowanceGapOrder_target hn hp hM hR]
  ring

theorem freeAllowance_rounded_mass_order {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    {M H xi E u β d : ℝ} (hM : 0 < M) (hxi : 0 ≤ xi)
    (hR : 0 < β-(n : ℝ)*(H/u)^32)
    (hd : d ≤ cutoffForGap n E xi u (allowanceGapOrder n p M (β-(n : ℝ)*(H/u)^32))) :
    massBoundOrder n p M H xi E u d ≤ β := by
  have hz := allowanceGapOrder_pos (p := p) hn hM hR
  apply (massBoundOrder_cutoff_mono hM.le hd ?_).trans
    (freeAllowance_exact_mass_order hn hp hM hxi hR).le
  rw [cutoffForGap_identity hn hxi hz.le]
  exact div_pos hz (sqrt_pos.mpr (by exact_mod_cast hn))

theorem freeAllowance_frame_order {n p : ℕ} (hn : 50 ≤ n) (hp : 1 ≤ p) (hp12 : p ≤ 12)
    (D : Design n) (c : Ret n) (hτ : 0 < D.tau0 c)
    (hb : 0 < normSq (D.bA c.1 c.2.1.1)) (hb0 : ∀ j, 0 ≤ D.bA c.1 c.2.1.1 j)
    {M H xiP E u d N xiF β cf : ℝ}
    (hI : WFInterfaces D c M H xiP) (hE : centreEnergy D c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd0 : 0 < d) (hd : d < (1-u)^2)
    (hgap : 0 < √((1-u)^2-d)-(√E+√(xiP/n)))
    (hN : 0 ≤ N) (hcov : COV_at D c N) (hcen : CENTRE_at D c xiF)
    (hmass : massBoundOrder n p M H xiP E u d ≤ β)
    (hframe : (N+xiF)/d+β ≤ cf) (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, BstLean.Part134.eDir (D.bA c.1 c.2.1.1)
      (hStand D c ξ) j*w j)^2 ∂stdGauss (Fin n) ≤ cf/n * ∑ j, w j^2 := by
  have hm := sharp_residual_mass_order hn hp hp12 D c hτ hb hb0 hI hE hu hu1 hd hgap
  exact frameA_at (by omega) D c hd0 hN hcov hcen (hm.trans hmass) hframe w

#print axioms massBoundOrder_formula
#print axioms massBoundOrder_cutoff_mono
#print axioms allowanceGapOrder_power
#print axioms freeAllowance_exact_mass_order
#print axioms freeAllowance_rounded_mass_order
#print axioms freeAllowance_frame_order
end BstLean.Part222
