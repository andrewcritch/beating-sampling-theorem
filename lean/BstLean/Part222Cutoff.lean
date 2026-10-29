import BstLean.Part222Formula
import BstLean.Part222Allowance

/-! Free allowance B selects a target gap and permits downward rational rounding. -/
namespace BstLean.Part222
open Real

lemma rotationConstant_pos (p : ℕ) : 0 < BstLean.Part195.rotationConstant p := by
  unfold BstLean.Part195.rotationConstant
  split_ifs
  · norm_num
  · apply mul_pos (by positivity)
    apply rpow_pos_of_pos
    unfold BstLean.Part195.oddMoment
    exact Finset.prod_pos fun j hj => by positivity

noncomputable def allowanceGap (n : ℕ) (M R : ℝ) : ℝ :=
  BstLean.Part195.rotationConstant 12 * √M * ((n : ℝ)/R)^((24 : ℝ)⁻¹)

lemma allowanceGap_pos {n : ℕ} (hn : 1 ≤ n) {M R : ℝ} (hM : 0 < M) (hR : 0 < R) :
    0 < allowanceGap n M R := by
  unfold allowanceGap
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos (mul_pos (rotationConstant_pos _) (sqrt_pos.mpr hM))
    (rpow_pos_of_pos (div_pos hnR hR) _)

lemma allowanceGap_power {n : ℕ} (hn : 1 ≤ n) {M R : ℝ} (hM : 0 ≤ M) (hR : 0 < R) :
    allowanceGap n M R^24 = BstLean.Part195.rotationConstant 12^24*M^12*((n : ℝ)/R) := by
  unfold allowanceGap
  have hr : (((n : ℝ)/R)^((24 : ℝ)⁻¹))^24 = (n : ℝ)/R := by
    simpa only [Nat.cast_ofNat] using rpow_inv_natCast_pow (x := (n : ℝ)/R) (n := 24)
      (by positivity : 0 ≤ (n : ℝ)/R) (by norm_num : (24 : ℕ) ≠ 0)
  rw [mul_pow, mul_pow, hr]
  rw [show (24 : ℕ) = 2*12 from rfl, pow_mul √M, sq_sqrt hM]

lemma massGap_at_cutoff {n : ℕ} (hn : 1 ≤ n) {E xi u z : ℝ}
    (hxi : 0 ≤ xi) (hz : 0 ≤ z) :
    massGap n xi E u (cutoffForGap n E xi u z) = z := by
  rw [massGap_identity hn hxi, cutoffForGap_identity hn hxi hz]
  have hs : √(n : ℝ) ≠ 0 := (sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  exact mul_div_cancel₀ _ hs

lemma allowanceGap_target {n : ℕ} (hn : 1 ≤ n) {M R : ℝ} (hM : 0 < M) (hR : 0 < R) :
    (n : ℝ)*(BstLean.Part195.rotationConstant 12*√M/allowanceGap n M R)^24 = R := by
  have hsm : √M^24 = M^12 := by rw [show (24 : ℕ) = 2*12 from rfl, pow_mul, sq_sqrt hM.le]
  simp only [div_pow, mul_pow, hsm]
  rw [allowanceGap_power hn hM.le hR]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : BstLean.Part195.rotationConstant 12 ≠ 0 := (rotationConstant_pos _).ne'
  field_simp [hM.ne', hR.ne', hc, hnR.ne']

/-- The exact inverse cutoff attains the chosen excluded-mass allowance. -/
theorem freeAllowance_exact_mass {n : ℕ} (hn : 1 ≤ n) {M H xi E u β : ℝ}
    (hM : 0 < M) (hxi : 0 ≤ xi)
    (hR : 0 < β-(n : ℝ)*(H/u)^32) :
    massBound n M H xi E u
      (cutoffForGap n E xi u (allowanceGap n M (β-(n : ℝ)*(H/u)^32))) = β := by
  let R := β-(n : ℝ)*(H/u)^32
  let z := allowanceGap n M R
  have hz : 0 < z := allowanceGap_pos hn hM hR
  have hg : 0 < √((1-u)^2-cutoffForGap n E xi u z)-(√E+√(xi/n)) := by
    rw [cutoffForGap_identity hn hxi hz.le]
    exact div_pos hz (sqrt_pos.mpr (by exact_mod_cast hn))
  rw [massBound_formula hn hM.le hxi hg, massGap_at_cutoff hn hxi hz.le,
    allowanceGap_target hn hM hR]
  ring

/-- Every downward rounding of the exact inverse cutoff preserves the mass allowance. -/
theorem freeAllowance_rounded_mass {n : ℕ} (hn : 1 ≤ n) {M H xi E u β d : ℝ}
    (hM : 0 < M) (hxi : 0 ≤ xi)
    (hR : 0 < β-(n : ℝ)*(H/u)^32)
    (hd : d ≤ cutoffForGap n E xi u (allowanceGap n M (β-(n : ℝ)*(H/u)^32))) :
    massBound n M H xi E u d ≤ β := by
  have hz := allowanceGap_pos hn hM hR
  apply rounded_mass_certificate hM.le hd
  · rw [cutoffForGap_identity hn hxi hz.le]
    exact div_pos hz (sqrt_pos.mpr (by exact_mod_cast hn))
  · exact (freeAllowance_exact_mass hn hM hxi hR).le

#print axioms freeAllowance_exact_mass
#print axioms freeAllowance_rounded_mass
end BstLean.Part222
