import BstLean.Part264bNormalize
import BstLean.Part199Examples

namespace BstLean.Part264b
open Real BstLean.Part182 BstLean.Part199

noncomputable def nrm (x θ : ℝ) (w : Window) : ℝ :=
  2 * w.t * √(θ * (1-θ) * x) + 2 * θ * √(w.z*x)
noncomputable def nrp (x θ : ℝ) (w : Window) : ℝ := nrm x θ w + 2*θ*w.z*x
noncomputable def nbp (x θ : ℝ) (w : Window) : ℝ := w.t * √(θ*x/(1-θ))
noncomputable def ngp (x z : ℝ) : ℝ := √(1+2*√(z*x)+2*z*x)
noncomputable def nov (x θ : ℝ) (w : Window) (s : ℝ) : ℝ :=
  (1-θ)*(1+s*nbp x θ w)^2+s*(θ*w.pair*√x*ngp x w.z)

theorem norm_radiusMinus (n : ℕ) (θ : ℝ) (w : Window) :
    radiusMinus n θ w = nrm (invN n) θ w := by
  unfold radiusMinus nrm invN
  simp only [div_eq_mul_inv, one_mul]

theorem norm_radiusPlus (n : ℕ) (θ : ℝ) (w : Window) :
    radiusPlus n θ w = nrp (invN n) θ w := by
  unfold radiusPlus nrp
  rw [norm_radiusMinus]
  unfold invN
  simp only [div_eq_mul_inv, one_mul]

theorem norm_planeRatio (n : ℕ) (θ : ℝ) (w : Window) :
    planeRatio n θ w = nbp (invN n) θ w := by
  unfold planeRatio nbp invN
  congr 2
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

theorem norm_gPlus {n : ℕ} (hn : 0 < n) {z : ℝ} (hz : 0 ≤ z) :
    gPlus n z = √(n : ℝ) * ngp (invN n) z := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have ht0 : √(n : ℝ) ≠ 0 := by positivity
  have ht : √(n : ℝ) ^ 2 = n := sq_sqrt (by positivity)
  have he : (n : ℝ) + 2*√((n : ℝ)*z)+2*z =
      (n : ℝ)*(1+2*√(z*invN n)+2*z*invN n) := by
    rw [sqrt_mul (by positivity : (0 : ℝ) ≤ n)]
    unfold invN
    rw [show z*(1/(n : ℝ)) = z / n by ring, sqrt_div hz]
    field_simp
    generalize √(n : ℝ) = a at ht ⊢
    rw [← ht]
    ring
  unfold gPlus ngp
  rw [he, sqrt_mul (by positivity : (0 : ℝ) ≤ n)]

theorem norm_overlap {n : ℕ} (hn : 0 < n) (θ s : ℝ) (w : Window) :
    overlapNumerator n θ w s = nov (invN n) θ w s := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have ht0 : √(n : ℝ) ≠ 0 := by positivity
  have ht : √(n : ℝ) ^ 2 = n := sq_sqrt (by positivity)
  unfold overlapNumerator nov
  rw [norm_planeRatio, norm_gPlus hn w.z_nonneg, root_invN]
  congr 1
  unfold invN
  field_simp
  generalize √(n : ℝ) = a at ht ⊢
  rw [← ht]
  ring

end BstLean.Part264b
