import BstLean.Part130Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Convex.Deriv

/-!
# Part 130, item 3: the kernel function `κ`

`κ(t) = (√(1 − t²) + t(π − arccos t))/π` (paper: `delegations/answers/onW4c-cx.md` §2).
* `kappa_zero`, `kappa_one`, `kappa_neg_one`: `κ(0) = 1/π`, `κ(1) = 1`, `κ(−1) = 0`.
* `hasDerivAt_kappa`: `κ′(t) = (π − arccos t)/π` on `(−1, 1)`; `kappa_deriv_bounds`: `0 ≤ κ′ ≤ 1`.
* `kappa_monotoneOn`, `kappa_convexOn`: `κ` is increasing and convex on `[−1, 1]`.
* `kappa_lipschitz`: `0 ≤ κ(s) − κ(t) ≤ s − t` for `−1 ≤ t ≤ s ≤ 1`.
* `kappa_mem`: `0 ≤ κ ≤ 1` on `[−1, 1]`.
* `kappa_cos`: `κ(cos ψ) = (sin ψ + (π − ψ) cos ψ)/π` for `0 ≤ ψ ≤ π`.
-/

namespace BstLean.Part130

open Real Set

/-- The kernel function `κ(t) = (√(1 − t²) + t(π − arccos t))/π`. -/
noncomputable def kappa (t : ℝ) : ℝ := (Real.sqrt (1 - t ^ 2) + t * (π - Real.arccos t)) / π

theorem kappa_zero : kappa 0 = 1 / π := by simp [kappa]

theorem kappa_one : kappa 1 = 1 := by
  simp [kappa, Real.pi_ne_zero]

theorem kappa_neg_one : kappa (-1) = 0 := by simp [kappa]

lemma continuous_kappa : Continuous kappa := by
  unfold kappa
  have := Real.continuous_arccos
  fun_prop

/-- `κ′(t) = (π − arccos t)/π` on `(−1, 1)`. -/
theorem hasDerivAt_kappa {t : ℝ} (h1 : -1 < t) (h2 : t < 1) :
    HasDerivAt kappa ((π - Real.arccos t) / π) t := by
  have hpos : 0 < 1 - t ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr hpos
  have d1 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_sub 1
    simpa using this
  have d2 := d1.sqrt hpos.ne'
  have d3 := (Real.hasDerivAt_arccos h1.ne' h2.ne).const_sub π
  have d4 := (hasDerivAt_id t).mul d3
  have d5 := (d2.add d4).div_const π
  have d6 : HasDerivAt kappa _ t := d5
  convert d6 using 1
  simp only [id]
  field_simp
  ring

/-- `0 ≤ κ′ ≤ 1`. -/
theorem kappa_deriv_bounds (t : ℝ) :
    0 ≤ (π - Real.arccos t) / π ∧ (π - Real.arccos t) / π ≤ 1 := by
  have h1 := Real.arccos_le_pi t
  have h2 := Real.arccos_nonneg t
  have hp := Real.pi_pos
  constructor
  · exact div_nonneg (by linarith) hp.le
  · rw [div_le_one hp]; linarith

lemma interior_Icc_pm : interior (Icc (-1 : ℝ) 1) = Ioo (-1) 1 := interior_Icc

lemma deriv_kappa {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    deriv kappa t = (π - Real.arccos t) / π := (hasDerivAt_kappa ht.1 ht.2).deriv

/-- `κ` is increasing on `[−1, 1]`. -/
theorem kappa_monotoneOn : MonotoneOn kappa (Icc (-1) 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) continuous_kappa.continuousOn ?_ ?_
  · rw [interior_Icc_pm]
    exact fun t ht => (hasDerivAt_kappa ht.1 ht.2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc_pm]
    intro t ht
    rw [deriv_kappa ht]
    exact (kappa_deriv_bounds t).1

/-- `κ` is convex on `[−1, 1]`. -/
theorem kappa_convexOn : ConvexOn ℝ (Icc (-1) 1) kappa := by
  refine MonotoneOn.convexOn_of_deriv (convex_Icc _ _) continuous_kappa.continuousOn ?_ ?_
  · rw [interior_Icc_pm]
    exact fun t ht => (hasDerivAt_kappa ht.1 ht.2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc_pm]
    intro s hs t ht hst
    rw [deriv_kappa hs, deriv_kappa ht]
    have := Real.arccos_le_arccos hst
    exact div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le

/-- `κ` is 1-Lipschitz and increasing on `[−1, 1]`: `0 ≤ κ(s) − κ(t) ≤ s − t` for `t ≤ s`. -/
theorem kappa_lipschitz {s t : ℝ} (ht : -1 ≤ t) (hts : t ≤ s) (hs : s ≤ 1) :
    0 ≤ kappa s - kappa t ∧ kappa s - kappa t ≤ s - t := by
  have hmono := kappa_monotoneOn ⟨ht, hts.trans hs⟩ ⟨ht.trans hts, hs⟩ hts
  have hmono2 : MonotoneOn (fun x => x - kappa x) (Icc (-1) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (continuous_id.sub continuous_kappa).continuousOn ?_ ?_
    · rw [interior_Icc_pm]
      exact fun x hx => ((hasDerivAt_id x).sub
        (hasDerivAt_kappa hx.1 hx.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc_pm]
      intro x hx
      have hd : HasDerivAt (fun x => x - kappa x) (1 - (π - Real.arccos x) / π) x :=
        (hasDerivAt_id x).sub (hasDerivAt_kappa hx.1 hx.2)
      rw [hd.deriv]
      have := (kappa_deriv_bounds x).2
      linarith
  have h2 := hmono2 ⟨ht, hts.trans hs⟩ ⟨ht.trans hts, hs⟩ hts
  simp only at h2
  constructor <;> linarith

/-- `0 ≤ κ ≤ 1` on `[−1, 1]`. -/
theorem kappa_mem {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1) : 0 ≤ kappa t ∧ kappa t ≤ 1 := by
  have a := kappa_monotoneOn ⟨le_refl _, by norm_num⟩ ⟨h1, h2⟩ h1
  have b := kappa_monotoneOn ⟨h1, h2⟩ ⟨by norm_num, le_refl _⟩ h2
  rw [kappa_neg_one] at a
  rw [kappa_one] at b
  exact ⟨a, b⟩

/-- `κ(cos ψ) = (sin ψ + (π − ψ) cos ψ)/π` for `0 ≤ ψ ≤ π`. -/
theorem kappa_cos {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ π) :
    kappa (Real.cos ψ) = (Real.sin ψ + (π - ψ) * Real.cos ψ) / π := by
  unfold kappa
  rw [Real.arccos_cos h0 h1]
  have hs : Real.sqrt (1 - Real.cos ψ ^ 2) = Real.sin ψ := by
    rw [← Real.sin_sq ψ, Real.sqrt_sq (Real.sin_nonneg_of_nonneg_of_le_pi h0 h1)]
  rw [hs]
  ring

end BstLean.Part130

open BstLean.Part130 in
#print axioms kappa_convexOn
open BstLean.Part130 in
#print axioms kappa_monotoneOn
open BstLean.Part130 in
#print axioms kappa_lipschitz
open BstLean.Part130 in
#print axioms hasDerivAt_kappa
