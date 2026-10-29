import BstLean.Part90Defs
import BstLean.Part73Rot

/-!
# Part 90: slice moments of a linear form perpendicular to `v` (`SliceLin`)

On the slice `x = S v + R w` (`w = perpDir v g`, `v·w = 0`) the linear form
`L = u · (x − (v·x) v)` equals `R (u·w)`. The distribution of `w` is the image of the uniform
distribution on the unit sphere of `ℝ^m` under a linear isometry (`XSliceOp.perp_map`), so
`u·w = c·ω` with `‖c‖ ≤ ‖u‖`, and `E (c·ω)^{2p} ≤ (2p−1)!! ‖c‖^{2p}/m^p`
(`Part73.sphere_dirm_le`).

* `sliceLin_moment`: `E L^{2p} ≤ (2p−1)!! R^{2p} ‖u‖^{2p}/m^p` for every `p ≥ 1`, `m ≥ 1`.
* `sliceLin_of`: `SliceLin m q4 q8 q16` when `3 ≤ q4⁴`, `105 ≤ q8⁸`, `2027025 ≤ q16¹⁶`.
* `sliceLinSharp`, `sliceLinRH`: the two instances.
-/

namespace BstLean.Part90

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part56 (UnitV polarPoint perpDir axialR axialS tailReconstruct basisReconstruct)
open BstLean.Part78 (nsq)
open BstLean.Part86
open BstLean.Part86.XSliceOp

/-- On the slice, the linear form is `R (u·w)` when `v·w = 0`. -/
lemma lin_slice {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : UnitV v) (w : Fin (m + 1) → ℝ)
    (hw : ∑ i, v i * w i = 0) (a r : ℝ) (u : Fin (m + 1) → ℝ) :
    ∑ i, u i * (polarPoint v w a r i - (∑ l, v l * polarPoint v w a r l) * v i) =
      axialR a r * ∑ i, u i * w i := by
  have hvv : ∑ i, v i ^ 2 = 1 := hv
  have e : ∑ l, v l * polarPoint v w a r l = axialS a r := by
    have : ∀ l, v l * polarPoint v w a r l =
        axialS a r * v l ^ 2 + axialR a r * (v l * w l) := by
      intro l
      simp only [polarPoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hvv, hw]
    ring
  rw [e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [polarPoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Even moments of the linear form on a slice**:
`E L^{2p} ≤ (2p−1)!! R^{2p} ‖u‖^{2p}/m^p`. -/
theorem sliceLin_moment (m : ℕ) (hm : 1 ≤ m) (v : Fin (m + 1) → ℝ) (hv : UnitV v) (a r : ℝ)
    (u : Fin (m + 1) → ℝ) (p : ℕ) (hp : 1 ≤ p) :
    ∫ g, (∑ i, u i * (polarPoint v (perpDir v g) a r i -
        (∑ l, v l * polarPoint v (perpDir v g) a r l) * v i)) ^ (2 * p) ∂stdGauss (Fin (m + 1)) ≤
      ((2 * p - 1).doubleFactorial : ℝ) * axialR a r ^ (2 * p) * nsq u ^ p / (m : ℝ) ^ p := by
  classical
  obtain ⟨b, hb⟩ := BstLean.Part56.unit_basis_exists (m + 1) (by omega) v hv
  have hb0 : b 0 = WithLp.toLp 2 v := hb
  set R := axialR a r with hR
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- step 1: the integrand is a function of the direction
  have e1 : ∀ g : Fin (m + 1) → ℝ,
      (∑ i, u i * (polarPoint v (perpDir v g) a r i -
        (∑ l, v l * polarPoint v (perpDir v g) a r l) * v i)) ^ (2 * p) =
      (fun w : Fin (m + 1) → ℝ => (R * ∑ i, u i * w i) ^ (2 * p)) (perpDir v g) := by
    intro g
    rw [lin_slice v hv _ (BstLean.Part56.perpDir_orth56 v g hv) a r u]
  simp_rw [e1]
  have hG : Measurable (fun w : Fin (m + 1) → ℝ => (R * ∑ i, u i * w i) ^ (2 * p)) := by
    have : Continuous (fun w : Fin (m + 1) → ℝ => (R * ∑ i, u i * w i) ^ (2 * p)) := by
      fun_prop
    exact this.measurable
  rw [perp_integral b hm v hb0 _ hG]
  -- step 2: `u · T ω = c · ω`
  set c : Fin m → ℝ := fun j => ∑ i, u i * Omat b i j.succ with hc
  have e2 : ∀ ω : Fin m → ℝ, ∑ i, u i * tailReconstruct b ω i = ∑ j, c j * ω j := by
    intro ω
    have h1 : ∀ i, tailReconstruct b ω i = ∑ j : Fin m, Omat b i j.succ * ω j := by
      intro i
      have := recon_sum b (Fin.cons 0 ω : Fin (m + 1) → ℝ) i
      rw [Fin.sum_univ_succ] at this
      simpa [tailReconstruct] using this
    simp only [h1, hc, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  -- step 3: `‖c‖ ≤ ‖u‖`
  have hcn : ∑ j, c j ^ 2 ≤ nsq u := by
    have h0 : 0 ≤ ∑ j, c j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u (tailReconstruct b c)
    rw [e2 c, BstLean.Part56.tailReconstruct_sumsq] at hcs
    have e3 : ∑ j, c j * c j = ∑ j, c j ^ 2 :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [e3] at hcs
    change (∑ j, c j ^ 2) ^ 2 ≤ nsq u * ∑ j, c j ^ 2 at hcs
    rcases eq_or_lt_of_le h0 with h | h
    · rw [← h]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    · nlinarith
  have h0 : 0 ≤ ∑ j, c j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have e4 : ∀ ω : Fin m → ℝ, (R * ∑ i, u i * tailReconstruct b ω i) ^ (2 * p) =
      R ^ (2 * p) * (∑ j, c j * ω j) ^ (2 * p) := by
    intro ω
    rw [e2 ω, mul_pow]
  simp_rw [e4]
  rw [integral_const_mul]
  have hs := BstLean.Part73.sphere_dirm_le hm c p hp
  have hRp : 0 ≤ R ^ (2 * p) := by
    rw [pow_mul]; exact pow_nonneg (sq_nonneg R) p
  have hdf : (0 : ℝ) ≤ ((2 * p - 1).doubleFactorial : ℝ) := by positivity
  calc R ^ (2 * p) * ∫ ω, (∑ j, c j * ω j) ^ (2 * p) ∂uniformSphere m
      ≤ R ^ (2 * p) * (((2 * p - 1).doubleFactorial : ℝ) * (∑ j, c j ^ 2) ^ p / (m : ℝ) ^ p) :=
        mul_le_mul_of_nonneg_left hs hRp
    _ ≤ R ^ (2 * p) * (((2 * p - 1).doubleFactorial : ℝ) * nsq u ^ p / (m : ℝ) ^ p) := by
        apply mul_le_mul_of_nonneg_left _ hRp
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hcn p) hdf
    _ = ((2 * p - 1).doubleFactorial : ℝ) * R ^ (2 * p) * nsq u ^ p / (m : ℝ) ^ p := by ring

/-- `SliceLin m q4 q8 q16` for all constants above the Gaussian values. -/
theorem sliceLin_of (m : ℕ) (hm : 1 ≤ m) (q4 q8 q16 : ℝ) (h4 : 3 ≤ q4 ^ 4) (h8 : 105 ≤ q8 ^ 8)
    (h16 : 2027025 ≤ q16 ^ 16) : SliceLin m q4 q8 q16 := by
  intro v hv a r u
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hu : 0 ≤ nsq u := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have key : ∀ (p : ℕ) (q : ℝ), 1 ≤ p → ((2 * p - 1).doubleFactorial : ℝ) ≤ q ^ (2 * p) →
      ∫ g, (∑ i, u i * (polarPoint v (perpDir v g) a r i -
        (∑ l, v l * polarPoint v (perpDir v g) a r l) * v i)) ^ (2 * p)
          ∂stdGauss (Fin (m + 1)) ≤
      (q * axialR a r) ^ (2 * p) * nsq u ^ p / (m : ℝ) ^ p := by
    intro p q hp hq
    refine (sliceLin_moment m hm v hv a r u p hp).trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hu p)
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_right hq
    rw [pow_mul]; exact pow_nonneg (sq_nonneg _) p
  have d2 : ((2 * 2 - 1).doubleFactorial : ℝ) = 3 := by norm_num [Nat.doubleFactorial]
  have d4 : ((2 * 4 - 1).doubleFactorial : ℝ) = 105 := by norm_num [Nat.doubleFactorial]
  have d8 : ((2 * 8 - 1).doubleFactorial : ℝ) = 2027025 := by norm_num [Nat.doubleFactorial]
  exact ⟨key 2 q4 (by norm_num) (by rw [d2]; exact h4),
    key 4 q8 (by norm_num) (by rw [d4]; exact h8),
    key 8 q16 (by norm_num) (by rw [d8]; exact h16)⟩

/-- **Slice moments of a linear form, fallback constants** (those of the slice reverse Hölder
inequality: `q4⁴ ≥ 9`, `q8⁸ = 9⁴`, `q16¹⁶ ≥ 9¹²`). -/
theorem sliceLinRH (m : ℕ) (hm : 5000 ≤ m) : SliceLin m (17321 / 10000) 3 (52 / 10) :=
  sliceLin_of m (by omega) _ _ _ (by norm_num) (by norm_num) (by norm_num)

/-- **Slice moments of a linear form, sharp Gaussian constants**
(`q4⁴ ≥ 3`, `q8⁸ ≥ 105`, `q16¹⁶ ≥ 2027025`). -/
theorem sliceLinSharp (m : ℕ) (hm : 5000 ≤ m) :
    SliceLin m (13161 / 10000) (17893 / 10000) (2479 / 1000) :=
  sliceLin_of m (by omega) _ _ _ (by norm_num) (by norm_num) (by norm_num)

end BstLean.Part90

#print axioms BstLean.Part90.sliceLin_moment
#print axioms BstLean.Part90.sliceLin_of
#print axioms BstLean.Part90.sliceLinRH
#print axioms BstLean.Part90.sliceLinSharp
