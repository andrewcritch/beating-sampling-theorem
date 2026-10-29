import BstLean.Part170Fin

/-!
# Part 170 (file `Sq`): concentration of a square of a Lipschitz function of a Gaussian vector

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, proof of `t7:p08:energy` ("`√Q_en` is `√Γ_max`-Lipschitz.
Concentration gives ..."). Lean's form: for `S ≥ 0` Euclidean `L`-Lipschitz on a standard
Gaussian space, `‖S² − E S²‖₈ ≤ c₁₆²L² + 2(√(E S²) + 1)c₈L + c₂²L²`, `c_p = (π/2)(E|g|^p)^{1/p}`
(`c₂ = π/2`, `c₈ ≤ 1.8π/2`, `c₁₆ ≤ 2.5π/2`). The proof writes
`S² − E S² = (S − ES)² + 2ES(S − ES) − Var S` and uses Pisier's Poincaré inequality at orders 2,
8 and 16.

* `pow8_split3`: three-term Minkowski in `L⁸` by convexity.
* `gmom16_le`: `E|g|¹⁶ ≤ 2.5¹⁶`; `gmom2_eq`: `E g² = 1`.
* **`sq_conc`**.
-/

namespace BstLean.Part170

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part162 (gmom gmom_nonneg poincare_p_lint poincare_p)
open BstLean.Part148 (EuLip)
open BstLean.Part151 (gradSq gradSq_le gradSq_nonneg)

lemma pow8_split3 {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) {A B C : ℝ} (hA : 0 < A)
    (hB : 0 < B) (hC : 0 < C) :
    (x + y + z) ^ 8 ≤ (A + B + C) ^ 7 / A ^ 7 * x ^ 8 + (A + B + C) ^ 7 / B ^ 7 * y ^ 8 +
      (A + B + C) ^ 7 / C ^ 7 * z ^ 8 := by
  have h1 := pow8_split x (y + z) hA (add_pos hB hC)
  have h2 := pow8_split y z hB hC
  rw [abs_of_nonneg hx, abs_of_nonneg (add_nonneg hy hz)] at h1
  rw [abs_of_nonneg hy, abs_of_nonneg hz] at h2
  have hBC : 0 < B + C := add_pos hB hC
  have e : (A + (B + C)) = A + B + C := by ring
  rw [e] at h1
  have h3 : (A + B + C) ^ 7 / (B + C) ^ 7 * (y + z) ^ 8 ≤ (A + B + C) ^ 7 / (B + C) ^ 7 *
      ((B + C) ^ 7 / B ^ 7 * y ^ 8 + (B + C) ^ 7 / C ^ 7 * z ^ 8) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e2 : (A + B + C) ^ 7 / (B + C) ^ 7 * ((B + C) ^ 7 / B ^ 7 * y ^ 8 +
      (B + C) ^ 7 / C ^ 7 * z ^ 8) = (A + B + C) ^ 7 / B ^ 7 * y ^ 8 +
      (A + B + C) ^ 7 / C ^ 7 * z ^ 8 := by
    field_simp
  rw [add_assoc x y z]
  linarith

lemma gmom16_le : gmom 16 ≤ (25 / 10) ^ 16 := by
  have h := BstLean.Part162.gmom_even 8
  rw [show (2 * 8 : ℕ) = 16 from rfl] at h
  rw [h]
  simp [Finset.prod_range_succ]
  norm_num

lemma gmom2_eq : gmom 2 = 1 := by
  have h := BstLean.Part162.gmom_even 1
  rw [show (2 * 1 : ℕ) = 2 from rfl] at h
  rw [h]; simp

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma integrable_normSq_std : Integrable (fun ξ : ι → ℝ => normSq ξ) (stdGauss ι) := by
  unfold normSq
  exact integrable_finsetSum _ fun i _ => (BstLean.Part112.memLp_coord i).integrable_sq

lemma euLip_sq_integrable {S : (ι → ℝ) → ℝ} {L : ℝ} (hL0 : 0 ≤ L) (hL : EuLip S L) :
    Integrable (fun ξ => S ξ ^ 2) (stdGauss ι) := by
  have hc := hL.continuous hL0
  refine Integrable.mono' ((integrable_const (2 * S 0 ^ 2)).add
    (integrable_normSq_std.const_mul (2 * L ^ 2))) (hc.measurable.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  show S ξ ^ 2 ≤ 2 * S 0 ^ 2 + 2 * L ^ 2 * normSq ξ
  have h := hL ξ 0
  simp only [Pi.zero_apply, sub_zero] at h
  have hn : √(∑ i, ξ i ^ 2) ^ 2 = normSq ξ := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have h2 : |S ξ| ≤ |S 0| + L * √(∑ i, ξ i ^ 2) := by
    have := abs_sub_abs_le_abs_sub (S ξ) (S 0); linarith
  have h3 : S ξ ^ 2 ≤ (|S 0| + L * √(∑ i, ξ i ^ 2)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have h4 : (|S 0| + L * √(∑ i, ξ i ^ 2)) ^ 2 ≤ 2 * S 0 ^ 2 + 2 * L ^ 2 * normSq ξ := by
    nlinarith [sq_nonneg (|S 0| - L * √(∑ i, ξ i ^ 2)), sq_abs (S 0)]
  linarith

lemma euLip_integrable {S : (ι → ℝ) → ℝ} {L : ℝ} (hL0 : 0 ≤ L) (hL : EuLip S L) :
    Integrable S (stdGauss ι) := by
  have hc := hL.continuous hL0
  have h2 := euLip_sq_integrable hL0 hL
  refine Integrable.mono' ((h2.add (integrable_const 1))) hc.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs]
  show |S ξ| ≤ S ξ ^ 2 + 1
  nlinarith [sq_nonneg (|S ξ| - 1), sq_abs (S ξ), abs_nonneg (S ξ)]

/-- **Concentration of a square** (eighth moment). -/
theorem sq_conc {S : (ι → ℝ) → ℝ} {L : ℝ} (hL : 0 < L) (hS : EuLip S L) (hS0 : ∀ ξ, 0 ≤ S ξ) :
    ∫⁻ ξ, ENNReal.ofReal (|S ξ ^ 2 - ∫ ξ', S ξ' ^ 2 ∂stdGauss ι| ^ 8) ∂stdGauss ι ≤
      ENNReal.ofReal (((π / 2 * (25 / 10) * L) ^ 2 +
        2 * (√(∫ ξ', S ξ' ^ 2 ∂stdGauss ι) + 1) * (π / 2 * (18 / 10) * L) +
        (π / 2 * L) ^ 2) ^ 8) := by
  have hc := hS.continuous hL.le
  have iS := euLip_integrable hL.le hS
  have iS2 := euLip_sq_integrable hL.le hS
  set sb := ∫ ξ, S ξ ∂stdGauss ι with hsb
  set qb := ∫ ξ, S ξ ^ 2 ∂stdGauss ι with hqb
  have hq0 : 0 ≤ qb := integral_nonneg fun ξ => sq_nonneg _
  have hs0 : 0 ≤ sb := integral_nonneg hS0
  -- `sb² ≤ qb`
  have hJ : sb ^ 2 ≤ qb := BstLean.Part133.sq_integral_le (ρ := stdGauss ι) iS2
  have hsq : sb ≤ √qb := Real.le_sqrt_of_sq_le hJ
  -- variance
  set V := ∫ ξ, (S ξ - sb) ^ 2 ∂stdGauss ι with hVd
  have iD2 : Integrable (fun ξ => (S ξ - sb) ^ 2) (stdGauss ι) := by
    have : (fun ξ => (S ξ - sb) ^ 2) = fun ξ => S ξ ^ 2 - 2 * sb * S ξ + sb ^ 2 := by
      funext ξ; ring
    rw [this]; exact (iS2.sub (iS.const_mul _)).add (integrable_const _)
  have hV : V = qb - sb ^ 2 := by
    have : (fun ξ => (S ξ - sb) ^ 2) = fun ξ => S ξ ^ 2 - 2 * sb * S ξ + sb ^ 2 := by
      funext ξ; ring
    have i3 : Integrable (fun ξ => S ξ ^ 2 - 2 * sb * S ξ) (stdGauss ι) :=
      iS2.sub (iS.const_mul _)
    rw [hVd, this, integral_add (f := fun ξ => S ξ ^ 2 - 2 * sb * S ξ) (g := fun _ => sb ^ 2) i3
      (integrable_const _), integral_sub (f := fun ξ => S ξ ^ 2) (g := fun ξ => 2 * sb * S ξ) iS2
      (iS.const_mul _), integral_const_mul, integral_const]
    simp; ring
  have hV0 : 0 ≤ V := integral_nonneg fun ξ => sq_nonneg _
  -- Poincaré at order 2: `V ≤ (π/2)²L²`
  have hP2 := poincare_p hL.le hS (p := 2) (by norm_num)
  have hg2 : ∫ x, √(gradSq S x) ^ 2 ∂stdGauss ι ≤ L ^ 2 := by
    have hpt : ∀ x, √(gradSq S x) ^ 2 ≤ L ^ 2 := fun x =>
      pow_le_pow_left₀ (Real.sqrt_nonneg _) ((Real.sqrt_le_left hL.le).mpr (gradSq_le hL.le hS x)) 2
    calc _ ≤ ∫ _x, L ^ 2 ∂stdGauss ι := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => by positivity) (integrable_const _)
          (Filter.Eventually.of_forall hpt)
      _ = L ^ 2 := by simp
  have hVb : V ≤ (π / 2 * L) ^ 2 := by
    have e : V = ∫ x, |S x - sb| ^ 2 ∂stdGauss ι := by
      rw [hVd]; exact integral_congr_ae (Filter.Eventually.of_forall fun x => (sq_abs _).symm)
    rw [e]
    refine hP2.trans ?_
    rw [gmom2_eq, one_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left hg2 (by positivity)
  -- the three terms
  set A := (π / 2 * (25 / 10) * L) ^ 2
  set B := 2 * (√qb + 1) * (π / 2 * (18 / 10) * L)
  set C := (π / 2 * L) ^ 2
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  have hC : 0 < C := by positivity
  have hpt : ∀ ξ, |S ξ ^ 2 - qb| ^ 8 ≤ (A + B + C) ^ 7 / A ^ 7 * (|S ξ - sb| ^ 2) ^ 8 +
      (A + B + C) ^ 7 / B ^ 7 * (2 * (√qb + 1) * |S ξ - sb|) ^ 8 +
      (A + B + C) ^ 7 / C ^ 7 * V ^ 8 := by
    intro ξ
    have e : S ξ ^ 2 - qb = (S ξ - sb) ^ 2 + 2 * sb * (S ξ - sb) - V := by rw [hV]; ring
    have h1 : |S ξ ^ 2 - qb| ≤ |S ξ - sb| ^ 2 + 2 * (√qb + 1) * |S ξ - sb| + V := by
      rw [e]
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg hV0]
      refine add_le_add ((abs_add_le _ _).trans (add_le_add (by rw [abs_pow]) ?_)) le_rfl
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg hs0]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      linarith
    have h2 := pow8_split3 (sq_nonneg |S ξ - sb|) (by positivity : 0 ≤ 2 * (√qb + 1) * |S ξ - sb|)
      hV0 hA hB hC
    calc |S ξ ^ 2 - qb| ^ 8 ≤ (|S ξ - sb| ^ 2 + 2 * (√qb + 1) * |S ξ - sb| + V) ^ 8 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 8
      _ ≤ _ := h2
  -- integrate
  have hP16 := poincare_p_lint hL.le hS (p := 16) (by norm_num)
  have hP8 := poincare_p_lint hL.le hS (p := 8) (by norm_num)
  have hgp : ∀ p : ℕ, ∫ x, √(gradSq S x) ^ p ∂stdGauss ι ≤ L ^ p := fun p => by
    have hpt : ∀ x, √(gradSq S x) ^ p ≤ L ^ p := fun x =>
      pow_le_pow_left₀ (Real.sqrt_nonneg _) ((Real.sqrt_le_left hL.le).mpr (gradSq_le hL.le hS x)) p
    calc _ ≤ ∫ _x, L ^ p ∂stdGauss ι := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => by positivity) (integrable_const _)
          (Filter.Eventually.of_forall hpt)
      _ = L ^ p := by simp
  have h16 : ∫⁻ ξ, ENNReal.ofReal ((|S ξ - sb| ^ 2) ^ 8) ∂stdGauss ι ≤ ENNReal.ofReal (A ^ 8) := by
    have e : ∀ ξ, (|S ξ - sb| ^ 2) ^ 8 = |S ξ - sb| ^ 16 := fun ξ => by ring
    simp_rw [e]
    refine hP16.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 := gmom16_le
    have h2 := hgp 16
    have : A ^ 8 = (π / 2) ^ 16 * ((25 / 10) ^ 16 * L ^ 16) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2
      (integral_nonneg fun x => pow_nonneg (Real.sqrt_nonneg _) _) (by norm_num))
      (by positivity)
  have h8 : ∫⁻ ξ, ENNReal.ofReal ((2 * (√qb + 1) * |S ξ - sb|) ^ 8) ∂stdGauss ι ≤ ENNReal.ofReal (B ^ 8) := by
    have e : ∀ ξ, ENNReal.ofReal ((2 * (√qb + 1) * |S ξ - sb|) ^ 8) =
        ENNReal.ofReal ((2 * (√qb + 1)) ^ 8) * ENNReal.ofReal (|S ξ - sb| ^ 8) := fun ξ => by
      rw [← ENNReal.ofReal_mul (by positivity), mul_pow]
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal ((2 * (√qb + 1)) ^ 8) * ∫⁻ ξ, ENNReal.ofReal (|S ξ - sb| ^ 8) ∂stdGauss ι
        ≤ ENNReal.ofReal ((2 * (√qb + 1)) ^ 8) *
          ENNReal.ofReal ((π / 2) ^ 8 * (gmom 8 * ∫ x, √(gradSq S x) ^ 8 ∂stdGauss ι)) := by gcongr
      _ ≤ ENNReal.ofReal ((2 * (√qb + 1)) ^ 8) * ENNReal.ofReal ((π / 2 * (18 / 10) * L) ^ 8) := by
          gcongr
          have h1 := gmom8_le
          have h2 := hgp 8
          have : (π / 2 * (18 / 10) * L) ^ 8 = (π / 2) ^ 8 * ((18 / 10) ^ 8 * L ^ 8) := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2
            (integral_nonneg fun x => pow_nonneg (Real.sqrt_nonneg _) _) (by norm_num))
            (by positivity)
      _ = ENNReal.ofReal (B ^ 8) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  set kA := (A + B + C) ^ 7 / A ^ 7
  set kB := (A + B + C) ^ 7 / B ^ 7
  set kC := (A + B + C) ^ 7 / C ^ 7
  have mD : Measurable (fun ξ => |S ξ - sb|) := (hc.measurable.sub_const _).abs
  calc ∫⁻ ξ, ENNReal.ofReal (|S ξ ^ 2 - qb| ^ 8) ∂stdGauss ι
      ≤ ∫⁻ ξ, (ENNReal.ofReal kA * ENNReal.ofReal ((|S ξ - sb| ^ 2) ^ 8) +
          ENNReal.ofReal kB * ENNReal.ofReal ((2 * (√qb + 1) * |S ξ - sb|) ^ 8) +
          ENNReal.ofReal (kC * V ^ 8)) ∂stdGauss ι := by
        refine lintegral_mono fun ξ => ?_
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hpt ξ)
    _ = ENNReal.ofReal kA * ∫⁻ ξ, ENNReal.ofReal ((|S ξ - sb| ^ 2) ^ 8) ∂stdGauss ι +
          ENNReal.ofReal kB * ∫⁻ ξ, ENNReal.ofReal ((2 * (√qb + 1) * |S ξ - sb|) ^ 8) ∂stdGauss ι +
          ENNReal.ofReal (kC * V ^ 8) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        rw [lintegral_add_left (f := fun a => ENNReal.ofReal kA * ENNReal.ofReal ((|S a - sb| ^ 2) ^ 8))
          (show Measurable (fun a => ENNReal.ofReal kA * ENNReal.ofReal ((|S a - sb| ^ 2) ^ 8)) from
            (ENNReal.measurable_ofReal.comp ((mD.pow_const 2).pow_const 8)).const_mul _)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal kA * ENNReal.ofReal (A ^ 8) + ENNReal.ofReal kB * ENNReal.ofReal (B ^ 8) +
          ENNReal.ofReal (kC * C ^ 8) := by
        gcongr
    _ = ENNReal.ofReal ((A + B + C) ^ 8) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        simp only [kA, kB, kC]
        field_simp

end BstLean.Part170
