import BstLean.Part150Kval

/-!
# Part 150, item 2: the Fourier representation of the binomial replacement error

Paper source: `onW45-opus-prover.md` §2, Lemma B-F, Step 1 (the displays
`|D(x)| ≤ (1/π)∫_0^∞|e^{−t²/2} − cos(t/√J)^J|/t² dt` and
`|D_2(x)| ≤ (2/π)∫_0^∞|e^{−t²/2} − cos(t/√J)^J|/t³ dt`). The Lean proof does not use the Fourier
inversion theorem: it uses the kernels `|y| = (2/π)∫_0^∞(1 − cos(ty))/t² dt` and
`y|y| = (4/π)∫_0^∞(ty − sin(ty))/t³ dt` and exchanges the integrals.

* `dChar J t = e^{−t²/2} − cos(t/√J)^J`: the difference of the characteristic functions.
* `diff_ker1`, `diff_ker2`: the exact formulas
  `(π/2)(E|x + Z_J| − E|x + Z|) = ∫_0^∞ cos(tx)·dChar J t/t² dt`,
  `(π/4)(E(x + Z_J)|x + Z_J| − E(x + Z)|x + Z|) = ∫_0^∞ sin(tx)·dChar J t/t³ dt`.
* **`relu_rep`**, **`reluSq_rep`**: for every majorant `M` of `|dChar J t|/t²` (of `/t³`) on
  `(0, ∞)`: `|E relu(a + sZ_J) − ψ_s(a)| ≤ (s/π)∫M` and
  `|E relu(a + sZ_J)² − E relu(a + sZ)²| ≤ (2s²/π)∫M`, every real `a`, `s ≥ 0`, `J ≥ 1`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open BstLean.Part130 BstLean.Part137 BstLean.Part141

/-- The difference of the characteristic functions of `Z` and `Z_J`. -/
noncomputable def dChar (J : ℕ) (t : ℝ) : ℝ := rexp (-(t ^ 2 / 2)) - Real.cos (t / √(J : ℝ)) ^ J

/-- The binomial side of the first kernel. -/
theorem bin_ker1 (J : ℕ) (x : ℝ) :
    IntegrableOn (fun t : ℝ => (1 - Real.cos (t / √(J : ℝ)) ^ J * Real.cos (t * x)) / t ^ 2)
      (Ioi 0) ∧
    K1 * binMean J (fun z => |x + z|) =
      ∫ t in Ioi 0, (1 - Real.cos (t / √(J : ℝ)) ^ J * Real.cos (t * x)) / t ^ 2 := by
  have hinner : ∀ t : ℝ, binMean J (fun z => ker1 t (x + z)) =
      (1 - Real.cos (t / √(J : ℝ)) ^ J * Real.cos (t * x)) / t ^ 2 := by
    intro t
    have e : (fun z => ker1 t (x + z)) = fun z => (t ^ 2)⁻¹ * (1 - Real.cos (t * (x + z))) := by
      funext z; unfold ker1; rw [div_eq_inv_mul]
    rw [e, binMean_const_mul, binMean_sub J (fun _ => 1) (fun z => Real.cos (t * (x + z))),
      binMean_const, binMean_cos]
    ring
  have hI : IntegrableOn (fun t => binMean J (fun z => ker1 t (x + z))) (Ioi 0) := by
    unfold binMean
    exact integrable_finsetSum _ fun j _ => (ker1_integrableOn _).const_mul _
  constructor
  · exact hI.congr_fun (fun t _ => hinner t) measurableSet_Ioi
  · calc K1 * binMean J (fun z => |x + z|)
        = binMean J (fun z => ∫ t in Ioi 0, ker1 t (x + z)) := by
          simp_rw [ker1_integral]; rw [← binMean_const_mul]; congr 1; funext z; ring
      _ = ∫ t in Ioi 0, binMean J (fun z => ker1 t (x + z)) := by
          unfold binMean
          rw [integral_finsetSum _ fun j _ => (ker1_integrableOn _).const_mul _]
          simp_rw [integral_const_mul]
      _ = _ := by simp_rw [hinner]

/-- The binomial side of the second kernel. -/
theorem bin_ker2 (J : ℕ) (x : ℝ) :
    IntegrableOn (fun t : ℝ => (t * x - Real.cos (t / √(J : ℝ)) ^ J * Real.sin (t * x)) / t ^ 3)
      (Ioi 0) ∧
    K2 * binMean J (fun z => (x + z) * |x + z|) =
      ∫ t in Ioi 0, (t * x - Real.cos (t / √(J : ℝ)) ^ J * Real.sin (t * x)) / t ^ 3 := by
  have hinner : ∀ t : ℝ, binMean J (fun z => ker2 t (x + z)) =
      (t * x - Real.cos (t / √(J : ℝ)) ^ J * Real.sin (t * x)) / t ^ 3 := by
    intro t
    have e : (fun z => ker2 t (x + z)) =
        fun z => (t ^ 3)⁻¹ * ((t * x + t * z) - Real.sin (t * (x + z))) := by
      funext z; unfold ker2; rw [div_eq_inv_mul, mul_add]
    rw [e, binMean_const_mul, binMean_sub J (fun z => t * x + t * z)
      (fun z => Real.sin (t * (x + z))), binMean_affine, binMean_sin]
    ring
  have hI : IntegrableOn (fun t => binMean J (fun z => ker2 t (x + z))) (Ioi 0) := by
    unfold binMean
    exact integrable_finsetSum _ fun j _ => (ker2_integrableOn _).const_mul _
  constructor
  · exact hI.congr_fun (fun t _ => hinner t) measurableSet_Ioi
  · calc K2 * binMean J (fun z => (x + z) * |x + z|)
        = binMean J (fun z => ∫ t in Ioi 0, ker2 t (x + z)) := by
          simp_rw [ker2_integral]; rw [← binMean_const_mul]; congr 1; funext z; ring
      _ = ∫ t in Ioi 0, binMean J (fun z => ker2 t (x + z)) := by
          unfold binMean
          rw [integral_finsetSum _ fun j _ => (ker2_integrableOn _).const_mul _]
          simp_rw [integral_const_mul]
      _ = _ := by simp_rw [hinner]

/-- **The exact formula for the first moment.** -/
theorem diff_ker1 (J : ℕ) (x : ℝ) :
    IntegrableOn (fun t : ℝ => Real.cos (t * x) * dChar J t / t ^ 2) (Ioi 0) ∧
    π / 2 * (binMean J (fun z => |x + z|) - ∫ z, |x + z| ∂gaussianReal 0 1) =
      ∫ t in Ioi 0, Real.cos (t * x) * dChar J t / t ^ 2 := by
  obtain ⟨hb, hbe⟩ := bin_ker1 J x
  obtain ⟨hg, hge⟩ := gauss_ker1 x
  have e : ∀ t : ℝ, Real.cos (t * x) * dChar J t / t ^ 2 =
      (1 - Real.cos (t / √(J : ℝ)) ^ J * Real.cos (t * x)) / t ^ 2 -
        (1 - rexp (-(t ^ 2 / 2)) * Real.cos (t * x)) / t ^ 2 := by
    intro t; unfold dChar; ring
  simp_rw [e]
  refine ⟨hb.sub hg, ?_⟩
  rw [integral_sub hb hg, ← hbe, ← hge, K1_eq]
  ring

/-- **The exact formula for the second moment.** -/
theorem diff_ker2 (J : ℕ) (x : ℝ) :
    IntegrableOn (fun t : ℝ => Real.sin (t * x) * dChar J t / t ^ 3) (Ioi 0) ∧
    π / 4 * (binMean J (fun z => (x + z) * |x + z|) -
        ∫ z, (x + z) * |x + z| ∂gaussianReal 0 1) =
      ∫ t in Ioi 0, Real.sin (t * x) * dChar J t / t ^ 3 := by
  obtain ⟨hb, hbe⟩ := bin_ker2 J x
  obtain ⟨hg, hge⟩ := gauss_ker2 x
  have e : ∀ t : ℝ, Real.sin (t * x) * dChar J t / t ^ 3 =
      (t * x - Real.cos (t / √(J : ℝ)) ^ J * Real.sin (t * x)) / t ^ 3 -
        (t * x - rexp (-(t ^ 2 / 2)) * Real.sin (t * x)) / t ^ 3 := by
    intro t; unfold dChar; ring
  simp_rw [e]
  refine ⟨hb.sub hg, ?_⟩
  rw [integral_sub hb hg, ← hbe, ← hge, K2_eq]
  ring

/-! ## From `|y|` and `y|y|` to `relu` -/

lemma relu_eq_abs (y : ℝ) : relu y = (y + |y|) / 2 := by
  unfold relu
  rcases le_total 0 y with h | h
  · rw [max_eq_right h, abs_of_nonneg h]; ring
  · rw [max_eq_left h, abs_of_nonpos h]; ring

lemma relu_sq_eq_abs (y : ℝ) : relu y ^ 2 = (y ^ 2 + y * |y|) / 2 := by
  unfold relu
  rcases le_total 0 y with h | h
  · rw [max_eq_right h, abs_of_nonneg h]; ring
  · rw [max_eq_left h, abs_of_nonpos h]; ring

/-- The first moment at scale `1`, for a majorant `M` of `|dChar J t|/t²`. -/
theorem relu_rep_one (J : ℕ) (x : ℝ) {M : ℝ → ℝ} (hM : IntegrableOn M (Ioi 0))
    (hb : ∀ t, 0 < t → |dChar J t| / t ^ 2 ≤ M t) :
    |binMean J (fun z => relu (x + z)) - psiS 1 x| ≤ 1 / π * ∫ t in Ioi 0, M t := by
  obtain ⟨hi, he⟩ := diff_ker1 J x
  have hp : (0 : ℝ) < π := Real.pi_pos
  have h1 : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by simpa using integrable_pow_gauss 1
  have eb : binMean J (fun z => relu (x + z)) = (x + binMean J (fun z => |x + z|)) / 2 := by
    have e : (fun z => relu (x + z)) = fun z => 2⁻¹ * ((x + 1 * z) + |x + z|) := by
      funext z; rw [relu_eq_abs]; ring
    rw [e, binMean_const_mul, binMean_add J (fun z => x + 1 * z) (fun z => |x + z|),
      binMean_affine]
    ring
  have eg : psiS 1 x = (x + ∫ z, |x + z| ∂gaussianReal 0 1) / 2 := by
    unfold psiS
    have e : (fun z : ℝ => relu (x + 1 * z)) = fun z => 2⁻¹ * ((x + z) + |x + z|) := by
      funext z; rw [relu_eq_abs]; ring_nf
    have hxz : Integrable (fun z : ℝ => x + z) (gaussianReal 0 1) := (integrable_const x).add h1
    have hxv : ∫ z : ℝ, x + z ∂gaussianReal 0 1 = x := by
      rw [integral_add (integrable_const x) h1, integral_id_gaussianReal]; simp
    rw [e, integral_const_mul, integral_add hxz (integrable_abs_shift x), hxv]
    ring
  have hn : |∫ t in Ioi 0, Real.cos (t * x) * dChar J t / t ^ 2| ≤ ∫ t in Ioi 0, M t := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hM ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (pow_pos ht0 2)]
    refine le_trans ?_ (hb t ht0)
    gcongr
    calc |Real.cos (t * x)| * |dChar J t| ≤ 1 * |dChar J t| :=
          mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |dChar J t| := one_mul _
  rw [eb, eg]
  have e3 : (x + binMean J (fun z => |x + z|)) / 2 - (x + ∫ z, |x + z| ∂gaussianReal 0 1) / 2 =
      1 / π * (π / 2 * (binMean J (fun z => |x + z|) - ∫ z, |x + z| ∂gaussianReal 0 1)) := by
    field_simp; ring
  rw [e3, he, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
  exact mul_le_mul_of_nonneg_left hn (by positivity)

/-- The second moment at scale `1`, for a majorant `M` of `|dChar J t|/t³`. -/
theorem reluSq_rep_one {J : ℕ} (hJ : 1 ≤ J) (x : ℝ) {M : ℝ → ℝ} (hM : IntegrableOn M (Ioi 0))
    (hb : ∀ t, 0 < t → |dChar J t| / t ^ 3 ≤ M t) :
    |binMean J (fun z => relu (x + z) ^ 2) - ∫ z, relu (x + z) ^ 2 ∂gaussianReal 0 1| ≤
      2 / π * ∫ t in Ioi 0, M t := by
  obtain ⟨hi, he⟩ := diff_ker2 J x
  have hp : (0 : ℝ) < π := Real.pi_pos
  have eb : binMean J (fun z => relu (x + z) ^ 2) =
      (x ^ 2 + 1 + binMean J (fun z => (x + z) * |x + z|)) / 2 := by
    have e : (fun z => relu (x + z) ^ 2) = fun z => 2⁻¹ * ((x + 1 * z) ^ 2 + (x + z) * |x + z|) := by
      funext z; rw [relu_sq_eq_abs]; ring
    rw [e, binMean_const_mul, binMean_add J (fun z => (x + 1 * z) ^ 2) (fun z => (x + z) * |x + z|),
      binMean_affine_sq hJ]
    ring
  have eg : ∫ z, relu (x + z) ^ 2 ∂gaussianReal 0 1 =
      (x ^ 2 + 1 + ∫ z, (x + z) * |x + z| ∂gaussianReal 0 1) / 2 := by
    have e : (fun z : ℝ => relu (x + z) ^ 2) = fun z => 2⁻¹ * ((x + z) ^ 2 + (x + z) * |x + z|) := by
      funext z; rw [relu_sq_eq_abs]; ring
    have h1 : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by simpa using integrable_pow_gauss 1
    have h2 : ∫ z : ℝ, z ^ 2 ∂gaussianReal 0 1 = 1 := by
      rw [BstLean.Part29.gaussMom_eq 2]
      norm_num [BstLean.Part29.gaussMom, Nat.doubleFactorial, Nat.even_iff]
    have hs : ∫ z : ℝ, (x + z) ^ 2 ∂gaussianReal 0 1 = x ^ 2 + 1 := by
      have e2 : (fun z : ℝ => (x + z) ^ 2) = fun z => (x ^ 2 + (2 * x) * z) + z ^ 2 := by
        funext z; ring
      have hl : Integrable (fun z : ℝ => x ^ 2 + (2 * x) * z) (gaussianReal 0 1) :=
        (integrable_const _).add (h1.const_mul _)
      have hlv : ∫ z : ℝ, x ^ 2 + (2 * x) * z ∂gaussianReal 0 1 = x ^ 2 := by
        rw [integral_add (integrable_const _) (h1.const_mul _), integral_const_mul,
          integral_id_gaussianReal]
        simp
      rw [e2, integral_add hl (integrable_pow_gauss 2), hlv, h2]
    rw [e, integral_const_mul, integral_add (integrable_shift_sq x) (integrable_shift_mul_abs x), hs]
    ring
  have hn : |∫ t in Ioi 0, Real.sin (t * x) * dChar J t / t ^ 3| ≤ ∫ t in Ioi 0, M t := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hM ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (pow_pos ht0 3)]
    refine le_trans ?_ (hb t ht0)
    gcongr
    calc |Real.sin (t * x)| * |dChar J t| ≤ 1 * |dChar J t| :=
          mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
      _ = |dChar J t| := one_mul _
  rw [eb, eg]
  have e3 : (x ^ 2 + 1 + binMean J (fun z => (x + z) * |x + z|)) / 2 -
      (x ^ 2 + 1 + ∫ z, (x + z) * |x + z| ∂gaussianReal 0 1) / 2 =
      2 / π * (π / 4 * (binMean J (fun z => (x + z) * |x + z|) -
        ∫ z, (x + z) * |x + z| ∂gaussianReal 0 1)) := by
    field_simp; ring
  rw [e3, he, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / π)]
  exact mul_le_mul_of_nonneg_left hn (by positivity)

lemma relu_scale {s : ℝ} (hs : 0 < s) (a z : ℝ) : relu (a + s * z) = s * relu (a / s + z) := by
  unfold relu
  rw [show a + s * z = s * (a / s + z) by field_simp, mul_max_of_nonneg _ _ hs.le, mul_zero]

/-- **The representation bound for the first moment**: every real `a`, `s ≥ 0`. -/
theorem relu_rep (J : ℕ) (a : ℝ) {s : ℝ} (hs : 0 ≤ s) {M : ℝ → ℝ} (hM : IntegrableOn M (Ioi 0))
    (hb : ∀ t, 0 < t → |dChar J t| / t ^ 2 ≤ M t) :
    |binMean J (fun z => relu (a + s * z)) - psiS s a| ≤ s * (1 / π * ∫ t in Ioi 0, M t) := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [psiS, binMean_const]
  · have e1 : (fun z => relu (a + s * z)) = fun z => s * relu (a / s + z) := by
      funext z; exact relu_scale hs a z
    have e2 : psiS s a = s * psiS 1 (a / s) := by
      unfold psiS
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show relu (a + s * z) = s * relu (a / s + 1 * z)
      rw [one_mul]; exact relu_scale hs a z
    rw [e1, binMean_const_mul, e2, ← mul_sub, abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left (relu_rep_one J (a / s) hM hb) hs.le

/-- **The representation bound for the second moment**: every real `a`, `s ≥ 0`, `J ≥ 1`. -/
theorem reluSq_rep {J : ℕ} (hJ : 1 ≤ J) (a : ℝ) {s : ℝ} (hs : 0 ≤ s) {M : ℝ → ℝ}
    (hM : IntegrableOn M (Ioi 0)) (hb : ∀ t, 0 < t → |dChar J t| / t ^ 3 ≤ M t) :
    |binMean J (fun z => relu (a + s * z) ^ 2) - ∫ z, relu (a + s * z) ^ 2 ∂gaussianReal 0 1| ≤
      s ^ 2 * (2 / π * ∫ t in Ioi 0, M t) := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [binMean_const]
  · have e1 : (fun z => relu (a + s * z) ^ 2) = fun z => s ^ 2 * relu (a / s + z) ^ 2 := by
      funext z; rw [relu_scale hs a z]; ring
    rw [e1, binMean_const_mul, integral_const_mul, ← mul_sub, abs_mul,
      abs_of_pos (pow_pos hs 2)]
    exact mul_le_mul_of_nonneg_left (reluSq_rep_one hJ (a / s) hM hb) (by positivity)

end BstLean.Part150
