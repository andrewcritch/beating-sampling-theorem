import BstLean.Part86SliceRH
import BstLean.Part86Gauss
import BstLean.Part86Inst
import BstLean.Part89Defs

/-!
# Part 89: the slice reverse Hölder inequality with the sharp constant `9^D`

* `sphere_rh9`: `E H(ω)⁴ ≤ 9^D (E H(ω)²)²` for `deg H ≤ D`, `ω` uniform on the sphere.
  Proof: as `Part86.sphere_rh`, but the fourth power of the parity split is expanded exactly;
  the odd terms vanish and the mixed term is bounded by Cauchy–Schwarz.
* `sliceRHRK9`: the same on every slice of `D_{t,v}`.
* `sliceRH_modRK9`: the model form.
-/

namespace BstLean.Part89

open MeasureTheory MvPolynomial
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part41 (Mono)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part56 (UnitV polarPoint perpDir axialR axialS tailReconstruct)
open BstLean.Part86
open BstLean.Part86.SliceRH

/-- An odd integrable function has Gaussian integral zero. -/
lemma odd_int_zero {k : ℕ} (f : (Fin k → ℝ) → ℝ) (hf : Integrable f (stdGauss (Fin k)))
    (hneg : ∀ z, f (-z) = -f z) : ∫ z, f z ∂stdGauss (Fin k) = 0 := by
  have hinv := BstLean.Part33.stdGauss_neg_invariant (ι := Fin k)
  have h := integral_map (μ := stdGauss (Fin k)) (φ := fun z : Fin k → ℝ => -z)
    measurable_neg.aemeasurable (f := f)
    (by rw [hinv]; exact hf.aestronglyMeasurable)
  rw [hinv] at h
  simp only [hneg, integral_neg] at h
  linarith

/-- **Reverse Hölder inequality on the sphere, sharp constant**:
`E H(ω)⁴ ≤ 9^D (E H(ω)²)²`. -/
theorem sphere_rh9 (k D : ℕ) (hk : 1 ≤ k) (H : MvPolynomial (Fin k) ℝ) (hH : H.totalDegree ≤ D) :
    ∫ z, (eval (unitF53 z) H) ^ 4 ∂stdGauss (Fin k) ≤
      9 ^ D * (∫ z, (eval (unitF53 z) H) ^ 2 ∂stdGauss (Fin k)) ^ 2 := by
  by_cases hD : D = 0
  · subst hD
    have hC : H = C (H.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hH)
    rw [hC]
    simp only [eval_C, integral_const, smul_eq_mul, pow_zero]
    simp
    exact le_of_eq (by ring)
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr hD
  set S0 := (Finset.range (D + 1)).filter (fun b => b % 2 = 0) with hS0
  set S1 := (Finset.range (D + 1)).filter (fun b => ¬ b % 2 = 0) with hS1
  set N0 := 2 * (D / 2) with hN0
  set N1 := 2 * ((D - 1) / 2) + 1 with hN1
  have c0 : ∀ b ∈ S0, 2 * ((N0 - b) / 2) + b = N0 := by
    intro b hb
    simp only [hS0, Finset.mem_filter, Finset.mem_range] at hb
    omega
  have c1 : ∀ b ∈ S1, 2 * ((N1 - b) / 2) + b = N1 := by
    intro b hb
    simp only [hS1, Finset.mem_filter, Finset.mem_range] at hb
    omega
  set P0 := hz H S0 N0 with hP0
  set P1 := hz H S1 N1 with hP1
  have r0 := par_rh hk P0 N0 (hz_deg H S0 N0 c0) (hz_hom H S0 N0 c0)
  have r1 := par_rh hk P1 N1 (hz_deg H S1 N1 c1) (hz_hom H S1 N1 c1)
  set u0 : (Fin k → ℝ) → ℝ := fun z => eval (unitF53 z) P0 with hu0
  set u1 : (Fin k → ℝ) → ℝ := fun z => eval (unitF53 z) P1 with hu1
  have hsplit : ∀ᵐ z ∂stdGauss (Fin k), eval (unitF53 z) H = u0 z + u1 z := by
    filter_upwards [BstLean.Part57.PropD57.gauss_ne_zero_ae k hk] with z hzne
    have h1 := unit_sumsq z hzne
    simp only [hu0, hu1, hP0, hP1]
    rw [hz_unit H S0 N0 _ h1, hz_unit H S1 N1 _ h1, hS0, hS1,
      Finset.sum_filter_add_sum_filter_not, ← map_sum, sum_comp H D hH]
  -- integrability
  have hc0 : Continuous fun ω : Fin k → ℝ => eval ω P0 := continuous_eval P0
  have hc1 : Continuous fun ω : Fin k → ℝ => eval ω P1 := continuous_eval P1
  have i04 : Integrable (fun z => u0 z ^ 4) (stdGauss (Fin k)) := int_unit _ (hc0.pow 4)
  have i14 : Integrable (fun z => u1 z ^ 4) (stdGauss (Fin k)) := int_unit _ (hc1.pow 4)
  have i02 : Integrable (fun z => u0 z ^ 2) (stdGauss (Fin k)) := int_unit _ (hc0.pow 2)
  have i12 : Integrable (fun z => u1 z ^ 2) (stdGauss (Fin k)) := int_unit _ (hc1.pow 2)
  have i01 : Integrable (fun z => u0 z * u1 z) (stdGauss (Fin k)) := int_unit _ (hc0.mul hc1)
  have i31 : Integrable (fun z => u0 z ^ 3 * u1 z) (stdGauss (Fin k)) :=
    int_unit _ ((hc0.pow 3).mul hc1)
  have i13 : Integrable (fun z => u0 z * u1 z ^ 3) (stdGauss (Fin k)) :=
    int_unit _ (hc0.mul (hc1.pow 3))
  have i22 : Integrable (fun z => u0 z ^ 2 * u1 z ^ 2) (stdGauss (Fin k)) :=
    int_unit _ ((hc0.pow 2).mul (hc1.pow 2))
  -- parity
  have n0 : ∀ z, u0 (-z) = u0 z := by
    intro z
    simp only [hu0, hP0, unit_neg, hz_hom H S0 N0 c0]
    have e0 : (-1 : ℝ) ^ N0 = 1 := by rw [hN0, pow_mul]; norm_num
    rw [e0]; ring
  have n1 : ∀ z, u1 (-z) = -u1 z := by
    intro z
    simp only [hu1, hP1, unit_neg, hz_hom H S1 N1 c1]
    have e1 : (-1 : ℝ) ^ N1 = -1 := by rw [hN1, pow_succ, pow_mul]; norm_num
    rw [e1]; ring
  have hcross : ∫ z, u0 z * u1 z ∂stdGauss (Fin k) = 0 :=
    odd_int_zero _ i01 (fun z => by rw [n0, n1]; ring)
  have h31 : ∫ z, u0 z ^ 3 * u1 z ∂stdGauss (Fin k) = 0 :=
    odd_int_zero _ i31 (fun z => by rw [n0, n1]; ring)
  have h13 : ∫ z, u0 z * u1 z ^ 3 ∂stdGauss (Fin k) = 0 :=
    odd_int_zero _ i13 (fun z => by rw [n0, n1]; ring)
  have hA : ∫ z, (eval (unitF53 z) H) ^ 4 ∂stdGauss (Fin k) =
      ∫ z, u0 z ^ 4 ∂stdGauss (Fin k) + 6 * ∫ z, u0 z ^ 2 * u1 z ^ 2 ∂stdGauss (Fin k) +
        ∫ z, u1 z ^ 4 ∂stdGauss (Fin k) := by
    have e : ∫ z, (eval (unitF53 z) H) ^ 4 ∂stdGauss (Fin k) =
        ∫ z, ((u0 z ^ 4 + 6 * (u0 z ^ 2 * u1 z ^ 2)) + u1 z ^ 4) +
          (4 * (u0 z ^ 3 * u1 z) + 4 * (u0 z * u1 z ^ 3)) ∂stdGauss (Fin k) := by
      refine integral_congr_ae ?_
      filter_upwards [hsplit] with z hz
      rw [hz]; ring
    have j1 : Integrable (fun z => u0 z ^ 4 + 6 * (u0 z ^ 2 * u1 z ^ 2)) (stdGauss (Fin k)) :=
      i04.add (i22.const_mul 6)
    have j2 : Integrable (fun z => (u0 z ^ 4 + 6 * (u0 z ^ 2 * u1 z ^ 2)) + u1 z ^ 4)
        (stdGauss (Fin k)) := j1.add i14
    have j3 : Integrable (fun z => 4 * (u0 z ^ 3 * u1 z) + 4 * (u0 z * u1 z ^ 3))
        (stdGauss (Fin k)) := (i31.const_mul 4).add (i13.const_mul 4)
    rw [e, integral_add j2 j3, integral_add j1 i14, integral_add i04 (i22.const_mul 6),
      integral_add (i31.const_mul 4) (i13.const_mul 4), integral_const_mul, integral_const_mul,
      integral_const_mul, h31, h13]
    ring
  have hBq : ∫ z, (eval (unitF53 z) H) ^ 2 ∂stdGauss (Fin k) =
      ∫ z, u0 z ^ 2 ∂stdGauss (Fin k) + ∫ z, u1 z ^ 2 ∂stdGauss (Fin k) := by
    have e : ∫ z, (eval (unitF53 z) H) ^ 2 ∂stdGauss (Fin k) =
        ∫ z, (u0 z ^ 2 + u1 z ^ 2) + 2 * (u0 z * u1 z) ∂stdGauss (Fin k) := by
      refine integral_congr_ae ?_
      filter_upwards [hsplit] with z hz
      rw [hz]; ring
    have i02p : Integrable (fun z => u0 z ^ 2 + u1 z ^ 2) (stdGauss (Fin k)) := i02.add i12
    have i01c : Integrable (fun z => 2 * (u0 z * u1 z)) (stdGauss (Fin k)) := i01.const_mul 2
    rw [e, integral_add i02p i01c, integral_add i02 i12, integral_const_mul, hcross]
    ring
  -- Cauchy–Schwarz for the mixed term
  have hcs : (∫ z, u0 z ^ 2 * u1 z ^ 2 ∂stdGauss (Fin k)) ^ 2 ≤
      (∫ z, u0 z ^ 4 ∂stdGauss (Fin k)) * ∫ z, u1 z ^ 4 ∂stdGauss (Fin k) := by
    have e0 : (fun z => (u0 z ^ 2) ^ 2) = fun z => u0 z ^ 4 := by funext z; ring
    have e1 : (fun z => (u1 z ^ 2) ^ 2) = fun z => u1 z ^ 4 := by funext z; ring
    have h := BstLean.Part86.XGauss.cs_sq (stdGauss (Fin k)) (fun z => u0 z ^ 2)
      (fun z => u1 z ^ 2) (by simpa only [e0] using i04) (by simpa only [e1] using i14) i22
    simpa only [e0, e1] using h
  rw [hA, hBq]
  set a0 := ∫ z, u0 z ^ 4 ∂stdGauss (Fin k)
  set a1 := ∫ z, u1 z ^ 4 ∂stdGauss (Fin k)
  set b0 := ∫ z, u0 z ^ 2 ∂stdGauss (Fin k)
  set b1 := ∫ z, u1 z ^ 2 ∂stdGauss (Fin k)
  set c := ∫ z, u0 z ^ 2 * u1 z ^ 2 ∂stdGauss (Fin k)
  have hb0 : 0 ≤ b0 := integral_nonneg fun z => sq_nonneg _
  have hb1 : 0 ≤ b1 := integral_nonneg fun z => sq_nonneg _
  have ha0 : 0 ≤ a0 := integral_nonneg fun z => by positivity
  have p0 : (9 : ℝ) ^ N0 ≤ 9 ^ D := pow_le_pow_right₀ (by norm_num) (by omega)
  have p1 : (9 : ℝ) ^ N1 ≤ 9 ^ D := pow_le_pow_right₀ (by norm_num) (by omega)
  have q0 : a0 ≤ 9 ^ D * b0 ^ 2 := r0.trans (mul_le_mul_of_nonneg_right p0 (sq_nonneg _))
  have q1 : a1 ≤ 9 ^ D * b1 ^ 2 := r1.trans (mul_le_mul_of_nonneg_right p1 (sq_nonneg _))
  have h9 : (0 : ℝ) < 9 ^ D := by positivity
  have hNN : (9 : ℝ) ^ N0 * 9 ^ N1 * 9 = (9 ^ D) ^ 2 := by
    rw [← pow_add, ← pow_succ, ← pow_mul]
    congr 1; omega
  have hX : 0 ≤ 9 ^ D / 3 * (b0 * b1) := by positivity
  have hsq : c ^ 2 ≤ (9 ^ D / 3 * (b0 * b1)) ^ 2 := by
    have hprod := mul_le_mul r0 r1 (integral_nonneg fun z => by positivity)
      (by positivity : (0 : ℝ) ≤ 9 ^ N0 * b0 ^ 2)
    refine (hcs.trans hprod).trans (le_of_eq ?_)
    have : (9 ^ D / 3 * (b0 * b1)) ^ 2 = ((9 : ℝ) ^ D) ^ 2 / 9 * (b0 ^ 2 * b1 ^ 2) := by ring
    rw [this, ← hNN]; ring
  have hc : c ≤ 9 ^ D / 3 * (b0 * b1) := le_trans (le_abs_self _) (abs_le_of_sq_le_sq hsq hX)
  calc a0 + 6 * c + a1 ≤ 9 ^ D * b0 ^ 2 + 6 * (9 ^ D / 3 * (b0 * b1)) + 9 ^ D * b1 ^ 2 := by
        linarith
    _ = 9 ^ D * (b0 + b1) ^ 2 := by ring

/-- **Slice reverse Hölder inequality for `D_{t,v}`, sharp constant `9^D`.** -/
theorem sliceRHRK9 (m D : ℕ) (hm : 1 ≤ m) : SliceRHRK9 m D := by
  intro v hv a r Q hQ
  obtain ⟨b, hb⟩ := BstLean.Part56.unit_basis_exists (m + 1) (by omega) v hv
  have hb0 : b 0 = WithLp.toLp 2 v := hb
  set S := axialS a r
  set R := axialR a r
  set c : Fin (m + 1) → Fin m → ℝ :=
    fun i j => tailReconstruct b (fun j' => if j = j' then 1 else 0) i with hc
  set L : Fin (m + 1) → MvPolynomial (Fin m) ℝ :=
    fun i => C (S * v i) + ∑ j, C (R * c i j) * X j with hL
  have hLd : ∀ i, (L i).totalDegree ≤ 1 := by
    intro i
    refine (totalDegree_add _ _).trans (max_le (by rw [totalDegree_C]; omega) ?_)
    refine BstLean.Part84.totalDegree_finset_sum_le (fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]
  set Q' := aeval L Q with hQ'
  have hQ'd : Q'.totalDegree ≤ D := (BstLean.Part84.deg_aeval L hLd Q).trans hQ
  have hev : ∀ ω : Fin m → ℝ,
      eval (polarPoint v (tailReconstruct b ω) a r) Q = eval ω Q' := by
    intro ω
    rw [hQ', BstLean.Part84.eval_aeval']
    have hx : polarPoint v (tailReconstruct b ω) a r = fun i => eval ω (L i) := ?_
    · rw [hx]
    funext i
    simp only [hL, map_add, eval_C, map_sum, map_mul, eval_X, polarPoint, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [SliceRH.tail_coord b ω i, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hc]; ring
  have hcont : Continuous fun w : Fin (m + 1) → ℝ => eval (polarPoint v w a r) Q := by
    have : Continuous fun w : Fin (m + 1) → ℝ => polarPoint v w a r := by
      unfold polarPoint; fun_prop
    exact (continuous_eval Q).comp this
  have e4 := SliceRH.perp_int b v hb0 (fun w => (eval (polarPoint v w a r) Q) ^ 4)
    (hcont.pow 4).measurable (fun w => by positivity)
  have e2 := SliceRH.perp_int b v hb0 (fun w => (eval (polarPoint v w a r) Q) ^ 2)
    (hcont.pow 2).measurable (fun w => sq_nonneg _)
  simp only [hev] at e4 e2
  rw [e4, e2]
  exact sphere_rh9 m D hm Q' hQ'd

/-- **Slice reverse Hölder inequality for the model**, constant `9^D`, from `SliceRHRK9`. -/
theorem sliceRH_modRK9 (m d : ℕ) (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (E : JR (m + 1) d → Mono (m + 1) d → ℝ) (D : ℕ) (hRH : SliceRHRK9 m D) :
    SliceRH (modRK m d t v E) D (9 ^ D) := by
  intro p Q hQ
  exact hRH v hv p.1 (radF53 p.2) Q hQ

end BstLean.Part89

#print axioms BstLean.Part89.sphere_rh9
#print axioms BstLean.Part89.sliceRHRK9
#print axioms BstLean.Part89.sliceRH_modRK9
