import BstLean.Part152Tau
import BstLean.Part148GC

/-!
# Part 152 (file `GC`): the SHARP Gaussian concentration inequality for Lipschitz functions

Role: `delegations/statements/p152-spec.md`. `f : (ι → ℝ) → ℝ` is Lipschitz for the Euclidean
norm with constant `L` (the predicate `BstLean.Part148.EuLip`), `γ = stdGauss ι`.

* **`gaussConc_mgf_sharp`**: `E exp(λ(f − E f)) ≤ exp(λ²L²/2)` for every real `λ`.
* **`gaussConc_lower_sharp`**, **`gaussConc_upper_sharp`**: `Pr(f ≤ E f − t) ≤ exp(−t²/(2L²))`
  and `Pr(f ≥ E f + t) ≤ exp(−t²/(2L²))` for `t ≥ 0`.
* **`gaussVar_le_sharp`**: `Var f ≤ L²` (the Gaussian Poincaré inequality for Lipschitz functions).
* `gaussConc_mat_lower_sharp`, `gaussConc_mat_upper_sharp`, `gaussVar_mat_le_sharp`: the same for a
  function of a Gaussian matrix with entry variance `v` (`gaussMat` of Part 130), Lipschitz for the
  Frobenius norm: `L²` becomes `v·L²`.

Proof of the first: the Prékopa–Leindler property `tau_stdGauss` with
`U = exp(λf − K)`, `V = exp(−bf)`, `K = λ²L²/(2(1 − s))`, `b = sλ/(1 − s)`, Jensen for `V`, and
`s → 0`. The constants are the sharp ones (equality for a linear `f`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part152

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Topology
open BstLean.Part29 (stdGauss)
open BstLean.Part148 (EuLip)

section GC

variable {ι : Type} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ} {L : ℝ}

/-- The bound for a fixed weight `s`. -/
lemma mgf_step (hL0 : 0 ≤ L) (hL : EuLip f L) (lam : ℝ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∫ x, Real.exp (lam * (f x - ∫ y, f y ∂stdGauss ι)) ∂stdGauss ι ≤
      Real.exp (lam ^ 2 * L ^ 2 / (2 * (1 - s))) := by
  have h1 : 0 < 1 - s := by linarith
  have hmf : Measurable f := (hL.continuous hL0).measurable
  have hfint : Integrable f (stdGauss ι) := (BstLean.Part148.gaussConc_mgf hL0 hL 0).1
  have hint : ∀ l : ℝ, Integrable (fun x => Real.exp (l * f x)) (stdGauss ι) := fun l =>
    (BstLean.Part148.gaussConc_mgf hL0 hL l).2.1
  set m : ℝ := ∫ y, f y ∂stdGauss ι with hm
  set K : ℝ := lam ^ 2 * L ^ 2 / (2 * (1 - s)) with hK
  set b : ℝ := s * lam / (1 - s) with hb
  have hb1 : b * (1 - s) = s * lam := by rw [hb]; field_simp
  have T := tau_stdGauss (ι := ι) hs0 hs1 (fun x => ENNReal.ofReal (Real.exp (lam * f x - K)))
    (fun y => ENNReal.ofReal (Real.exp (-b * f y))) (by fun_prop) (by fun_prop)
    (fun x y => by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hs0.le,
        ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le h1.le, ← Real.exp_mul, ← Real.exp_mul,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      set r : ℝ := √(∑ i, (x i - y i) ^ 2) with hr
      have hr0 : 0 ≤ r := Real.sqrt_nonneg _
      have hr2 : ∑ i, (x i - y i) ^ 2 = r ^ 2 :=
        (Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)).symm
      beta_reduce
      rw [hr2]
      have hlip : |f x - f y| ≤ L * r := hL x y
      set q : ℝ := |lam| * L with hq
      have hq0 : 0 ≤ q := mul_nonneg (abs_nonneg _) hL0
      have hq2 : q ^ 2 = lam ^ 2 * L ^ 2 := by rw [hq, mul_pow, sq_abs]
      have hKq : K * (2 * (1 - s)) = q ^ 2 := by rw [hK, hq2]; field_simp
      have h2 : lam * (f x - f y) ≤ q * r := by
        calc lam * (f x - f y) ≤ |lam * (f x - f y)| := le_abs_self _
          _ = |lam| * |f x - f y| := abs_mul _ _
          _ ≤ |lam| * (L * r) := mul_le_mul_of_nonneg_left hlip (abs_nonneg _)
          _ = q * r := by rw [hq]; ring
      have h3 : q * r - K ≤ (1 - s) * r ^ 2 / 2 := by
        have : (q * r - K) * (2 * (1 - s)) ≤ ((1 - s) * r ^ 2 / 2) * (2 * (1 - s)) := by
          have e : (q * r - K) * (2 * (1 - s)) = 2 * (1 - s) * (q * r) - q ^ 2 := by
            rw [← hKq]; ring
          rw [e]
          nlinarith [sq_nonneg ((1 - s) * r - q)]
        exact le_of_mul_le_mul_right this (by positivity)
      have e : (lam * f x - K) * s + -b * f y * (1 - s) = s * (lam * (f x - f y) - K) := by
        have : -b * f y * (1 - s) = -(b * (1 - s)) * f y := by ring
        rw [this, hb1]; ring
      rw [e]
      have : s * (lam * (f x - f y) - K) ≤ s * ((1 - s) * r ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hs0.le
      refine this.trans (le_of_eq ?_)
      ring)
  have iA : Integrable (fun x => Real.exp (lam * f x - K)) (stdGauss ι) := by
    have e : (fun x => Real.exp (lam * f x - K)) = fun x => Real.exp (-K) * Real.exp (lam * f x) := by
      funext x
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    exact (hint lam).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal iA (ae_of_all _ fun _ => (Real.exp_pos _).le),
    ← ofReal_integral_eq_lintegral_ofReal (hint (-b)) (ae_of_all _ fun _ => (Real.exp_pos _).le)] at T
  set A : ℝ := ∫ x, Real.exp (lam * f x - K) ∂stdGauss ι with hA
  set B : ℝ := ∫ x, Real.exp (-b * f x) ∂stdGauss ι with hB
  have hA0 : 0 ≤ A := integral_nonneg fun _ => (Real.exp_pos _).le
  have hB0 : 0 ≤ B := integral_nonneg fun _ => (Real.exp_pos _).le
  rw [ENNReal.ofReal_rpow_of_nonneg hA0 hs0.le, ENNReal.ofReal_rpow_of_nonneg hB0 h1.le,
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_one] at T
  -- Jensen for `B`
  have hJ : Real.exp (-b * m) ≤ B := by
    have h := (convexOn_exp).map_integral_le (μ := stdGauss ι) (f := fun y => -b * f y)
      Real.continuous_exp.continuousOn isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _)
      (hfint.const_mul _) (hint (-b))
    rw [integral_const_mul] at h
    exact h
  have hJ2 : Real.exp (-(s * lam * m)) ≤ B ^ (1 - s) := by
    have := Real.rpow_le_rpow (Real.exp_pos _).le hJ h1.le
    rw [← Real.exp_mul] at this
    have e : -b * m * (1 - s) = -(s * lam * m) := by
      have : -b * m * (1 - s) = -(b * (1 - s)) * m := by ring
      rw [this, hb1]; ring
    rwa [e] at this
  have hAs : A ^ s ≤ Real.exp (lam * m) ^ s := by
    rw [← Real.exp_mul]
    have hpos : 0 < Real.exp (-(s * lam * m)) := Real.exp_pos _
    have l1 : A ^ s * Real.exp (-(s * lam * m)) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hJ2 (Real.rpow_nonneg hA0 _)).trans T
    have e : Real.exp (lam * m * s) * Real.exp (-(s * lam * m)) = 1 := by
      rw [← Real.exp_add]
      have : lam * m * s + -(s * lam * m) = 0 := by ring
      rw [this, Real.exp_zero]
    rw [← e] at l1
    exact le_of_mul_le_mul_right l1 hpos
  have hAle : A ≤ Real.exp (lam * m) := (Real.rpow_le_rpow_iff hA0 (Real.exp_pos _).le hs0).mp hAs
  have e1 : ∫ x, Real.exp (lam * (f x - m)) ∂stdGauss ι = Real.exp (K - lam * m) * A := by
    rw [hA, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e1]
  calc Real.exp (K - lam * m) * A ≤ Real.exp (K - lam * m) * Real.exp (lam * m) :=
        mul_le_mul_of_nonneg_left hAle (Real.exp_pos _).le
    _ = Real.exp K := by rw [← Real.exp_add]; congr 1; ring

/-- **The sharp bound of the moment generating function of a Lipschitz function of a standard
Gaussian vector**: `E exp(λ(f − E f)) ≤ exp(λ²L²/2)`. -/
theorem gaussConc_mgf_sharp (hL0 : 0 ≤ L) (hL : EuLip f L) (lam : ℝ) :
    Integrable f (stdGauss ι) ∧ Integrable (fun x => Real.exp (lam * f x)) (stdGauss ι) ∧
    ∫ x, Real.exp (lam * (f x - ∫ y, f y ∂stdGauss ι)) ∂stdGauss ι ≤
      Real.exp (lam ^ 2 * L ^ 2 / 2) := by
  obtain ⟨h1, h2, -⟩ := BstLean.Part148.gaussConc_mgf hL0 hL lam
  refine ⟨h1, h2, ?_⟩
  have hc : ContinuousAt (fun s : ℝ => Real.exp (lam ^ 2 * L ^ 2 / (2 * (1 - s)))) 0 := by
    refine Real.continuous_exp.continuousAt.comp ?_
    exact ContinuousAt.div continuousAt_const (by fun_prop) (by norm_num)
  have ht : Filter.Tendsto (fun s : ℝ => Real.exp (lam ^ 2 * L ^ 2 / (2 * (1 - s)))) (𝓝[>] 0)
      (𝓝 (Real.exp (lam ^ 2 * L ^ 2 / 2))) := by
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs
  exact mgf_step hL0 hL lam hs.1 hs.2

/-- **Sharp Gaussian concentration, lower tail**: `Pr(f ≤ E f − t) ≤ exp(−t²/(2L²))`. -/
theorem gaussConc_lower_sharp (hL0 : 0 ≤ L) (hL : EuLip f L) {t : ℝ} (ht : 0 ≤ t) :
    (stdGauss ι).real {x | f x ≤ ∫ y, f y ∂stdGauss ι - t} ≤
      Real.exp (-t ^ 2 / (2 * L ^ 2)) := by
  rcases hL0.eq_or_lt with h0 | hLpos
  · rw [← h0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, div_zero,
      Real.exp_zero]
    exact measureReal_le_one
  set m : ℝ := ∫ y, f y ∂stdGauss ι with hm
  set s : ℝ := t / L ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  obtain ⟨_, hI, hM⟩ := gaussConc_mgf_sharp hL0 hL (-s)
  have hI' : Integrable (fun x => Real.exp (-s * (f x - m))) (stdGauss ι) := by
    have e : (fun x => Real.exp (-s * (f x - m))) =
        fun x => Real.exp (s * m) * Real.exp (-s * f x) := by
      funext x
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    exact hI.const_mul _
  have h := measure_le_le_exp_mul_mgf (μ := stdGauss ι) (X := fun x => f x - m) (t := -s)
    (-t) (by linarith) hI'
  have hset : {x : ι → ℝ | f x - m ≤ -t} = {x | f x ≤ m - t} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [hset] at h
  refine h.trans ?_
  unfold mgf
  calc Real.exp (- -s * -t) * ∫ x, Real.exp (-s * (f x - m)) ∂stdGauss ι
      ≤ Real.exp (- -s * -t) * Real.exp ((-s) ^ 2 * L ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
    _ = Real.exp (-t ^ 2 / (2 * L ^ 2)) := by
        rw [← Real.exp_add]
        congr 1
        rw [hs]
        field_simp
        ring

/-- **Sharp Gaussian concentration, upper tail**: `Pr(f ≥ E f + t) ≤ exp(−t²/(2L²))`. -/
theorem gaussConc_upper_sharp (hL0 : 0 ≤ L) (hL : EuLip f L) {t : ℝ} (ht : 0 ≤ t) :
    (stdGauss ι).real {x | ∫ y, f y ∂stdGauss ι + t ≤ f x} ≤
      Real.exp (-t ^ 2 / (2 * L ^ 2)) := by
  have hLn : EuLip (fun x => -f x) L := by
    intro x y
    have := hL x y
    rw [show -f x - -f y = -(f x - f y) by ring, abs_neg]
    exact this
  have h := gaussConc_lower_sharp hL0 hLn ht
  rw [integral_neg] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-- `y² ≤ e^y + e^{−y} − 2`. -/
lemma sq_le_exp_add (y : ℝ) : y ^ 2 ≤ Real.exp y + Real.exp (-y) - 2 := by
  have key : ∀ z : ℝ, 0 ≤ z → z ^ 2 ≤ Real.exp z + Real.exp (-z) - 2 := by
    intro z hz
    have h1 : z / 2 ≤ Real.sinh (z / 2) := Real.self_le_sinh_iff.mpr (by positivity)
    rw [Real.sinh_eq] at h1
    have h2 : z ≤ Real.exp (z / 2) - Real.exp (-(z / 2)) := by linarith
    have e1 : Real.exp z = Real.exp (z / 2) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-z) = Real.exp (-(z / 2)) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have e3 : Real.exp (z / 2) * Real.exp (-(z / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 := pow_le_pow_left₀ hz h2 2
    rw [e1, e2]
    nlinarith
  rcases le_total 0 y with h | h
  · exact key y h
  · have := key (-y) (neg_nonneg.mpr h)
    rw [neg_neg, neg_sq] at this
    linarith

/-- **The Gaussian Poincaré inequality for Lipschitz functions**: `Var f ≤ L²`. -/
theorem gaussVar_le_sharp (hL0 : 0 ≤ L) (hL : EuLip f L) :
    Integrable (fun x => (f x - ∫ y, f y ∂stdGauss ι) ^ 2) (stdGauss ι) ∧
    ∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι ≤ L ^ 2 := by
  set m := ∫ y, f y ∂stdGauss ι with hm
  have hmf : Measurable f := (hL.continuous hL0).measurable
  have key : ∀ lam : ℝ, 0 < lam → Integrable (fun x => (f x - m) ^ 2) (stdGauss ι) ∧
      ∫ x, (f x - m) ^ 2 ∂stdGauss ι ≤ L ^ 2 * Real.exp (lam ^ 2 * L ^ 2 / 2) := by
    intro lam hl
    obtain ⟨-, i1, b1⟩ := gaussConc_mgf_sharp hL0 hL lam
    obtain ⟨-, i2, b2⟩ := gaussConc_mgf_sharp hL0 hL (-lam)
    have j1 : Integrable (fun x => Real.exp (lam * (f x - m))) (stdGauss ι) := by
      have e : (fun x => Real.exp (lam * (f x - m))) =
          fun x => Real.exp (-(lam * m)) * Real.exp (lam * f x) := by
        funext x
        rw [← Real.exp_add]
        congr 1
        ring
      rw [e]
      exact i1.const_mul _
    have j2 : Integrable (fun x => Real.exp (-lam * (f x - m))) (stdGauss ι) := by
      have e : (fun x => Real.exp (-lam * (f x - m))) =
          fun x => Real.exp (lam * m) * Real.exp (-lam * f x) := by
        funext x
        rw [← Real.exp_add]
        congr 1
        ring
      rw [e]
      exact i2.const_mul _
    have jS : Integrable (fun x => Real.exp (lam * (f x - m)) + Real.exp (-lam * (f x - m)) - 2)
        (stdGauss ι) := (j1.add j2).sub (integrable_const 2)
    have hle : ∀ x, lam ^ 2 * (f x - m) ^ 2 ≤
        Real.exp (lam * (f x - m)) + Real.exp (-lam * (f x - m)) - 2 := by
      intro x
      have h := sq_le_exp_add (lam * (f x - m))
      have e1 : (lam * (f x - m)) ^ 2 = lam ^ 2 * (f x - m) ^ 2 := by ring
      have e2 : -(lam * (f x - m)) = -lam * (f x - m) := by ring
      rw [e1, e2] at h
      exact h
    have iQ0 : Integrable (fun x => lam ^ 2 * (f x - m) ^ 2) (stdGauss ι) := by
      refine Integrable.mono' jS ((hmf.sub measurable_const).pow_const 2 |>.const_mul _
        ).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hle x
    have hc : lam ^ 2 ≠ 0 := by positivity
    have iQ : Integrable (fun x => (f x - m) ^ 2) (stdGauss ι) := by
      have := iQ0.const_mul (lam ^ 2)⁻¹
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    refine ⟨iQ, ?_⟩
    have h1 := integral_mono iQ0 jS hle
    rw [integral_const_mul] at h1
    have e : ∫ x, (Real.exp (lam * (f x - m)) + Real.exp (-lam * (f x - m)) - 2) ∂stdGauss ι =
        ∫ x, Real.exp (lam * (f x - m)) ∂stdGauss ι +
          ∫ x, Real.exp (-lam * (f x - m)) ∂stdGauss ι - 2 := by
      have jA : Integrable (fun x => Real.exp (lam * (f x - m)) +
          Real.exp (-lam * (f x - m))) (stdGauss ι) := j1.add j2
      rw [integral_sub jA (integrable_const 2), integral_add j1 j2, integral_const]
      simp
    rw [e] at h1
    have e3 : (-lam) ^ 2 = lam ^ 2 := by ring
    rw [e3] at b2
    set x0 : ℝ := lam ^ 2 * L ^ 2 / 2 with hx0
    have hx00 : 0 ≤ x0 := by positivity
    -- `e^x − 1 ≤ x·e^x`
    have hex : Real.exp x0 - 1 ≤ x0 * Real.exp x0 := by
      have h := Real.add_one_le_exp (-x0)
      have e4 : Real.exp x0 * Real.exp (-x0) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos x0]
    have h5 : lam ^ 2 * ∫ x, (f x - m) ^ 2 ∂stdGauss ι ≤ lam ^ 2 * (L ^ 2 * Real.exp x0) := by
      have : 2 * (x0 * Real.exp x0) = lam ^ 2 * (L ^ 2 * Real.exp x0) := by rw [hx0]; ring
      linarith
    exact le_of_mul_le_mul_left h5 (by positivity)
  refine ⟨(key 1 one_pos).1, ?_⟩
  have hc : ContinuousAt (fun lam : ℝ => L ^ 2 * Real.exp (lam ^ 2 * L ^ 2 / 2)) 0 := by fun_prop
  have ht : Filter.Tendsto (fun lam : ℝ => L ^ 2 * Real.exp (lam ^ 2 * L ^ 2 / 2)) (𝓝[>] 0)
      (𝓝 (L ^ 2)) := by
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  refine ge_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with lam hl
  exact (key lam hl).2

end GC

/-! ## The matrix form -/

section mat

open BstLean.Part130

variable {m k : ℕ} {g : Matrix (Fin m) (Fin k) ℝ → ℝ} {L : ℝ}

/-- A Frobenius-Lipschitz function of the scaled flat vector is `EuLip`. -/
lemma flat_euLip
    (hL : ∀ M M' : Matrix (Fin m) (Fin k) ℝ,
      |g M - g M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2)) {v : ℝ} (hv : 0 ≤ v) :
    EuLip (fun ξ : Fin m × Fin k → ℝ => g (Matrix.of fun i j => Real.sqrt v * ξ (i, j)))
      (√v * L) := by
  intro ξ η
  have h := hL (Matrix.of fun i j => Real.sqrt v * ξ (i, j))
    (Matrix.of fun i j => Real.sqrt v * η (i, j))
  have e : ∑ i, ∑ j, ((Matrix.of fun i j => Real.sqrt v * ξ (i, j) : Matrix (Fin m) (Fin k) ℝ) i j -
      (Matrix.of fun i j => Real.sqrt v * η (i, j) : Matrix (Fin m) (Fin k) ℝ) i j) ^ 2 =
      v * ∑ p, (ξ p - η p) ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.of_apply]
    rw [← mul_sub, mul_pow, Real.sq_sqrt hv]
  rw [e, Real.sqrt_mul hv] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- **Sharp Gaussian concentration for a Lipschitz function of a Gaussian matrix, lower tail.** If
`|g M − g M′| ≤ L·√(Σ_{ij}(M_{ij} − M′_{ij})²)` and the entries are independent `N(0, v)`:
`Pr(g ≤ E g − t) ≤ exp(−t²/(2·v·L²))`. -/
theorem gaussConc_mat_lower_sharp (hL0 : 0 ≤ L)
    (hL : ∀ M M' : Matrix (Fin m) (Fin k) ℝ,
      |g M - g M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2))
    {v : ℝ} (hv : 0 ≤ v) {t : ℝ} (ht : 0 ≤ t) :
    (gaussMat m k v).real {M | g M ≤ ∫ M, g M ∂gaussMat m k v - t} ≤
      Real.exp (-t ^ 2 / (2 * (v * L ^ 2))) := by
  have hgc := BstLean.Part148.matLip_continuous hL
  set T : (Fin m × Fin k → ℝ) → Matrix (Fin m) (Fin k) ℝ :=
    fun ξ => Matrix.of fun i j => Real.sqrt v * ξ (i, j) with hT
  have mT : Measurable T := measurable_ofFlat _
  have hf : EuLip (fun ξ => g (T ξ)) (√v * L) := flat_euLip hL hv
  have h := gaussConc_lower_sharp (mul_nonneg (Real.sqrt_nonneg v) hL0) hf ht
  have eI : ∫ M, g M ∂gaussMat m k v = ∫ ξ, g (T ξ) ∂stdGauss (Fin m × Fin k) := by
    unfold gaussMat
    exact integral_map mT.aemeasurable hgc.measurable.aestronglyMeasurable
  have mS : MeasurableSet {M : Matrix (Fin m) (Fin k) ℝ | g M ≤ ∫ M, g M ∂gaussMat m k v - t} :=
    measurableSet_le hgc.measurable measurable_const
  have eS : (gaussMat m k v).real {M | g M ≤ ∫ M, g M ∂gaussMat m k v - t} =
      (stdGauss (Fin m × Fin k)).real
        {ξ | g (T ξ) ≤ ∫ ξ, g (T ξ) ∂stdGauss (Fin m × Fin k) - t} := by
    have e1 := map_measureReal_apply (μ := stdGauss (Fin m × Fin k)) mT mS
    rw [← eI]
    exact e1
  rw [eS]
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, Real.sq_sqrt hv]

/-- **Sharp Gaussian concentration for a Lipschitz function of a Gaussian matrix, upper tail**:
`Pr(g ≥ E g + t) ≤ exp(−t²/(2·v·L²))`. -/
theorem gaussConc_mat_upper_sharp (hL0 : 0 ≤ L)
    (hL : ∀ M M' : Matrix (Fin m) (Fin k) ℝ,
      |g M - g M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2))
    {v : ℝ} (hv : 0 ≤ v) {t : ℝ} (ht : 0 ≤ t) :
    (gaussMat m k v).real {M | ∫ M, g M ∂gaussMat m k v + t ≤ g M} ≤
      Real.exp (-t ^ 2 / (2 * (v * L ^ 2))) := by
  have hLn : ∀ M M' : Matrix (Fin m) (Fin k) ℝ,
      |(fun M => -g M) M - (fun M => -g M) M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2) := by
    intro M M'
    have := hL M M'
    simp only
    rw [show -g M - -g M' = -(g M - g M') by ring, abs_neg]
    exact this
  have h := gaussConc_mat_lower_sharp hL0 hLn hv ht
  rw [integral_neg] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext M
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-- **The Gaussian Poincaré inequality for a Lipschitz function of a Gaussian matrix**:
`Var g ≤ v·L²`. -/
theorem gaussVar_mat_le_sharp (hL0 : 0 ≤ L)
    (hL : ∀ M M' : Matrix (Fin m) (Fin k) ℝ,
      |g M - g M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2))
    {v : ℝ} (hv : 0 ≤ v) :
    Integrable (fun M => (g M - ∫ M, g M ∂gaussMat m k v) ^ 2) (gaussMat m k v) ∧
    ∫ M, (g M - ∫ M, g M ∂gaussMat m k v) ^ 2 ∂gaussMat m k v ≤ v * L ^ 2 := by
  have hgc := BstLean.Part148.matLip_continuous hL
  set T : (Fin m × Fin k → ℝ) → Matrix (Fin m) (Fin k) ℝ :=
    fun ξ => Matrix.of fun i j => Real.sqrt v * ξ (i, j) with hT
  have mT : Measurable T := measurable_ofFlat _
  have hf : EuLip (fun ξ => g (T ξ)) (√v * L) := flat_euLip hL hv
  obtain ⟨hi, hvar⟩ := gaussVar_le_sharp (mul_nonneg (Real.sqrt_nonneg v) hL0) hf
  have eI : ∫ M, g M ∂gaussMat m k v = ∫ ξ, g (T ξ) ∂stdGauss (Fin m × Fin k) := by
    unfold gaussMat
    exact integral_map mT.aemeasurable hgc.measurable.aestronglyMeasurable
  have msq : Measurable fun M => (g M - ∫ M, g M ∂gaussMat m k v) ^ 2 :=
    (hgc.measurable.sub measurable_const).pow_const 2
  rw [← eI] at hi hvar
  constructor
  · exact (integrable_map_measure (μ := stdGauss (Fin m × Fin k)) (f := T)
      msq.aestronglyMeasurable mT.aemeasurable).mpr hi
  · have e2 : ∫ M, (g M - ∫ M, g M ∂gaussMat m k v) ^ 2 ∂gaussMat m k v =
        ∫ ξ, (g (T ξ) - ∫ M, g M ∂gaussMat m k v) ^ 2 ∂stdGauss (Fin m × Fin k) := by
      conv_lhs => unfold gaussMat
      exact integral_map mT.aemeasurable msq.aestronglyMeasurable
    rw [e2]
    refine hvar.trans (le_of_eq ?_)
    rw [mul_pow, Real.sq_sqrt hv]

end mat

end BstLean.Part152

open BstLean.Part152 in
#print axioms gaussConc_mgf_sharp
open BstLean.Part152 in
#print axioms gaussConc_lower_sharp
open BstLean.Part152 in
#print axioms gaussConc_upper_sharp
open BstLean.Part152 in
#print axioms gaussVar_le_sharp
open BstLean.Part152 in
#print axioms gaussConc_mat_lower_sharp
open BstLean.Part152 in
#print axioms gaussConc_mat_upper_sharp
open BstLean.Part152 in
#print axioms gaussVar_mat_le_sharp
