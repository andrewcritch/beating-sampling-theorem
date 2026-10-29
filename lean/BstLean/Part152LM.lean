import BstLean.Part152GC
import BstLean.Part148Tools

/-!
# Part 152 (LM): the Laurent–Massart tails of a chi-square variable, and the moment form of
the sharp Gaussian concentration

* `chiSq_upper_LM`: `Pr(Σ ξ_i² ≥ d + 2√(d x) + 2x) ≤ e^{−x}` for `x ≥ 0`, with `ξ` a standard
  Gaussian vector in dimension `d`.
* `chiSq_lower_LM`: `Pr(Σ ξ_i² ≤ d − 2√(d x)) ≤ e^{−x}` for `x ≥ 0` and `d ≥ 1`.
* `gaussConc_moment`: for `f` with Euclidean Lipschitz constant `L`,
  `E (f − E f)_+^{2p} ≤ L^{2p}·2^p·p!`.
-/

namespace BstLean.Part152

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Topology
open BstLean.Part29 (stdGauss)
open BstLean.Part148 (EuLip)

/-! ## The Laplace transform of the square of a standard Gaussian, on the positive side -/

/-- `∫ e^{t z²} dγ(z) = (1 − 2t)^{−1/2}` for `t < 1/2`. -/
lemma gauss_mgf_sq {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun z : ℝ => exp (t * z ^ 2)) (gaussianReal 0 1) ∧
    (∫ z : ℝ, exp (t * z ^ 2) ∂gaussianReal 0 1) = (Real.sqrt (1 - 2 * t))⁻¹ := by
  have hb : 0 < 1 / 2 - t := by linarith
  have he : (fun z : ℝ => gaussianPDFReal 0 1 z • exp (t * z ^ 2)) =
      fun z => (Real.sqrt (2 * π))⁻¹ * exp (-(1 / 2 - t) * z ^ 2) := by
    funext z
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul,
      mul_assoc, ← Real.exp_add]
    congr 2
    ring
  constructor
  · rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero),
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
        (ae_of_all _ fun _ => gaussianPDF_lt_top)]
    have e2 : (fun z : ℝ => (gaussianPDF 0 1 z).toReal • exp (t * z ^ 2)) =
        fun z => gaussianPDFReal 0 1 z • exp (t * z ^ 2) := by
      funext z
      rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
    rw [e2, he]
    exact (integrable_exp_neg_mul_sq hb).const_mul _
  · rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
    rw [he, integral_const_mul, integral_gaussian]
    have hp := Real.pi_pos
    have ht' : 0 < 1 - 2 * t := by linarith
    have hdiv : π / (1 / 2 - t) = (2 * π) / (1 - 2 * t) := by
      field_simp
    rw [hdiv, Real.sqrt_div (by positivity), div_eq_mul_inv]
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- `(1 − 2t)^{−1/2} ≤ exp(t + t²/(1 − 2t))` for `0 ≤ t < 1/2`. -/
lemma inv_sqrt_le_exp_pos {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1 / 2) :
    (Real.sqrt (1 - 2 * t))⁻¹ ≤ exp (t + t ^ 2 / (1 - 2 * t)) := by
  set w : ℝ := 1 - 2 * t with hw
  have hw0 : 0 < w := by rw [hw]; linarith
  have hw1 : w ≤ 1 := by rw [hw]; linarith
  have hv : 0 ≤ -Real.log w := by
    have := Real.log_nonpos hw0.le hw1
    linarith
  have hsinh := Real.self_le_sinh_iff.mpr hv
  rw [Real.sinh_eq, neg_neg, Real.exp_neg, Real.exp_log hw0] at hsinh
  have hsq : Real.sqrt w = exp (Real.log w / 2) := by
    rw [Real.exp_half, Real.exp_log hw0]
  rw [hsq, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have e : t + t ^ 2 / w = (w⁻¹ - w) / 4 := by
    have ht2 : t = (1 - w) / 2 := by rw [hw]; ring
    rw [ht2]
    field_simp
    ring
  rw [e]
  linarith

/-- The arithmetic of the Chernoff choice `t = b/(a + 2b)`. -/
lemma lm_arith {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    -(b / (a + 2 * b)) * (a ^ 2 + 2 * (a * b) + 2 * b ^ 2) +
      a ^ 2 * (b / (a + 2 * b) + (b / (a + 2 * b)) ^ 2 / (1 - 2 * (b / (a + 2 * b)))) =
      -b ^ 2 := by
  have hab : 0 < a + 2 * b := by positivity
  have h1 : 1 - 2 * (b / (a + 2 * b)) = a / (a + 2 * b) := by
    field_simp
    ring
  rw [h1]
  field_simp
  ring

/-! ## Laurent–Massart -/

/-- **Laurent–Massart, upper tail**: `Pr(Σ ξ_i² ≥ d + 2√(d x) + 2x) ≤ e^{−x}`. -/
theorem chiSq_upper_LM {ι : Type} [Fintype ι] {x : ℝ} (hx : 0 ≤ x) :
    (stdGauss ι).real {ξ | (Fintype.card ι : ℝ) + 2 * √((Fintype.card ι : ℝ) * x) + 2 * x ≤
      ∑ i, ξ i ^ 2} ≤ Real.exp (-x) := by
  rcases hx.eq_or_lt with hx0 | hxpos
  · rw [← hx0]
    simp only [neg_zero, Real.exp_zero]
    exact measureReal_le_one
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hset : {ξ : ι → ℝ | (Fintype.card ι : ℝ) + 2 * √((Fintype.card ι : ℝ) * x) + 2 * x ≤
        ∑ i, ξ i ^ 2} = ∅ := by
      ext ξ
      simp only [Fintype.card_eq_zero, Nat.cast_zero, zero_mul, Real.sqrt_zero, mul_zero,
        add_zero, zero_add, Finset.univ_eq_empty, Finset.sum_empty, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false, not_le]
      linarith
    rw [hset]
    simpa using (Real.exp_pos (-x)).le
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  have hdpos : 0 < d := by
    rw [hd]
    exact_mod_cast Fintype.card_pos
  set a : ℝ := √d with ha
  set b : ℝ := √x with hb
  have ha0 : 0 < a := Real.sqrt_pos.mpr hdpos
  have hb0 : 0 < b := Real.sqrt_pos.mpr hxpos
  have ha2 : a ^ 2 = d := Real.sq_sqrt hdpos.le
  have hb2 : b ^ 2 = x := Real.sq_sqrt hx
  have hab : √(d * x) = a * b := Real.sqrt_mul hdpos.le x
  set t : ℝ := b / (a + 2 * b) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t < 1 / 2 := by
    rw [ht, div_lt_iff₀ (by positivity)]
    linarith
  have hind : iIndepFun (fun (i : ι) (ξ : ι → ℝ) => ξ i ^ 2) (stdGauss ι) := by
    unfold stdGauss
    exact iIndepFun_pi (μ := fun _ : ι => gaussianReal 0 1)
      (X := fun _ => fun z : ℝ => z ^ 2) (fun _ => by fun_prop)
  have hm : ∀ i : ι, Measurable (fun ξ : ι → ℝ => ξ i ^ 2) := fun i => by fun_prop
  have hval : ∀ i : ι,
      Integrable (fun ξ : ι → ℝ => exp (t * ξ i ^ 2)) (stdGauss ι) ∧
      ∫ ξ : ι → ℝ, exp (t * ξ i ^ 2) ∂stdGauss ι = (Real.sqrt (1 - 2 * t))⁻¹ := by
    intro i
    obtain ⟨hI, hE⟩ := gauss_mgf_sq ht1
    have e : (fun ξ : ι → ℝ => exp (t * ξ i ^ 2)) =
        fun ξ => (fun z : ℝ => exp (t * z ^ 2)) (ξ i) := rfl
    rw [e]
    unfold stdGauss
    refine ⟨integrable_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := i) hI, ?_⟩
    rw [integral_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := i)
      hI.aestronglyMeasurable, hE]
  have hI : Integrable (fun ξ => exp (t * (∑ i, fun ξ : ι → ℝ => ξ i ^ 2) ξ)) (stdGauss ι) :=
    hind.integrable_exp_mul_sum hm (s := Finset.univ) fun i _ => (hval i).1
  have h := measure_ge_le_exp_mul_mgf (μ := stdGauss ι)
    (X := ∑ i, fun ξ : ι → ℝ => ξ i ^ 2) (t := t) (d + 2 * √(d * x) + 2 * x) ht0 hI
  have hset : {ξ : ι → ℝ | d + 2 * √(d * x) + 2 * x ≤ (∑ i, fun ξ : ι → ℝ => ξ i ^ 2) ξ} =
      {ξ | d + 2 * √(d * x) + 2 * x ≤ ∑ i, ξ i ^ 2} := by
    ext ξ; simp
  rw [hset] at h
  refine h.trans ?_
  rw [hind.mgf_sum hm Finset.univ]
  have hprod : ∏ i, mgf (fun ξ : ι → ℝ => ξ i ^ 2) (stdGauss ι) t ≤
      ∏ _i : ι, exp (t + t ^ 2 / (1 - 2 * t)) :=
    Finset.prod_le_prod₀ (fun i _ => mgf_nonneg) fun i _ => by
      unfold mgf
      rw [(hval i).2]
      exact inv_sqrt_le_exp_pos ht0 ht1
  have hexp : ∏ _i : ι, exp (t + t ^ 2 / (1 - 2 * t)) =
      exp (d * (t + t ^ 2 / (1 - 2 * t))) := by
    rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
  calc exp (-t * (d + 2 * √(d * x) + 2 * x)) *
        ∏ i, mgf (fun ξ : ι → ℝ => ξ i ^ 2) (stdGauss ι) t
      ≤ exp (-t * (d + 2 * √(d * x) + 2 * x)) * exp (d * (t + t ^ 2 / (1 - 2 * t))) := by
        rw [← hexp]
        exact mul_le_mul_of_nonneg_left hprod (exp_pos _).le
    _ = exp (-x) := by
        rw [← Real.exp_add]
        congr 1
        rw [hab, ← ha2, ← hb2, ht]
        exact lm_arith ha0 hb0

/-- **Laurent–Massart, lower tail**: `Pr(Σ ξ_i² ≤ d − 2√(d x)) ≤ e^{−x}`. -/
theorem chiSq_lower_LM {ι : Type} [Fintype ι] [Nonempty ι] {x : ℝ} (hx : 0 ≤ x) :
    (stdGauss ι).real {ξ | ∑ i, ξ i ^ 2 ≤
      (Fintype.card ι : ℝ) - 2 * √((Fintype.card ι : ℝ) * x)} ≤ Real.exp (-x) := by
  have hdpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := BstLean.Part148.chiSqLower (ι := ι) (lam := fun _ => (1 : ℝ))
    (fun _ => zero_le_one) (B := (Fintype.card ι : ℝ)) (by simp)
    (t := 2 * √((Fintype.card ι : ℝ) * x)) (by positivity)
  simp only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  field_simp
  ring

/-! ## The moment form of the sharp Gaussian concentration -/

section Moment

variable {ι : Type} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ} {L : ℝ}

/-- `∫_0^∞ e^{−u²/(2L²)}·(2q+2)·u^{2q+1} du = L^{2(q+1)}·2^{q+1}·(q+1)!`, with integrability. -/
lemma gauss_moment_integral (hL : 0 < L) (q : ℕ) :
    IntegrableOn (fun u : ℝ => exp (-u ^ 2 / (2 * L ^ 2)) * ((2 * (q : ℝ) + 2) * u ^ (2 * q + 1)))
      (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), exp (-u ^ 2 / (2 * L ^ 2)) * ((2 * (q : ℝ) + 2) * u ^ (2 * q + 1)) =
      L ^ (2 * (q + 1)) * (2 ^ (q + 1) * ((q + 1).factorial : ℝ)) := by
  set b : ℝ := (2 * L ^ 2)⁻¹ with hb
  have hb0 : 0 < b := by positivity
  set s : ℝ := ((2 * q + 1 : ℕ) : ℝ) with hs
  have hs0 : (-1 : ℝ) < s := by
    have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    linarith
  have hpt : ∀ u ∈ Ioi (0 : ℝ),
      (2 * (q : ℝ) + 2) * (u ^ s * exp (-b * u ^ (2 : ℝ))) =
        exp (-u ^ 2 / (2 * L ^ 2)) * ((2 * (q : ℝ) + 2) * u ^ (2 * q + 1)) := by
    intro u _
    have e1 : u ^ s = u ^ (2 * q + 1) := by rw [hs, Real.rpow_natCast]
    have e2 : -b * u ^ (2 : ℝ) = -u ^ 2 / (2 * L ^ 2) := by
      rw [Real.rpow_two, hb]
      field_simp
    rw [e1, e2]
    ring
  constructor
  · have h1 : IntegrableOn (fun u : ℝ => u ^ s * exp (-b * u ^ (2 : ℝ))) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow hs0 two_pos hb0
    have h2 : IntegrableOn (fun u : ℝ => (2 * (q : ℝ) + 2) * (u ^ s * exp (-b * u ^ (2 : ℝ))))
        (Ioi 0) := h1.const_mul (2 * (q : ℝ) + 2)
    exact IntegrableOn.congr_fun h2 hpt measurableSet_Ioi
  · rw [← setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
      integral_rpow_mul_exp_neg_mul_rpow two_pos hs0 hb0]
    have hs1 : (s + 1) / 2 = (q : ℝ) + 1 := by
      rw [hs]; push_cast; ring
    have hs2 : -(s + 1) / 2 = -(((q + 1 : ℕ)) : ℝ) := by
      rw [hs]; push_cast; ring
    rw [hs1, hs2, Real.Gamma_nat_eq_factorial, Real.rpow_neg hb0.le, Real.rpow_natCast, hb,
      inv_pow, inv_inv, Nat.factorial_succ]
    push_cast
    ring

/-- The `lintegral` form of the moment bound, for `L > 0` and the exponent `2(q+1)`. -/
lemma gaussConc_moment_lintegral (hLpos : 0 < L) (hL : EuLip f L) (q : ℕ) :
    ∫⁻ x, ENNReal.ofReal ((max (f x - ∫ y, f y ∂stdGauss ι) 0) ^ (2 * (q + 1))) ∂stdGauss ι ≤
      ENNReal.ofReal (L ^ (2 * (q + 1)) * (2 ^ (q + 1) * ((q + 1).factorial : ℝ))) := by
  set m : ℝ := ∫ y, f y ∂stdGauss ι with hm
  have hfm : Measurable f := (hL.continuous hLpos.le).measurable
  set h : (ι → ℝ) → ℝ := fun x => max (f x - m) 0 with hh
  set g : ℝ → ℝ := fun u => (2 * (q : ℝ) + 2) * u ^ (2 * q + 1) with hg
  have hgc : Continuous g := by fun_prop
  have hgnn : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ g u := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu => ?_)
    have hu' : 0 < u := hu
    simp only [hg]
    positivity
  have key := lintegral_comp_eq_lintegral_meas_le_mul (stdGauss ι) (f := h) (g := g)
    (ae_of_all _ fun x => le_max_right _ _) (by fun_prop)
    (fun u _ => hgc.intervalIntegrable _ _) hgnn
  have hint : ∀ a : ℝ, ∫ u in (0 : ℝ)..a, g u = a ^ (2 * (q + 1)) := by
    intro a
    simp only [hg]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have e : ((2 * q + 1 : ℕ) : ℝ) + 1 = 2 * (q : ℝ) + 2 := by push_cast; ring
    have hne : (2 * (q : ℝ) + 2) ≠ 0 := by positivity
    rw [e, zero_pow (by omega), sub_zero, mul_div_cancel₀ _ hne]
    congr 1
  simp only [hint] at key
  rw [key]
  obtain ⟨hI, hE⟩ := gauss_moment_integral hLpos q
  have hF0 : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun u : ℝ => exp (-u ^ 2 / (2 * L ^ 2)) * ((2 * (q : ℝ) + 2) * u ^ (2 * q + 1)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu => ?_)
    have hu' : 0 < u := hu
    simp only [Pi.zero_apply]
    positivity
  rw [← hE, ofReal_integral_eq_lintegral_ofReal hI hF0]
  refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu => ?_))
  have hu' : 0 < u := hu
  have hset : {a : ι → ℝ | u ≤ h a} = {a | m + u ≤ f a} := by
    ext a
    simp only [hh, Set.mem_ofPred_eq, le_max_iff]
    constructor
    · rintro (h1 | h1)
      · linarith
      · linarith
    · intro h1
      left
      linarith
  rw [hset, ENNReal.ofReal_mul (exp_pos _).le]
  gcongr
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (gaussConc_upper_sharp hLpos.le hL hu'.le)

/-- **The moment form of the sharp Gaussian concentration**: for `f` with Euclidean Lipschitz
constant `L` and every natural number `p`, `E (f − E f)_+^{2p} ≤ L^{2p}·2^p·p!`. -/
theorem gaussConc_moment (hL0 : 0 ≤ L) (hL : EuLip f L) (p : ℕ) :
    Integrable (fun x => (max (f x - ∫ y, f y ∂stdGauss ι) 0) ^ (2 * p)) (stdGauss ι) ∧
    ∫ x, (max (f x - ∫ y, f y ∂stdGauss ι) 0) ^ (2 * p) ∂stdGauss ι ≤
      L ^ (2 * p) * (2 ^ p * (p.factorial : ℝ)) := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    simp
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rcases hL0.eq_or_lt with h0 | hLpos
  · have hc : ∀ x, f x = f 0 := by
      intro x
      have := hL x 0
      rw [← h0, zero_mul] at this
      have h2 := abs_nonneg (f x - f 0)
      have h3 : |f x - f 0| = 0 := le_antisymm this h2
      have := abs_eq_zero.mp h3
      linarith
    have hm : ∫ y, f y ∂stdGauss ι = f 0 := by
      have e : f = fun _ => f 0 := funext hc
      rw [e]
      simp
    have e : (fun x => (max (f x - ∫ y, f y ∂stdGauss ι) 0) ^ (2 * (q + 1))) = fun _ => 0 := by
      funext x
      rw [hm, hc x]
      simp
    rw [e]
    refine ⟨integrable_const _, ?_⟩
    simp only [integral_zero]
    positivity
  have hb := gaussConc_moment_lintegral hLpos hL q
  have hfc : Continuous f := hL.continuous hL0
  have hnn : ∀ x, 0 ≤ (max (f x - ∫ y, f y ∂stdGauss ι) 0) ^ (2 * (q + 1)) := fun x => by
    positivity
  have hsm : AEStronglyMeasurable
      (fun x => (max (f x - ∫ y, f y ∂stdGauss ι) 0) ^ (2 * (q + 1))) (stdGauss ι) := by
    have : Continuous (fun x => (max (f x - ∫ y, f y ∂stdGauss ι) 0) ^ (2 * (q + 1))) := by
      fun_prop
    exact this.aestronglyMeasurable
  refine ⟨⟨hsm, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)).2
    (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hsm]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hb

end Moment

end BstLean.Part152

open BstLean.Part152 in
#print axioms chiSq_upper_LM
open BstLean.Part152 in
#print axioms chiSq_lower_LM
open BstLean.Part152 in
#print axioms gaussConc_moment
