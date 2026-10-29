import BstLean.Part144Num2
import BstLean.Part144Block3

/-!
# Part 146 (file `Tail`): `Pr(|ξ| ≥ t) ≤ c₀/t²` for a standard Gaussian, with `c₀ < 1`

Role: `delegations/statements/p146-spec.md`, item 1 (a Markov-type inequality with a constant
below `1` for a centred Gaussian variable). `φ = gaussianPDFReal 0 1`,
`Φ̄(t) = (gaussianReal 0 1).real (Ioi t)`.

* `mills9_upper`: `Φ̄(t) ≤ φ(t)·N(t)/D(t)` for `t > 0`, with
  `N = t⁸ + 35t⁶ + 345t⁴ + 975t² + 384`, `D = t⁹ + 36t⁷ + 378t⁵ + 1260t³ + 945t` (a convergent
  of the continued fraction of the Mills ratio; `t·R − R′ − 1 = 362880/D²`).
* `two_sided_le`: `Pr(|ξ| ≥ t) ≤ 2Φ̄(t)`.
* **`tail2_le`**: `Pr(|ξ| ≥ t) ≤ cTail/t²` for every `t > 0`. The true supremum of
  `2t²Φ̄(t)` is `0.33114…`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part146
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open BstLean.Part131 BstLean.Part144

/-- The numerator of the convergent. -/
noncomputable def nP (x : ℝ) : ℝ := x ^ 8 + 35 * x ^ 6 + 345 * x ^ 4 + 975 * x ^ 2 + 384

/-- The denominator of the convergent, divided by `x`. -/
noncomputable def eP (x : ℝ) : ℝ := x ^ 8 + 36 * x ^ 6 + 378 * x ^ 4 + 1260 * x ^ 2 + 945

lemma nP_pos (x : ℝ) : 0 < nP x := by unfold nP; positivity
lemma eP_pos (x : ℝ) : 0 < eP x := by unfold eP; positivity

lemma nP_le_eP (x : ℝ) : nP x ≤ eP x := by
  unfold nP eP
  have h6 : 0 ≤ x ^ 6 := by positivity
  have h4 : 0 ≤ x ^ 4 := by positivity
  have h2 : 0 ≤ x ^ 2 := by positivity
  linarith

lemma nP_hasDerivAt (x : ℝ) :
    HasDerivAt nP (8 * x ^ 7 + 210 * x ^ 5 + 1380 * x ^ 3 + 1950 * x) x := by
  have h := ((((hasDerivAt_pow 8 x).add ((hasDerivAt_pow 6 x).const_mul 35)).add
    ((hasDerivAt_pow 4 x).const_mul 345)).add ((hasDerivAt_pow 2 x).const_mul 975)).add_const 384
  convert h using 1
  · funext y; simp only [nP, Pi.add_apply]
  · norm_num; ring

lemma dP_hasDerivAt (x : ℝ) :
    HasDerivAt (fun x : ℝ => x * eP x)
      (9 * x ^ 8 + 252 * x ^ 6 + 1890 * x ^ 4 + 3780 * x ^ 2 + 945) x := by
  have h := ((((hasDerivAt_pow 9 x).add ((hasDerivAt_pow 7 x).const_mul 36)).add
    ((hasDerivAt_pow 5 x).const_mul 378)).add ((hasDerivAt_pow 3 x).const_mul 1260)).add
    ((hasDerivAt_id x).const_mul 945)
  have e : (fun x : ℝ => x * eP x) =
      ((((fun x : ℝ => x ^ 9) + fun x => 36 * x ^ 7) + fun x => 378 * x ^ 5) +
        fun x => 1260 * x ^ 3) + fun x => 945 * id x := by
    funext y; simp only [eP, Pi.add_apply, id]; ring
  rw [e]
  convert h using 1
  norm_num
  ring

/-- **A Mills upper bound from the continued fraction**:
`Φ̄(t) ≤ φ(t)·N(t)/(t·E(t))` for `t > 0`. -/
theorem mills9_upper {t : ℝ} (ht : 0 < t) :
    (gaussianReal 0 1).real (Ioi t) ≤ gaussianPDFReal 0 1 t * (nP t / (t * eP t)) := by
  have hint := integrable_gaussianPDFReal 0 1
  rw [gauss_real_eq]
  let f : ℝ → ℝ := fun x => -(gaussianPDFReal 0 1 x * (nP x / (x * eP x)))
  let f' : ℝ → ℝ := fun x => gaussianPDFReal 0 1 x * (1 + 362880 / (x * eP x) ^ 2)
  have hderiv : ∀ x ∈ Ici t, HasDerivAt f (f' x) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ht hx
    have hd0 : x * eP x ≠ 0 := (mul_pos hx0 (eP_pos x)).ne'
    have h3 := ((pdf_hasDerivAt x).mul ((nP_hasDerivAt x).div (dP_hasDerivAt x) hd0)).neg
    have e4 : f' x = -(gaussianPDFReal 0 1 x * -x * (nP x / (x * eP x)) +
        gaussianPDFReal 0 1 x * (((8 * x ^ 7 + 210 * x ^ 5 + 1380 * x ^ 3 + 1950 * x) *
          (x * eP x) - nP x * (9 * x ^ 8 + 252 * x ^ 6 + 1890 * x ^ 4 + 3780 * x ^ 2 + 945)) /
            (x * eP x) ^ 2)) := by
      have he := (eP_pos x).ne'
      have hx' := hx0.ne'
      simp only [f']
      field_simp
      unfold nP eP
      ring
    rw [e4]; exact h3
  have hbd0 : ∀ x : ℝ, 0 ≤ 362880 / (x * eP x) ^ 2 := fun x => by positivity
  have hbd2 : ∀ x : ℝ, t < x → 362880 / (x * eP x) ^ 2 ≤ 362880 / (t * 945) ^ 2 := by
    intro x hx
    have hx0 : 0 < x := ht.trans hx
    have h1 : (945 : ℝ) ≤ eP x := by
      unfold eP
      have h8 : 0 ≤ x ^ 8 := by positivity
      have h6 : 0 ≤ x ^ 6 := by positivity
      have h4 : 0 ≤ x ^ 4 := by positivity
      have h2 : 0 ≤ x ^ 2 := by positivity
      linarith
    have h2 : t * 945 ≤ x * eP x := mul_le_mul hx.le h1 (by norm_num) hx0.le
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ (by positivity) h2 2)
  have hmeas : Measurable fun x : ℝ => 1 + 362880 / (x * eP x) ^ 2 := by
    unfold eP; fun_prop
  have hf'int : IntegrableOn f' (Ioi t) := by
    refine Integrable.mono' (hint.const_mul (1 + 362880 / (t * 945) ^ 2)).integrableOn
      ((hint.aestronglyMeasurable.mul hmeas.aestronglyMeasurable).restrict) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    have hp := gaussianPDFReal_nonneg 0 1 x
    have h1 := hbd0 x
    have h2 := hbd2 x hx
    simp only [f', Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg hp (by linarith)), mul_comm]
    exact mul_le_mul_of_nonneg_right (by linarith) hp
  have htend : Tendsto f atTop (𝓝 0) := by
    have hb : ∀ᶠ x : ℝ in atTop, ‖f x‖ ≤ phi1 * Real.exp (1 / 2) * x⁻¹ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hr0 : 0 ≤ nP x / (x * eP x) :=
        div_nonneg (nP_pos x).le (mul_pos hx (eP_pos x)).le
      have hr : nP x / (x * eP x) ≤ x⁻¹ := by
        rw [div_le_iff₀ (mul_pos hx (eP_pos x)), ← mul_assoc, inv_mul_cancel₀ hx.ne', one_mul]
        exact nP_le_eP x
      simp only [f, norm_neg, Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) hr0), pdf_eq_phi1]
      have : Real.exp ((1 - x ^ 2) / 2) ≤ Real.exp (1 / 2) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
      have h2 := phi1_pos
      gcongr
    have h0 : Tendsto (fun x : ℝ => phi1 * Real.exp (1 / 2) * x⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (phi1 * Real.exp (1 / 2))
    exact squeeze_zero_norm' hb h0
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hf'int htend
  have hle : ∫ x in Ioi t, gaussianPDFReal 0 1 x ≤ ∫ x in Ioi t, f' x := by
    refine setIntegral_mono_on hint.integrableOn hf'int measurableSet_Ioi ?_
    intro x _
    have hp := gaussianPDFReal_nonneg 0 1 x
    have h1 := hbd0 x
    simp only [f']
    nlinarith
  rw [hI] at hle
  have hft : f t = -(gaussianPDFReal 0 1 t * (nP t / (t * eP t))) := rfl
  rw [hft, zero_sub, neg_neg] at hle
  exact hle

/-- `Pr(|ξ| ≥ t) ≤ 2Φ̄(t)`. -/
theorem two_sided_le (t : ℝ) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ 2 * (gaussianReal 0 1).real (Ioi t) := by
  have hsub : {x : ℝ | t ≤ |x|} ⊆ Ici t ∪ Iic (-t) := by
    intro x hx
    rcases le_abs'.mp (show t ≤ |x| from hx) with h | h
    · exact Or.inr h
    · exact Or.inl h
  have h1 : (gaussianReal 0 1).real (Ici t) = (gaussianReal 0 1).real (Ioi t) := by
    rw [gauss_real_eq, gauss_real_eq, integral_Ici_eq_integral_Ioi]
  have h2 : (gaussianReal 0 1).real (Iic (-t)) = (gaussianReal 0 1).real (Ioi t) := by
    rw [← tail_neg t, gauss_real_eq, gauss_real_eq, integral_Iic_eq_integral_Iio]
  calc (gaussianReal 0 1).real {x | t ≤ |x|}
      ≤ (gaussianReal 0 1).real (Ici t ∪ Iic (-t)) := measureReal_mono hsub
    _ ≤ (gaussianReal 0 1).real (Ici t) + (gaussianReal 0 1).real (Iic (-t)) :=
        measureReal_union_le _ _
    _ = 2 * (gaussianReal 0 1).real (Ioi t) := by rw [h1, h2]; ring

/-- The polynomial lower bound of `exp(t²/2 − 11/16)`. -/
noncomputable def bP (x : ℝ) : ℝ := (1 + (x ^ 2 / 2 - 11 / 16) / 8) ^ 8

lemma bP_base (x : ℝ) : 0 < 1 + (x ^ 2 / 2 - 11 / 16) / 8 := by nlinarith [sq_nonneg x]

lemma bP_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : bP x ≤ bP y := by
  unfold bP
  refine pow_le_pow_left₀ (bP_base x).le ?_ 8
  have : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx hxy 2
  linarith

lemma eP_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : eP x ≤ eP y := by
  unfold eP
  have h8 := pow_le_pow_left₀ hx hxy 8
  have h6 := pow_le_pow_left₀ hx hxy 6
  have h4 := pow_le_pow_left₀ hx hxy 4
  have h2 := pow_le_pow_left₀ hx hxy 2
  linarith

lemma nP_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : nP x ≤ nP y := by
  unfold nP
  have h8 := pow_le_pow_left₀ hx hxy 8
  have h6 := pow_le_pow_left₀ hx hxy 6
  have h4 := pow_le_pow_left₀ hx hxy 4
  have h2 := pow_le_pow_left₀ hx hxy 2
  linarith

/-- `1.98873 ≤ exp(11/16)`. -/
lemma exp_1116 : (198873 : ℝ) / 100000 ≤ Real.exp (11 / 16) := by
  have h1 := Real.exp_one_gt_d9
  have hp : 0 < Real.exp (11 / 16) := Real.exp_pos _
  have h16 : Real.exp (11 / 16) ^ 16 = Real.exp 1 ^ 11 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  by_contra hcon
  have hlt : Real.exp (11 / 16) < 198873 / 100000 := not_le.mp hcon
  have h9 : Real.exp (11 / 16) ^ 16 < (198873 / 100000 : ℝ) ^ 16 :=
    pow_lt_pow_left₀ hlt hp.le (by norm_num)
  rw [h16] at h9
  have h2 : (2.7182818283 : ℝ) ^ 11 < Real.exp 1 ^ 11 :=
    pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  norm_num at h9 h2
  linarith

/-- `φ(t)·(√(2π)·e^{11/16}·b(t)) ≤ 1`. -/
lemma pdf_bP (t : ℝ) :
    gaussianPDFReal 0 1 t * (2506627 / 1000000 * (198873 / 100000) * bP t) ≤ 1 := by
  rw [pdf_eq]
  have hs := sqrt_two_pi_bounds.1
  have hs0 : (0 : ℝ) < √(2 * Real.pi) := by positivity
  have hL := exp_1116
  have hb : bP t ≤ Real.exp (t ^ 2 / 2 - 11 / 16) := by
    unfold bP
    have h1 : 1 + (t ^ 2 / 2 - 11 / 16) / 8 ≤ Real.exp ((t ^ 2 / 2 - 11 / 16) / 8) := by
      have := Real.add_one_le_exp ((t ^ 2 / 2 - 11 / 16) / 8)
      linarith
    have h2 := pow_le_pow_left₀ (bP_base t).le h1 8
    rw [← Real.exp_nat_mul] at h2
    refine h2.trans (le_of_eq ?_)
    congr 1; ring
  have hb0 : 0 ≤ bP t := by unfold bP; positivity
  have h3 : (198873 / 100000 : ℝ) * bP t ≤ Real.exp (t ^ 2 / 2) := by
    have e : Real.exp (t ^ 2 / 2) = Real.exp (11 / 16) * Real.exp (t ^ 2 / 2 - 11 / 16) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    exact mul_le_mul hL hb hb0 (Real.exp_pos _).le
  have h4 : (2506627 / 1000000 : ℝ) * (198873 / 100000) * bP t ≤
      √(2 * Real.pi) * Real.exp (t ^ 2 / 2) := by
    rw [mul_assoc]
    exact mul_le_mul hs h3 (by positivity) hs0.le
  have h5 : (√(2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2 / 2)) *
      (√(2 * Real.pi) * Real.exp (t ^ 2 / 2)) = 1 := by
    rw [Real.exp_neg]
    have := (Real.exp_pos (t ^ 2 / 2)).ne'
    field_simp
  rw [← h5]
  exact mul_le_mul_of_nonneg_left h4 (by positivity)

/-- **One piece.** For `0 ≤ t1 ≤ t ≤ t2`, `t > 0`: if
`2·N(t2)·t2 ≤ c·(√(2π)·e^{11/16})·b(t1)·E(t1)` at the rational bounds, then
`Pr(|ξ| ≥ t) ≤ c/t²`. -/
lemma piece {c t1 t2 t : ℝ} (hc : 0 ≤ c) (h1 : 0 ≤ t1) (ht1 : t1 ≤ t) (ht2 : t ≤ t2) (ht : 0 < t)
    (hnum : 2 * nP t2 * t2 ≤ c * (2506627 / 1000000 * (198873 / 100000)) * (bP t1 * eP t1)) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ c / t ^ 2 := by
  have hm := mills9_upper ht
  have h2 := two_sided_le t
  have hp := pdf_bP t
  have hpdf := gaussianPDFReal_nonneg 0 1 t
  have hE := eP_pos t
  have hN := nP_pos t
  have hb0 : 0 < bP t := by unfold bP; exact pow_pos (bP_base t) 8
  set K : ℝ := 2506627 / 1000000 * (198873 / 100000) with hK
  have hK0 : 0 < K := by rw [hK]; norm_num
  -- the polynomial inequality at `t`
  have hpoly : 2 * nP t * t ≤ c * K * (bP t * eP t) := by
    have a1 : 2 * nP t * t ≤ 2 * nP t2 * t2 :=
      mul_le_mul (by have := nP_mono ht.le ht2; linarith) ht2 ht.le
        (by have := nP_pos t2; linarith)
    have a2 : bP t1 * eP t1 ≤ bP t * eP t :=
      mul_le_mul (bP_mono h1 ht1) (eP_mono h1 ht1) (eP_pos t1).le hb0.le
    have a3 : c * K * (bP t1 * eP t1) ≤ c * K * (bP t * eP t) :=
      mul_le_mul_of_nonneg_left a2 (by positivity)
    linarith
  -- `φ(t) ≤ 1/(K·b(t))`
  have hphi : gaussianPDFReal 0 1 t ≤ 1 / (K * bP t) := by
    rw [le_div_iff₀ (by positivity)]
    exact hp
  have hfin : 2 * (gaussianPDFReal 0 1 t * (nP t / (t * eP t))) ≤ c / t ^ 2 := by
    have h3 : 2 * (gaussianPDFReal 0 1 t * (nP t / (t * eP t))) ≤
        2 * (1 / (K * bP t) * (nP t / (t * eP t))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hphi (by positivity)) (by norm_num)
    refine h3.trans ?_
    rw [div_mul_div_comm, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : 2 * (1 * nP t) * t ^ 2 = (2 * nP t * t) * t := by ring
    have e2 : c * (K * bP t * (t * eP t)) = (c * K * (bP t * eP t)) * t := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hpoly ht.le
  linarith

/-- The constant of `tail2_le`. -/
noncomputable def cTail : ℝ := 669 / 2000

lemma cTail_pos : 0 < cTail := by unfold cTail; norm_num
lemma cTail_le : cTail ≤ 3345 / 10000 := by unfold cTail; norm_num

/-- A zone of the grid: `t ∈ (lo/M, hi/M]`, pieces of width `1/M`. -/
lemma zone {M lo hi : ℕ} (hM : 0 < M)
    (hall : ∀ j : ℕ, lo ≤ j → j < hi →
      2 * nP (((j : ℝ) + 1) / M) * (((j : ℝ) + 1) / M) ≤
        cTail * (2506627 / 1000000 * (198873 / 100000)) *
          (bP ((j : ℝ) / M) * eP ((j : ℝ) / M)))
    {t : ℝ} (ht : 0 < t) (hlo : (lo : ℝ) / M ≤ t) (hhi : t < (hi : ℝ) / M) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have htM : 0 ≤ t * M := by positivity
  set j : ℕ := ⌊t * M⌋₊ with hj
  have hj1 : (j : ℝ) ≤ t * M := Nat.floor_le htM
  have hj2 : t * M < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlo' : lo ≤ j := by
    rw [hj]; apply Nat.le_floor
    rw [div_le_iff₀ hM0] at hlo; exact hlo
  have hhi' : j < hi := by
    have : (j : ℝ) < hi := by
      rw [lt_div_iff₀ hM0] at hhi; linarith
    exact_mod_cast this
  refine piece cTail_pos.le (t1 := (j : ℝ) / M) (t2 := ((j : ℝ) + 1) / M) (by positivity) ?_ ?_ ht
    (hall j hlo' hhi')
  · rw [div_le_iff₀ hM0]; exact hj1
  · rw [le_div_iff₀ hM0]; exact hj2.le

/-- Large `t`: `t ≥ 17/8`. -/
lemma tail_large {t : ℝ} (ht : 17 / 8 ≤ t) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  refine piece cTail_pos.le ht0.le le_rfl le_rfl ht0 ?_
  have hb : 1 + (t ^ 2 / 2 - 11 / 16) ≤ bP t := by
    unfold bP
    have h := one_add_mul_le_pow (a := (t ^ 2 / 2 - 11 / 16) / 8)
      (by have := bP_base t; linarith) 8
    norm_num at h ⊢
    linarith
  have hE := eP_pos t
  have hNE := nP_le_eP t
  have h1 : 2 * t ≤ cTail * (2506627 / 1000000 * (198873 / 100000)) * bP t := by
    have h2 : 2 * t ≤ cTail * (2506627 / 1000000 * (198873 / 100000)) *
        (1 + (t ^ 2 / 2 - 11 / 16)) := by
      unfold cTail
      nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr ht)]
    refine h2.trans (mul_le_mul_of_nonneg_left hb ?_)
    unfold cTail; norm_num
  calc 2 * nP t * t = (2 * t) * nP t := by ring
    _ ≤ (2 * t) * eP t := mul_le_mul_of_nonneg_left hNE (by linarith)
    _ ≤ (cTail * (2506627 / 1000000 * (198873 / 100000)) * bP t) * eP t :=
        mul_le_mul_of_nonneg_right h1 hE.le
    _ = _ := by ring

lemma zc0 {t : ℝ} (ht : 0 < t) (hlo : (0 : ℝ) / 16 ≤ t) (hhi : t < (12 : ℝ) / 16) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 16) (lo := 0) (hi := 12) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc1 {t : ℝ} (ht : 0 < t) (hlo : (96 : ℝ) / 128 ≤ t) (hhi : t < (112 : ℝ) / 128) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 128) (lo := 96) (hi := 112) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc2 {t : ℝ} (ht : 0 < t) (hlo : (112 : ℝ) / 128 ≤ t) (hhi : t < (128 : ℝ) / 128) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 128) (lo := 112) (hi := 128) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc3 {t : ℝ} (ht : 0 < t) (hlo : (1024 : ℝ) / 1024 ≤ t) (hhi : t < (1040 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1024) (hi := 1040) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc4 {t : ℝ} (ht : 0 < t) (hlo : (1040 : ℝ) / 1024 ≤ t) (hhi : t < (1056 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1040) (hi := 1056) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc5 {t : ℝ} (ht : 0 < t) (hlo : (1056 : ℝ) / 1024 ≤ t) (hhi : t < (1072 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1056) (hi := 1072) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc6 {t : ℝ} (ht : 0 < t) (hlo : (1072 : ℝ) / 1024 ≤ t) (hhi : t < (1088 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1072) (hi := 1088) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc7 {t : ℝ} (ht : 0 < t) (hlo : (1088 : ℝ) / 1024 ≤ t) (hhi : t < (1104 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1088) (hi := 1104) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc8 {t : ℝ} (ht : 0 < t) (hlo : (1104 : ℝ) / 1024 ≤ t) (hhi : t < (1120 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1104) (hi := 1120) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc9 {t : ℝ} (ht : 0 < t) (hlo : (1120 : ℝ) / 1024 ≤ t) (hhi : t < (1136 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1120) (hi := 1136) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc10 {t : ℝ} (ht : 0 < t) (hlo : (1136 : ℝ) / 1024 ≤ t) (hhi : t < (1152 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1136) (hi := 1152) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc11 {t : ℝ} (ht : 0 < t) (hlo : (1152 : ℝ) / 1024 ≤ t) (hhi : t < (1168 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1152) (hi := 1168) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc12 {t : ℝ} (ht : 0 < t) (hlo : (1168 : ℝ) / 1024 ≤ t) (hhi : t < (1184 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1168) (hi := 1184) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc13 {t : ℝ} (ht : 0 < t) (hlo : (1184 : ℝ) / 1024 ≤ t) (hhi : t < (1200 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1184) (hi := 1200) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc14 {t : ℝ} (ht : 0 < t) (hlo : (1200 : ℝ) / 1024 ≤ t) (hhi : t < (1216 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1200) (hi := 1216) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc15 {t : ℝ} (ht : 0 < t) (hlo : (1216 : ℝ) / 1024 ≤ t) (hhi : t < (1232 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1216) (hi := 1232) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc16 {t : ℝ} (ht : 0 < t) (hlo : (1232 : ℝ) / 1024 ≤ t) (hhi : t < (1248 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1232) (hi := 1248) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc17 {t : ℝ} (ht : 0 < t) (hlo : (1248 : ℝ) / 1024 ≤ t) (hhi : t < (1264 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1248) (hi := 1264) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc18 {t : ℝ} (ht : 0 < t) (hlo : (1264 : ℝ) / 1024 ≤ t) (hhi : t < (1280 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1264) (hi := 1280) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc19 {t : ℝ} (ht : 0 < t) (hlo : (1280 : ℝ) / 1024 ≤ t) (hhi : t < (1296 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1280) (hi := 1296) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc20 {t : ℝ} (ht : 0 < t) (hlo : (1296 : ℝ) / 1024 ≤ t) (hhi : t < (1312 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1296) (hi := 1312) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc21 {t : ℝ} (ht : 0 < t) (hlo : (1312 : ℝ) / 1024 ≤ t) (hhi : t < (1328 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1312) (hi := 1328) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc22 {t : ℝ} (ht : 0 < t) (hlo : (1328 : ℝ) / 1024 ≤ t) (hhi : t < (1344 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1328) (hi := 1344) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc23 {t : ℝ} (ht : 0 < t) (hlo : (1344 : ℝ) / 1024 ≤ t) (hhi : t < (1360 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1344) (hi := 1360) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc24 {t : ℝ} (ht : 0 < t) (hlo : (1360 : ℝ) / 1024 ≤ t) (hhi : t < (1376 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1360) (hi := 1376) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc25 {t : ℝ} (ht : 0 < t) (hlo : (1376 : ℝ) / 1024 ≤ t) (hhi : t < (1392 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1376) (hi := 1392) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc26 {t : ℝ} (ht : 0 < t) (hlo : (1392 : ℝ) / 1024 ≤ t) (hhi : t < (1408 : ℝ) / 1024) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 1024) (lo := 1392) (hi := 1408) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc27 {t : ℝ} (ht : 0 < t) (hlo : (176 : ℝ) / 128 ≤ t) (hhi : t < (192 : ℝ) / 128) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 128) (lo := 176) (hi := 192) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc28 {t : ℝ} (ht : 0 < t) (hlo : (192 : ℝ) / 128 ≤ t) (hhi : t < (208 : ℝ) / 128) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 128) (lo := 192) (hi := 208) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc29 {t : ℝ} (ht : 0 < t) (hlo : (208 : ℝ) / 128 ≤ t) (hhi : t < (224 : ℝ) / 128) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 128) (lo := 208) (hi := 224) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

lemma zc30 {t : ℝ} (ht : 0 < t) (hlo : (28 : ℝ) / 16 ≤ t) (hhi : t < (34 : ℝ) / 16) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  refine zone (M := 16) (lo := 28) (hi := 34) (by norm_num) ?_ ht (by exact_mod_cast hlo)
    (by exact_mod_cast hhi)
  intro j h1 h2
  interval_cases j <;> norm_num [nP, eP, bP, cTail]

/-- The grid: every `0 < t < 17/8`. -/
lemma tail_grid {t : ℝ} (ht : 0 < t) (hhi : t < 17 / 8) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  rcases lt_or_ge t ((12 : ℝ) / 16) with h0 | h0
  · exact zc0 ht (by norm_num; linarith) h0
  rcases lt_or_ge t ((112 : ℝ) / 128) with h1 | h1
  · exact zc1 ht (by norm_num; linarith) h1
  rcases lt_or_ge t ((128 : ℝ) / 128) with h2 | h2
  · exact zc2 ht (by norm_num; linarith) h2
  rcases lt_or_ge t ((1040 : ℝ) / 1024) with h3 | h3
  · exact zc3 ht (by norm_num; linarith) h3
  rcases lt_or_ge t ((1056 : ℝ) / 1024) with h4 | h4
  · exact zc4 ht (by norm_num; linarith) h4
  rcases lt_or_ge t ((1072 : ℝ) / 1024) with h5 | h5
  · exact zc5 ht (by norm_num; linarith) h5
  rcases lt_or_ge t ((1088 : ℝ) / 1024) with h6 | h6
  · exact zc6 ht (by norm_num; linarith) h6
  rcases lt_or_ge t ((1104 : ℝ) / 1024) with h7 | h7
  · exact zc7 ht (by norm_num; linarith) h7
  rcases lt_or_ge t ((1120 : ℝ) / 1024) with h8 | h8
  · exact zc8 ht (by norm_num; linarith) h8
  rcases lt_or_ge t ((1136 : ℝ) / 1024) with h9 | h9
  · exact zc9 ht (by norm_num; linarith) h9
  rcases lt_or_ge t ((1152 : ℝ) / 1024) with h10 | h10
  · exact zc10 ht (by norm_num; linarith) h10
  rcases lt_or_ge t ((1168 : ℝ) / 1024) with h11 | h11
  · exact zc11 ht (by norm_num; linarith) h11
  rcases lt_or_ge t ((1184 : ℝ) / 1024) with h12 | h12
  · exact zc12 ht (by norm_num; linarith) h12
  rcases lt_or_ge t ((1200 : ℝ) / 1024) with h13 | h13
  · exact zc13 ht (by norm_num; linarith) h13
  rcases lt_or_ge t ((1216 : ℝ) / 1024) with h14 | h14
  · exact zc14 ht (by norm_num; linarith) h14
  rcases lt_or_ge t ((1232 : ℝ) / 1024) with h15 | h15
  · exact zc15 ht (by norm_num; linarith) h15
  rcases lt_or_ge t ((1248 : ℝ) / 1024) with h16 | h16
  · exact zc16 ht (by norm_num; linarith) h16
  rcases lt_or_ge t ((1264 : ℝ) / 1024) with h17 | h17
  · exact zc17 ht (by norm_num; linarith) h17
  rcases lt_or_ge t ((1280 : ℝ) / 1024) with h18 | h18
  · exact zc18 ht (by norm_num; linarith) h18
  rcases lt_or_ge t ((1296 : ℝ) / 1024) with h19 | h19
  · exact zc19 ht (by norm_num; linarith) h19
  rcases lt_or_ge t ((1312 : ℝ) / 1024) with h20 | h20
  · exact zc20 ht (by norm_num; linarith) h20
  rcases lt_or_ge t ((1328 : ℝ) / 1024) with h21 | h21
  · exact zc21 ht (by norm_num; linarith) h21
  rcases lt_or_ge t ((1344 : ℝ) / 1024) with h22 | h22
  · exact zc22 ht (by norm_num; linarith) h22
  rcases lt_or_ge t ((1360 : ℝ) / 1024) with h23 | h23
  · exact zc23 ht (by norm_num; linarith) h23
  rcases lt_or_ge t ((1376 : ℝ) / 1024) with h24 | h24
  · exact zc24 ht (by norm_num; linarith) h24
  rcases lt_or_ge t ((1392 : ℝ) / 1024) with h25 | h25
  · exact zc25 ht (by norm_num; linarith) h25
  rcases lt_or_ge t ((1408 : ℝ) / 1024) with h26 | h26
  · exact zc26 ht (by norm_num; linarith) h26
  rcases lt_or_ge t ((192 : ℝ) / 128) with h27 | h27
  · exact zc27 ht (by norm_num; linarith) h27
  rcases lt_or_ge t ((208 : ℝ) / 128) with h28 | h28
  · exact zc28 ht (by norm_num; linarith) h28
  rcases lt_or_ge t ((224 : ℝ) / 128) with h29 | h29
  · exact zc29 ht (by norm_num; linarith) h29
  exact zc30 ht (by norm_num; linarith) (by norm_num; linarith)

/-- **`Pr(|ξ| ≥ t) ≤ cTail/t²` for a standard Gaussian `ξ`, every `t > 0`**
(`cTail = 0.3345`; the true supremum of `2t²Φ̄(t)` is `0.33114…`). -/
theorem tail2_le {t : ℝ} (ht : 0 < t) :
    (gaussianReal 0 1).real {x | t ≤ |x|} ≤ cTail / t ^ 2 := by
  rcases lt_or_ge t (17 / 8) with h3 | h3
  · exact tail_grid ht h3
  · exact tail_large h3

end BstLean.Part146

open BstLean.Part146 in
#print axioms mills9_upper
open BstLean.Part146 in
#print axioms tail2_le
