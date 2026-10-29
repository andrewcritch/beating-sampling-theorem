import BstLean.Part131Tail

/-!
# Part 131, item 1: the Gaussian block lemma

Role: `delegations/statements/p131-spec.md`, item 1. Paper source: round onW4c, "Confirmed
probability argument".

`gauss_block`: for a standard Gaussian vector `g` in `ℝ^ι`, a vector `v` and a matrix `M` with
`yᵀMy ≥ 0` for every `y` and `tr M < |v|²`: `Pr(gᵀMg < (g·v)²) > 3/25`.

Proof (the paper's, without a rotation matrix): with `e = v/|v|` and `P = I − eeᵀ`, `g` has the
distribution of `x·e + P h` with `x` a standard Gaussian in `ℝ` and `h` an independent standard
Gaussian vector (`stdGauss_decomp`, from "centred Gaussian vectors with the same covariance have
the same distribution"). For fixed `h`, one of the two signs of `x` makes the cross term
nonpositive, so the event has conditional probability at least `Φ̄(√(q(h)/(D − a)))`,
`q(h) = (Ph)ᵀM(Ph)`, `a = eᵀMe`, `D = |v|²`. The supporting line of `z ↦ Φ̄(√z)` at `1`
(`tail_line`) and `E q = tr M − a` give at least `Φ̄(1) + (φ(1)/2)(D − tr M)/(D − a) > Φ̄(1) > 3/25`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part131

open MeasureTheory ProbabilityTheory Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part105 (gaussLin105)
open BstLean.Part130 (stdGauss_cov stdGauss_mul_integrable)

variable {ι : Type} [Fintype ι]

/-! ## The quadratic form of a standard Gaussian vector -/

lemma qform_expand (N : Matrix ι ι ℝ) (h : ι → ℝ) :
    h ⬝ᵥ N *ᵥ h = ∑ i, ∑ j, N i j * (h i * h j) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma qform_integrable (N : Matrix ι ι ℝ) :
    Integrable (fun h : ι → ℝ => h ⬝ᵥ N *ᵥ h) (stdGauss ι) := by
  simp_rw [qform_expand]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (stdGauss_mul_integrable i j).const_mul _

/-- `E hᵀNh = tr N` for a standard Gaussian vector `h`. -/
lemma qform_integral (N : Matrix ι ι ℝ) : ∫ h, h ⬝ᵥ N *ᵥ h ∂stdGauss ι = N.trace := by
  classical
  rw [show (fun h : ι → ℝ => h ⬝ᵥ N *ᵥ h) = fun h => ∑ i, ∑ j, N i j * (h i * h j) from
    funext (qform_expand N)]
  have h1 : ∫ h : ι → ℝ, ∑ i, ∑ j, N i j * (h i * h j) ∂stdGauss ι =
      ∑ i, ∑ j, N i j * ∫ h : ι → ℝ, h i * h j ∂stdGauss ι := by
    rw [integral_finsetSum (f := fun i (h : ι → ℝ) => ∑ j, N i j * (h i * h j)) _
      fun i _ => integrable_finsetSum _ fun j _ => (stdGauss_mul_integrable i j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum (f := fun j (h : ι → ℝ) => N i j * (h i * h j)) _
      fun j _ => (stdGauss_mul_integrable i j).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact integral_const_mul _ _
  rw [h1]
  simp_rw [stdGauss_cov]
  simp [Matrix.trace]

/-! ## The decomposition of a standard Gaussian vector along a unit vector -/

lemma stdGauss_sum_split :
    (stdGauss (Fin 1 ⊕ ι)).map (fun ξ => (ξ (Sum.inl 0), fun i => ξ (Sum.inr i))) =
      (gaussianReal 0 1).prod (stdGauss ι) := by
  unfold stdGauss
  have h1 := (measurePreserving_sumPiEquivProdPi (fun _ : Fin 1 ⊕ ι => gaussianReal 0 1)).map_eq
  have h2 := (measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) 0).map_eq
  have h3 := Measure.map_prod_map (Measure.pi fun _ : Fin 1 => gaussianReal 0 1)
    (Measure.pi fun _ : ι => gaussianReal 0 1) (measurable_pi_apply 0) measurable_id
  rw [h2, Measure.map_id] at h3
  rw [h3, ← h1, Measure.map_map ((measurable_pi_apply 0).prodMap measurable_id)
    (MeasurableEquiv.measurable _)]
  rfl

/-- The projection `P = I − eeᵀ`. -/
noncomputable def projMat [DecidableEq ι] (e : ι → ℝ) : Matrix ι ι ℝ := 1 - vecMulVec e e

omit [Fintype ι] in
lemma projMat_transpose [DecidableEq ι] (e : ι → ℝ) : (projMat e)ᵀ = projMat e := by
  simp [projMat, transpose_sub, transpose_vecMulVec]

lemma projMat_mul_self [DecidableEq ι] {e : ι → ℝ} (he : e ⬝ᵥ e = 1) : projMat e * projMat e = projMat e := by
  simp only [projMat, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    vecMulVec_mul_vecMulVec, he, one_smul]
  abel

lemma projMat_mulVec [DecidableEq ι] (e h : ι → ℝ) : projMat e *ᵥ h = h - (e ⬝ᵥ h) • e := by
  simp [projMat, sub_mulVec, vecMulVec_mulVec]

lemma projMat_dot [DecidableEq ι] {e : ι → ℝ} (he : e ⬝ᵥ e = 1) (h : ι → ℝ) : (projMat e *ᵥ h) ⬝ᵥ e = 0 := by
  rw [projMat_mulVec, sub_dotProduct, smul_dotProduct, he, dotProduct_comm]
  simp

/-- **A standard Gaussian vector `g` has the distribution of `x·e + P h`**, `e` a unit vector,
`P = I − eeᵀ`, `x` a standard Gaussian in `ℝ`, `h` an independent standard Gaussian vector. -/
theorem stdGauss_decomp [DecidableEq ι] {e : ι → ℝ} (he : e ⬝ᵥ e = 1) :
    ((gaussianReal 0 1).prod (stdGauss ι)).map (fun p => p.1 • e + projMat e *ᵥ p.2) =
      stdGauss ι := by
  let A : Matrix ι (Fin 1 ⊕ ι) ℝ :=
    Matrix.of fun i k => Sum.elim (fun _ => e i) (fun j => projMat e i j) k
  have hA : ∀ ξ : Fin 1 ⊕ ι → ℝ,
      A *ᵥ ξ = ξ (Sum.inl 0) • e + projMat e *ᵥ (fun i => ξ (Sum.inr i)) := by
    intro ξ
    ext i
    simp [A, mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]
  have hAA : A * Aᵀ = (1 : Matrix ι ι ℝ) * (1 : Matrix ι ι ℝ)ᵀ := by
    simp only [Matrix.one_mul, transpose_one]
    ext i i'
    have hsym : ∀ j, projMat e j i' = projMat e i' j := fun j => by
      have := congrFun (congrFun (projMat_transpose e) i') j
      rw [transpose_apply] at this
      exact this
    have hP' := congrFun (congrFun (projMat_mul_self he) i) i'
    simp only [mul_apply] at hP'
    simp_rw [hsym] at hP'
    simp only [mul_apply, transpose_apply, A, of_apply, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton]
    rw [hP']
    have h11 : (1 : Matrix ι ι ℝ) i' i = (1 : Matrix ι ι ℝ) i i' := by
      simp [Matrix.one_apply, eq_comm]
    simp only [projMat, Matrix.sub_apply, vecMulVec_apply, h11]
    ring
  have hg := gaussLin105 _ _ _ A (1 : Matrix ι ι ℝ) hAA
  simp only [one_mulVec, Measure.map_id'] at hg
  conv_rhs => rw [← hg]
  rw [← stdGauss_sum_split, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext ξ
  exact (hA ξ).symm

/-! ## The block lemma -/

/-- **The Gaussian block lemma with the paper's constant `Φ̄(1)`** (round onW4c, "Confirmed
probability argument"). `g` is a standard Gaussian vector in `ℝ^ι`; `M` has a nonnegative
quadratic form; `tr M < |v|²`. Then `Pr(gᵀMg < (g·v)²) > Φ̄(1)`, `Φ̄(1) = γ(1, ∞)`. -/
theorem gauss_block_tail (v : ι → ℝ) (M : Matrix ι ι ℝ) (hM : ∀ y : ι → ℝ, 0 ≤ y ⬝ᵥ M *ᵥ y)
    (hv : M.trace < v ⬝ᵥ v) :
    (gaussianReal 0 1).real (Ioi 1) < (stdGauss ι).real {g | g ⬝ᵥ M *ᵥ g < (g ⬝ᵥ v) ^ 2} := by
  classical
  have htr : 0 ≤ M.trace := by
    rw [← qform_integral]; exact integral_nonneg fun h => hM h
  set D : ℝ := v ⬝ᵥ v with hD
  have hDpos : 0 < D := lt_of_le_of_lt htr hv
  set s : ℝ := √D with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hDpos
  have hss : s ^ 2 = D := Real.sq_sqrt hDpos.le
  set e : ι → ℝ := s⁻¹ • v with he_def
  have hve : v = s • e := by rw [he_def, smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]
  have he : e ⬝ᵥ e = 1 := by
    rw [he_def, smul_dotProduct, dotProduct_smul, ← hD, smul_eq_mul, smul_eq_mul, ← hss]
    field_simp
  set P := projMat e with hP
  set a : ℝ := e ⬝ᵥ M *ᵥ e with ha
  let q : (ι → ℝ) → ℝ := fun h => (P *ᵥ h) ⬝ᵥ M *ᵥ (P *ᵥ h)
  let β : (ι → ℝ) → ℝ := fun h => e ⬝ᵥ M *ᵥ (P *ᵥ h) + (P *ᵥ h) ⬝ᵥ M *ᵥ e
  have hq0 : ∀ h, 0 ≤ q h := fun h => hM _
  have hqN : ∀ h, q h = h ⬝ᵥ (Pᵀ * M * P) *ᵥ h := by
    intro h
    simp only [q]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec h, vecMul_transpose]
  have hqint : Integrable q (stdGauss ι) := by
    rw [show q = fun h => h ⬝ᵥ (Pᵀ * M * P) *ᵥ h from funext hqN]; exact qform_integrable _
  have hEq : ∫ h, q h ∂stdGauss ι = M.trace - a := by
    rw [show q = fun h => h ⬝ᵥ (Pᵀ * M * P) *ᵥ h from funext hqN]
    rw [qform_integral, trace_mul_cycle, hP, projMat_transpose, projMat_mul_self he, projMat,
      Matrix.sub_mul, Matrix.one_mul, trace_sub, vecMulVec_mul, trace_vecMulVec, ha,
      dotProduct_mulVec, dotProduct_comm]
  have haT : a ≤ M.trace := by
    have : 0 ≤ ∫ h, q h ∂stdGauss ι := integral_nonneg hq0
    linarith
  set δ : ℝ := D - a with hδ
  have hδpos : 0 < δ := by linarith
  -- the event in the coordinates `(x, h)`
  let Φ : ℝ × (ι → ℝ) → ι → ℝ := fun p => p.1 • e + P *ᵥ p.2
  have hΦ : Measurable Φ := by fun_prop
  set S : Set (ι → ℝ) := {g | g ⬝ᵥ M *ᵥ g < (g ⬝ᵥ v) ^ 2} with hSdef
  have hS : MeasurableSet S := by
    have h1 : Continuous fun g : ι → ℝ => g ⬝ᵥ M *ᵥ g := by fun_prop
    have h2 : Continuous fun g : ι → ℝ => (g ⬝ᵥ v) ^ 2 := by fun_prop
    exact measurableSet_lt h1.measurable h2.measurable
  have hmem : ∀ (x : ℝ) (h : ι → ℝ), Φ (x, h) ∈ S ↔ x ^ 2 * a + x * β h + q h < D * x ^ 2 := by
    intro x h
    have h0 : (P *ᵥ h) ⬝ᵥ e = 0 := projMat_dot he h
    have e1 : Φ (x, h) ⬝ᵥ M *ᵥ Φ (x, h) = x ^ 2 * a + x * β h + q h := by
      simp only [Φ, β, q, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, ha]
      ring
    have e2 : (Φ (x, h) ⬝ᵥ v) ^ 2 = D * x ^ 2 := by
      simp only [Φ]
      rw [hve, dotProduct_smul, add_dotProduct, smul_dotProduct, he, h0, ← hss]
      simp only [smul_eq_mul]; ring
    change Φ (x, h) ⬝ᵥ M *ᵥ Φ (x, h) < (Φ (x, h) ⬝ᵥ v) ^ 2 ↔ _
    rw [e1, e2]
  have hreal : (stdGauss ι).real S =
      ∫ h, (gaussianReal 0 1).real {x | Φ (x, h) ∈ S} ∂stdGauss ι := by
    conv_lhs => rw [← stdGauss_decomp he]
    rw [map_measureReal_apply hΦ hS, Measure.real, Measure.prod_apply_symm (hΦ hS),
      ← integral_toReal (measurable_measure_prodMk_right (hΦ hS)).aemeasurable
        (ae_of_all _ fun h => measure_lt_top _ _)]
    rfl
  set c : ℝ := phi1 / 2 with hc
  have hcpos : 0 < c := by have := phi1_pos; positivity
  set T1 : ℝ := (gaussianReal 0 1).real (Ioi 1) with hT1
  -- the pointwise lower bound
  have hpt : ∀ h, T1 + c * (1 - q h / δ) ≤ (gaussianReal 0 1).real {x | Φ (x, h) ∈ S} := by
    intro h
    set t : ℝ := √(q h / δ) with ht
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have htt : t ^ 2 = q h / δ := Real.sq_sqrt (div_nonneg (hq0 h) hδpos.le)
    have hline := tail_line ht0
    rw [htt] at hline
    have hkey : ∀ x : ℝ, t ^ 2 < x ^ 2 → x * β h ≤ 0 → Φ (x, h) ∈ S := by
      intro x hx hxb
      rw [hmem]
      rw [htt, div_lt_iff₀ hδpos] at hx
      rw [hδ] at hx
      nlinarith
    rcases le_or_gt (β h) 0 with hb | hb
    · have hsub : Ioi t ⊆ {x | Φ (x, h) ∈ S} := by
        intro x hx
        have hx' : t < x := hx
        exact hkey x (by nlinarith) (by nlinarith)
      exact hline.trans (measureReal_mono hsub)
    · have hsub : Iio (-t) ⊆ {x | Φ (x, h) ∈ S} := by
        intro x hx
        have hx' : x < -t := hx
        exact hkey x (by nlinarith) (by nlinarith)
      exact (hline.trans (tail_neg t).symm.le).trans (measureReal_mono hsub)
  have i1 : Integrable (fun h => q h / δ) (stdGauss ι) := hqint.div_const _
  have i2 : Integrable (fun h => 1 - q h / δ) (stdGauss ι) := (integrable_const _).sub i1
  have i3 : Integrable (fun h => c * (1 - q h / δ)) (stdGauss ι) := i2.const_mul c
  have hint1 : Integrable (fun h => T1 + c * (1 - q h / δ)) (stdGauss ι) :=
    (integrable_const _).add i3
  have hint2 : Integrable (fun h => (gaussianReal 0 1).real {x | Φ (x, h) ∈ S}) (stdGauss ι) := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (measurable_measure_prodMk_right (hΦ hS)).ennreal_toReal.aestronglyMeasurable ?_
    refine ae_of_all _ fun h => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hmono := integral_mono hint1 hint2 hpt
  rw [← hreal] at hmono
  have hI : ∫ h, T1 + c * (1 - q h / δ) ∂stdGauss ι = T1 + c * (1 - (M.trace - a) / δ) := by
    have e1 : ∫ h, q h / δ ∂stdGauss ι = (M.trace - a) / δ := by rw [integral_div, hEq]
    have e2 : ∫ h, (1 - q h / δ) ∂stdGauss ι = 1 - (M.trace - a) / δ := by
      rw [integral_sub (integrable_const _) i1, e1]; simp
    have e3 : ∫ h, c * (1 - q h / δ) ∂stdGauss ι = c * (1 - (M.trace - a) / δ) := by
      rw [integral_const_mul, e2]
    rw [integral_add (integrable_const _) i3, e3]; simp
  rw [hI] at hmono
  have h1 : 0 < 1 - (M.trace - a) / δ := by
    rw [sub_pos, div_lt_one hδpos]; linarith
  have h3 : 0 < c * (1 - (M.trace - a) / δ) := mul_pos hcpos h1
  linarith

/-- **The Gaussian block lemma** (item 1): under the same hypotheses,
`Pr(gᵀMg < (g·v)²) > 3/25`. -/
theorem gauss_block (v : ι → ℝ) (M : Matrix ι ι ℝ) (hM : ∀ y : ι → ℝ, 0 ≤ y ⬝ᵥ M *ᵥ y)
    (hv : M.trace < v ⬝ᵥ v) :
    3 / 25 < (stdGauss ι).real {g | g ⬝ᵥ M *ᵥ g < (g ⬝ᵥ v) ^ 2} :=
  tail_one_gt.trans (gauss_block_tail v M hM hv)

/-- **A linear form of a standard Gaussian vector is a centred Gaussian with variance `|v|²`.** -/
theorem stdGauss_dot (v : ι → ℝ) :
    (stdGauss ι).map (fun ξ => ξ ⬝ᵥ v) = gaussianReal 0 (v ⬝ᵥ v).toNNReal := by
  have hD : 0 ≤ v ⬝ᵥ v := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  let A : Matrix (Fin 1) ι ℝ := Matrix.of fun _ j => v j
  let B : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => √(v ⬝ᵥ v)
  have hAB : A * Aᵀ = B * Bᵀ := by
    ext i j
    simp only [mul_apply, transpose_apply, A, B, of_apply, Finset.univ_unique,
      Finset.sum_singleton, Real.mul_self_sqrt hD]
    rfl
  have hg := gaussLin105 _ _ _ A B hAB
  have h1 := congrArg (Measure.map (fun y : Fin 1 → ℝ => y 0)) hg
  rw [Measure.map_map (measurable_pi_apply 0) (by fun_prop),
    Measure.map_map (measurable_pi_apply 0) (by fun_prop)] at h1
  have e1 : ((fun y : Fin 1 → ℝ => y 0) ∘ fun ξ : ι → ℝ => A *ᵥ ξ) = fun ξ => ξ ⬝ᵥ v := by
    funext ξ
    simp [A, mulVec, dotProduct, mul_comm]
  have e2 : ((fun y : Fin 1 → ℝ => y 0) ∘ fun ξ : Fin 1 → ℝ => B *ᵥ ξ) =
      (fun x : ℝ => √(v ⬝ᵥ v) * x) ∘ fun ξ : Fin 1 → ℝ => ξ 0 := by
    funext ξ
    simp [B, mulVec, dotProduct]
  have h2 : (stdGauss (Fin 1)).map (fun ξ : Fin 1 → ℝ => ξ 0) = gaussianReal 0 1 :=
    (measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) 0).map_eq
  have h3 : Measure.map ((fun x : ℝ => √(v ⬝ᵥ v) * x) ∘ fun ξ : Fin 1 → ℝ => ξ 0)
      (stdGauss (Fin 1)) = Measure.map (fun x : ℝ => √(v ⬝ᵥ v) * x)
        (Measure.map (fun ξ : Fin 1 → ℝ => ξ 0) (stdGauss (Fin 1))) :=
    (Measure.map_map (by fun_prop) (measurable_pi_apply 0)).symm
  rw [e1, e2, h3, h2, gaussianReal_map_const_mul] at h1
  rw [h1]
  congr 1
  · simp
  · ext
    simp [Real.sq_sqrt hD, Real.coe_toNNReal _ hD]


/-- The block lemma for a positive semidefinite matrix. -/
theorem gauss_block_posSemidef (v : ι → ℝ) (M : Matrix ι ι ℝ) (hM : M.PosSemidef)
    (hv : M.trace < v ⬝ᵥ v) :
    3 / 25 < (stdGauss ι).real {g | g ⬝ᵥ M *ᵥ g < (g ⬝ᵥ v) ^ 2} := by
  refine gauss_block v M (fun y => ?_) hv
  have := hM.dotProduct_mulVec_nonneg y
  simpa using this

end BstLean.Part131

open BstLean.Part131 in
#print axioms stdGauss_decomp
open BstLean.Part131 in
#print axioms gauss_block_tail
open BstLean.Part131 in
#print axioms gauss_block
open BstLean.Part131 in
#print axioms stdGauss_dot
open BstLean.Part131 in
#print axioms gauss_block_posSemidef
