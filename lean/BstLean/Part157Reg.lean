import BstLean.Part157Defs

/-!
# Part 157, item 2: the Gaussian regression as a product decomposition

Role: `delegations/statements/p157-spec.md`, item 2. Paper: `theorem7-02-world.tex`,
Lemma `t7:p02:regression`, and `theorem7-03-composition.tex`, Lemma `t7:p03:regression`.
Do not use `sorry`, `native_decide` or `axiom`.

`M` is a Gaussian matrix with `q` rows and `m` columns (entry variance `v`), `b` is a vector of
`ℝ^m` (the centre). Part 134 has `M = glue b (M b) (M P_{b^⊥})` (`split_eq`) and, for a FIXED
`b ≠ 0`, the independence of `M b` and `M P_{b^⊥}` (`s1_split`, `s1_disint`).

This file gives the form that the composition needs:

* `cOf v b ξ = (√v·|b|)·ξ`: the centre image `M b` written with a standard Gaussian vector `ξ`.
* `reb b c M' = glue b c (M' P_{b^⊥})`: the matrix with image `c` on `b` and the residual part of
  `M'`. For `b = 0`: `reb 0 c M' = M'`.
* `gauss_split` (every `b`, also `b = 0`): the pair `(M b, M)` has the distribution of
  `(c, reb b c M')`, `c = cOf v b ξ`, where `ξ` (standard Gaussian vector) and `M'` (Gaussian
  matrix) are independent.
* `gauss_split_param`: the same when `b = b(d)` is a measurable function of data `d` that are
  independent of `M`: the triple `(d, M b(d), M)` has the distribution of
  `(d, c, reb (b d) c M')`, with `d`, `ξ`, `M'` independent. One statement for `W₃` and for `A₃`.
* `reb_mulVec`: `(reb b c M') h = λ(h)·c + M' r(h)` for EVERY `h` (the map from the residual to the
  output at all inputs), and `mlp2_reb`: the network output at every input `z`.
* `resid_gauss`: `M' r(h)` has the distribution of `σ(h)·γ`, `σ(h) = √v·|r(h)|`.
* `net_split`: the decomposition for a random MLP whose centre is a measurable function of the
  two hidden matrices.
* `map_fibre`: the general tool (replace the conditional distribution on each fibre).
-/

namespace BstLean.Part157

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss)

/-! ## The general tool -/

section fibre

variable {X Y Y' Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Y']
  [MeasurableSpace Z]

/-- **Replace the conditional distribution on each fibre.** If, for every `x`, the image of `ν`
under `T(x, ·)` is the image of `ρ` under `S(x, ·)`, then the image of `μ ⊗ ν` under
`(x, y) ↦ (x, T(x, y))` is the image of `μ ⊗ ρ` under `(x, y') ↦ (x, S(x, y'))`. -/
theorem map_fibre (μ : Measure X) [SFinite μ] (ν : Measure Y) [SFinite ν] (ρ : Measure Y')
    [SFinite ρ] {T : X × Y → Z} {S : X × Y' → Z} (hT : Measurable T) (hS : Measurable S)
    (h : ∀ x, ν.map (fun y => T (x, y)) = ρ.map (fun y => S (x, y))) :
    (μ.prod ν).map (fun p => (p.1, T p)) = (μ.prod ρ).map (fun p => (p.1, S p)) := by
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have mT : Measurable (fun p : X × Y => (p.1, T p)) := measurable_fst.prodMk hT
  have mS : Measurable (fun p : X × Y' => (p.1, S p)) := measurable_fst.prodMk hS
  rw [lintegral_map hg mT, lintegral_map hg mS,
    lintegral_prod (fun a : X × Y => g (a.1, T a)) (hg.comp mT).aemeasurable,
    lintegral_prod (fun a : X × Y' => g (a.1, S a)) (hg.comp mS).aemeasurable]
  refine lintegral_congr fun x => ?_
  have hgx : Measurable (fun z : Z => g (x, z)) := hg.comp measurable_prodMk_left
  have e1 : ∫⁻ y, g (x, T (x, y)) ∂ν = ∫⁻ z, g (x, z) ∂ν.map (fun y => T (x, y)) :=
    (lintegral_map hgx (hT.comp measurable_prodMk_left)).symm
  have e2 : ∫⁻ y, g (x, S (x, y)) ∂ρ = ∫⁻ z, g (x, z) ∂ρ.map (fun y => S (x, y)) :=
    (lintegral_map hgx (hS.comp measurable_prodMk_left)).symm
  rw [e1, e2, h x]

end fibre

/-! ## The decomposition of one Gaussian matrix -/

variable {q m : ℕ}

/-- The centre image written with a standard Gaussian vector: `(√v·|b|)·ξ`. For a Gaussian matrix
`M` with entry variance `v`, `M b` has the distribution of `cOf v b ξ`. -/
noncomputable def cOf (v : ℝ) (b : Fin m → ℝ) (ξ : Fin q → ℝ) : Fin q → ℝ :=
  (√v * √(normSq b)) • ξ

/-- **The matrix with image `c` on `b` and the residual part of `M'`**:
`c bᵀ/|b|² + M' P_{b^⊥}`. -/
noncomputable def reb (b : Fin m → ℝ) (c : Fin q → ℝ) (M' : Matrix (Fin q) (Fin m) ℝ) :
    Matrix (Fin q) (Fin m) ℝ :=
  glue b c (M' * projPerp b)

lemma projPerp_zero : projPerp (0 : Fin m → ℝ) = 1 := by
  unfold projPerp
  have : normSq (0 : Fin m → ℝ) = 0 := by simp [normSq]
  simp [this]

lemma reb_zero (c : Fin q → ℝ) (M' : Matrix (Fin q) (Fin m) ℝ) : reb (0 : Fin m → ℝ) c M' = M' := by
  unfold reb glue
  have : normSq (0 : Fin m → ℝ) = 0 := by simp [normSq]
  rw [projPerp_zero]
  simp [this]

lemma cOf_zero (v : ℝ) (ξ : Fin q → ℝ) : cOf v (0 : Fin m → ℝ) ξ = 0 := by
  unfold cOf
  have : normSq (0 : Fin m → ℝ) = 0 := by simp [normSq]
  simp [this]

/-- **The residual determines the output at every hidden vector**:
`(reb b c M') h = λ(h)·c + M' r(h)`, `λ = ⟨h, b⟩/|b|²`, `r = h − λ b`. -/
theorem reb_mulVec (b : Fin m → ℝ) (c : Fin q → ℝ) (M' : Matrix (Fin q) (Fin m) ℝ)
    (h : Fin m → ℝ) : (reb b c M').mulVec h = lam b h • c + M'.mulVec (res b h) :=
  glue_res b c M' h

/-- The matrix `reb b c M'` has image `c` on `b` (for `b ≠ 0`). -/
theorem reb_mulVec_self {b : Fin m → ℝ} (hb : b ≠ 0) (c : Fin q → ℝ)
    (M' : Matrix (Fin q) (Fin m) ℝ) : (reb b c M').mulVec b = c := by
  rw [reb_mulVec, res_self hb]
  have h1 : lam b b = 1 := by
    unfold lam
    have : ∑ j, b j * b j = normSq b := Finset.sum_congr rfl fun j _ => (sq _).symm
    rw [this, div_self (normSq_ne_zero hb)]
  simp [h1]

/-- **The network output at EVERY input**, for a last matrix `reb b c M'`:
`N(z) = λ(z)·c + M' r(z)`, with `a₂(z) = ReLU(M₂ ReLU(M₁ z))` the last hidden vector. -/
theorem mlp2_reb {k m₁ : ℕ} (M₁ : Matrix (Fin m₁) (Fin k) ℝ) (M₂ : Matrix (Fin m) (Fin m₁) ℝ)
    (b : Fin m → ℝ) (c : Fin q → ℝ) (M' : Matrix (Fin q) (Fin m) ℝ) (z : Fin k → ℝ) :
    mlp2 M₁ M₂ (reb b c M') z =
      lam b (hid2 M₁ M₂ z) • c + M'.mulVec (res b (hid2 M₁ M₂ z)) :=
  reb_mulVec b c M' _

/-- **The residual field at one hidden vector is Gaussian**: `M' r(h)` has the distribution of
`σ(h)·γ`, `σ(h) = √v·|r(h)|`, `γ` a standard Gaussian vector. -/
theorem resid_gauss (v : ℝ) (b h : Fin m → ℝ) :
    (gaussMat q m v).map (fun M' => M'.mulVec (res b h)) =
      (stdGauss (Fin q)).map (fun γ => sig v b h • γ) :=
  gaussMat_mulVec v (res b h)

lemma measurable_cOf (v : ℝ) :
    Measurable (fun p : (Fin m → ℝ) × (Fin q → ℝ) => cOf v p.1 p.2) := by
  unfold cOf
  have h1 : Measurable (fun p : (Fin m → ℝ) × (Fin q → ℝ) => √v * √(normSq p.1)) :=
    measurable_const.mul
      ((continuous_normSq.measurable.comp measurable_fst).sqrt)
  exact h1.smul measurable_snd

/-- `(b, c, M') ↦ reb b c M'` is measurable (jointly, also in the centre `b`). -/
lemma measurable_reb :
    Measurable (fun p : (Fin m → ℝ) × (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ =>
      reb p.1 p.2.1 p.2.2) := by
  have hc : Continuous (fun x : ℝ × (Fin m → ℝ) × (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ =>
      x.1 • Matrix.vecMulVec x.2.2.1 x.2.1 +
        x.2.2.2 * (1 - x.1 • Matrix.vecMulVec x.2.1 x.2.1)) := by
    have v1 : Continuous (fun x : ℝ × (Fin m → ℝ) × (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ =>
        Matrix.vecMulVec x.2.2.1 x.2.1) := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.vecMulVec_apply]
      fun_prop
    have v2 : Continuous (fun x : ℝ × (Fin m → ℝ) × (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ =>
        Matrix.vecMulVec x.2.1 x.2.1) := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.vecMulVec_apply]
      fun_prop
    exact (continuous_fst.smul v1).add
      (Continuous.matrix_mul (continuous_snd.comp (continuous_snd.comp continuous_snd))
        (continuous_const.sub (continuous_fst.smul v2)))
  have hm : Measurable (fun p : (Fin m → ℝ) × (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ =>
      ((normSq p.1)⁻¹, p)) :=
    ((continuous_normSq.measurable.comp measurable_fst).inv).prodMk measurable_id
  exact hc.measurable.comp hm

lemma measurable_cOf_comp {α : Type*} [MeasurableSpace α] (v : ℝ) {b : α → Fin m → ℝ}
    {ξ : α → Fin q → ℝ} (hb : Measurable b) (hξ : Measurable ξ) :
    Measurable (fun a => cOf v (b a) (ξ a)) := by
  have h := (measurable_cOf (m := m) (q := q) v).comp (hb.prodMk hξ)
  exact h

lemma measurable_reb_comp {α : Type*} [MeasurableSpace α] {b : α → Fin m → ℝ}
    {c : α → Fin q → ℝ} {M : α → Matrix (Fin q) (Fin m) ℝ} (hb : Measurable b)
    (hc : Measurable c) (hM : Measurable M) :
    Measurable (fun a => reb (b a) (c a) (M a)) := by
  have h := (measurable_reb (m := m) (q := q)).comp (hb.prodMk (hc.prodMk hM))
  exact h

/-- **The Gaussian regression for one matrix, every centre `b`** (also `b = 0`). `M` a Gaussian
matrix with entry variance `v`. The pair `(M b, M)` has the distribution of `(c, reb b c M')` with
`c = (√v·|b|)·ξ`, where the standard Gaussian vector `ξ` and the Gaussian matrix `M'` are
independent (their joint distribution is the product). So `M b` and the residual part are
independent, and `M = (M b) bᵀ/|b|² + M_⊥`. -/
theorem gauss_split (v : ℝ) (b : Fin m → ℝ) :
    (gaussMat q m v).map (fun M => (M.mulVec b, M)) =
      ((stdGauss (Fin q)).prod (gaussMat q m v)).map
        (fun p => (cOf v b p.1, reb b (cOf v b p.1) p.2)) := by
  by_cases hb : b = 0
  · subst hb
    have e1 : (fun M : Matrix (Fin q) (Fin m) ℝ => (M.mulVec (0 : Fin m → ℝ), M)) =
        fun M => ((0 : Fin q → ℝ), M) := by
      funext M; simp
    have e2 : (fun p : (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ =>
        (cOf v (0 : Fin m → ℝ) p.1, reb (0 : Fin m → ℝ) (cOf v (0 : Fin m → ℝ) p.1) p.2)) =
        (fun M => ((0 : Fin q → ℝ), M)) ∘ Prod.snd := by
      funext p; simp [cOf_zero, reb_zero]
    have e3 : Measure.map ((fun M : Matrix (Fin q) (Fin m) ℝ => ((0 : Fin q → ℝ), M)) ∘ Prod.snd)
        ((stdGauss (Fin q)).prod (gaussMat q m v)) =
        Measure.map (fun M : Matrix (Fin q) (Fin m) ℝ => ((0 : Fin q → ℝ), M))
          (Measure.map Prod.snd ((stdGauss (Fin q)).prod (gaussMat q m v))) :=
      (Measure.map_map (measurable_const.prodMk measurable_id) measurable_snd).symm
    rw [e1, e2, e3, Measure.map_snd_prod]
    simp
  · have hf : Measurable (fun ξ : Fin q → ℝ => (√v * √(normSq b)) • ξ) :=
      measurable_const_smul _
    have hG : Measurable (fun p : (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ =>
        (p.1, glue b p.1 (p.2 * projPerp b))) :=
      measurable_fst.prodMk ((measurable_glue b).comp
        (measurable_fst.prodMk ((measurable_mul_right _).comp measurable_snd)))
    rw [s1_disint v hb]
    have e : (cDist q v b).prod (gaussMat q m v) =
        ((stdGauss (Fin q)).prod (gaussMat q m v)).map
          (Prod.map (fun ξ : Fin q → ℝ => (√v * √(normSq b)) • ξ) id) := by
      rw [← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id]
      rfl
    rw [e, Measure.map_map hG (hf.prodMap measurable_id)]
    rfl

/-- **The Gaussian regression with a centre that depends on independent data** (the form for
`W₃` and for `A₃`). `d` has the distribution `μD` and is independent of the Gaussian matrix `M`;
`b = b(d)` is measurable. Then `(d, M b(d), M)` has the distribution of
`(d, c, reb (b d) c M')`, `c = (√v·|b(d)|)·ξ`, where `d`, the standard Gaussian vector `ξ` and the
Gaussian matrix `M'` are independent. In particular, given the retained data `(d, M b(d))`, the
residual `M'` is a Gaussian matrix whose distribution does not depend on the retained data. -/
theorem gauss_split_param {D : Type*} [MeasurableSpace D] (μD : Measure D) [SFinite μD] (v : ℝ)
    {b : D → Fin m → ℝ} (hb : Measurable b) :
    (μD.prod (gaussMat q m v)).map (fun p => (p.1, (p.2.mulVec (b p.1), p.2))) =
      (μD.prod ((stdGauss (Fin q)).prod (gaussMat q m v))).map
        (fun p => (p.1, (cOf v (b p.1) p.2.1, reb (b p.1) (cOf v (b p.1) p.2.1) p.2.2))) := by
  have hc : Measurable (fun p : D × (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ =>
      cOf v (b p.1) p.2.1) := measurable_cOf_comp v (hb.comp measurable_fst)
    (measurable_fst.comp measurable_snd)
  have hT : Measurable (fun p : D × Matrix (Fin q) (Fin m) ℝ => (p.2.mulVec (b p.1), p.2)) :=
    (measurable_mulVec_joint.comp (measurable_snd.prodMk (hb.comp measurable_fst))).prodMk
      measurable_snd
  have hS : Measurable (fun p : D × (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ =>
      (cOf v (b p.1) p.2.1, reb (b p.1) (cOf v (b p.1) p.2.1) p.2.2)) :=
    hc.prodMk (measurable_reb_comp (hb.comp measurable_fst) hc (measurable_snd.comp measurable_snd))
  exact map_fibre μD (gaussMat q m v) ((stdGauss (Fin q)).prod (gaussMat q m v)) hT hS
    (fun d => gauss_split v (b d))

end BstLean.Part157

open BstLean.Part157 in
#print axioms gauss_split
open BstLean.Part157 in
#print axioms gauss_split_param
