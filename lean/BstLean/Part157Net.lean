import BstLean.Part157Reg

/-!
# Part 157, item 2 (continued): the regression for a random MLP, and two rearrangements

Do not use `sorry`, `native_decide` or `axiom`.

* `net_split`: the decomposition for a random MLP whose centre is a measurable function of the
  two hidden matrices.
* `prod4_comm`, `prod_right_comm`: rearrangements of product measures (Tonelli).
-/

namespace BstLean.Part157

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss)

/-! ## Rearrangements of product measures -/

section rearr

variable {X₁ X₂ X₃ X₄ : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace X₃]
  [MeasurableSpace X₄]

/-- `(μ₁ ⊗ μ₂) ⊗ (μ₃ ⊗ μ₄)` and `(μ₁ ⊗ μ₃) ⊗ (μ₂ ⊗ μ₄)` agree under the exchange of the two
middle coordinates. -/
theorem prod4_comm (μ₁ : Measure X₁) (μ₂ : Measure X₂) (μ₃ : Measure X₃) (μ₄ : Measure X₄)
    [SFinite μ₁] [SFinite μ₂] [SFinite μ₃] [SFinite μ₄] :
    ((μ₁.prod μ₂).prod (μ₃.prod μ₄)).map (fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2))) =
      (μ₁.prod μ₃).prod (μ₂.prod μ₄) := by
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have me : Measurable (fun p : (X₁ × X₂) × (X₃ × X₄) => ((p.1.1, p.2.1), (p.1.2, p.2.2))) := by
    fun_prop
  rw [lintegral_map hg me]
  have hL : ∫⁻ p, g ((p.1.1, p.2.1), (p.1.2, p.2.2)) ∂((μ₁.prod μ₂).prod (μ₃.prod μ₄)) =
      ∫⁻ x₁, ∫⁻ x₂, ∫⁻ x₃, ∫⁻ x₄, g ((x₁, x₃), (x₂, x₄)) ∂μ₄ ∂μ₃ ∂μ₂ ∂μ₁ := by
    rw [lintegral_prod (fun p : (X₁ × X₂) × (X₃ × X₄) => g ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      (hg.comp me).aemeasurable]
    have m1 : Measurable (fun x : X₁ × X₂ =>
        ∫⁻ y, g ((x.1, y.1), (x.2, y.2)) ∂(μ₃.prod μ₄)) :=
      Measurable.lintegral_prod_right'
        (f := fun p : (X₁ × X₂) × (X₃ × X₄) => g ((p.1.1, p.2.1), (p.1.2, p.2.2))) (hg.comp me)
    rw [lintegral_prod (fun x : X₁ × X₂ => ∫⁻ y, g ((x.1, y.1), (x.2, y.2)) ∂(μ₃.prod μ₄))
      m1.aemeasurable]
    refine lintegral_congr fun x₁ => lintegral_congr fun x₂ => ?_
    exact lintegral_prod (fun y : X₃ × X₄ => g ((x₁, y.1), (x₂, y.2)))
      (hg.comp (by fun_prop)).aemeasurable
  have hR : ∫⁻ p, g p ∂((μ₁.prod μ₃).prod (μ₂.prod μ₄)) =
      ∫⁻ x₁, ∫⁻ x₃, ∫⁻ x₂, ∫⁻ x₄, g ((x₁, x₃), (x₂, x₄)) ∂μ₄ ∂μ₂ ∂μ₃ ∂μ₁ := by
    rw [lintegral_prod _ hg.aemeasurable]
    have m1 : Measurable (fun x : X₁ × X₃ => ∫⁻ y, g (x, y) ∂(μ₂.prod μ₄)) :=
      Measurable.lintegral_prod_right' (f := fun p : (X₁ × X₃) × (X₂ × X₄) => g p) hg
    rw [lintegral_prod (fun x : X₁ × X₃ => ∫⁻ y, g (x, y) ∂(μ₂.prod μ₄)) m1.aemeasurable]
    refine lintegral_congr fun x₁ => lintegral_congr fun x₃ => ?_
    exact lintegral_prod (fun y : X₂ × X₄ => g ((x₁, x₃), y))
      (hg.comp (by fun_prop)).aemeasurable
  rw [hL, hR]
  refine lintegral_congr fun x₁ => ?_
  refine lintegral_lintegral_swap (f := fun x₂ x₃ => ∫⁻ x₄, g ((x₁, x₃), (x₂, x₄)) ∂μ₄) ?_
  have m2 : Measurable (fun q : X₂ × X₃ => ∫⁻ x₄, g ((x₁, q.2), (q.1, x₄)) ∂μ₄) :=
    Measurable.lintegral_prod_right'
      (f := fun p : (X₂ × X₃) × X₄ => g ((x₁, p.1.2), (p.1.1, p.2))) (hg.comp (by fun_prop))
  exact m2.aemeasurable

/-- `(μ₁ ⊗ μ₂) ⊗ μ₃` and `(μ₁ ⊗ μ₃) ⊗ μ₂` agree under the exchange of the last two
coordinates. -/
theorem prod_right_comm (μ₁ : Measure X₁) (μ₂ : Measure X₂) (μ₃ : Measure X₃)
    [SFinite μ₁] [SFinite μ₂] [SFinite μ₃] :
    ((μ₁.prod μ₂).prod μ₃).map (fun p => ((p.1.1, p.2), p.1.2)) = (μ₁.prod μ₃).prod μ₂ := by
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have me : Measurable (fun p : (X₁ × X₂) × X₃ => ((p.1.1, p.2), p.1.2)) := by fun_prop
  rw [lintegral_map hg me]
  have hL : ∫⁻ p, g ((p.1.1, p.2), p.1.2) ∂((μ₁.prod μ₂).prod μ₃) =
      ∫⁻ x₁, ∫⁻ x₂, ∫⁻ x₃, g ((x₁, x₃), x₂) ∂μ₃ ∂μ₂ ∂μ₁ := by
    rw [lintegral_prod (fun p : (X₁ × X₂) × X₃ => g ((p.1.1, p.2), p.1.2))
      (hg.comp me).aemeasurable]
    have m1 : Measurable (fun x : X₁ × X₂ => ∫⁻ y, g ((x.1, y), x.2) ∂μ₃) :=
      Measurable.lintegral_prod_right'
        (f := fun p : (X₁ × X₂) × X₃ => g ((p.1.1, p.2), p.1.2)) (hg.comp me)
    exact lintegral_prod (fun x : X₁ × X₂ => ∫⁻ y, g ((x.1, y), x.2) ∂μ₃) m1.aemeasurable
  have hR : ∫⁻ p, g p ∂((μ₁.prod μ₃).prod μ₂) =
      ∫⁻ x₁, ∫⁻ x₃, ∫⁻ x₂, g ((x₁, x₃), x₂) ∂μ₂ ∂μ₃ ∂μ₁ := by
    rw [lintegral_prod _ hg.aemeasurable]
    have m1 : Measurable (fun x : X₁ × X₃ => ∫⁻ y, g (x, y) ∂μ₂) :=
      Measurable.lintegral_prod_right' (f := fun p : (X₁ × X₃) × X₂ => g p) hg
    exact lintegral_prod (fun x : X₁ × X₃ => ∫⁻ y, g (x, y) ∂μ₂) m1.aemeasurable
  rw [hL, hR]
  refine lintegral_congr fun x₁ => ?_
  refine lintegral_lintegral_swap (f := fun x₂ x₃ => g ((x₁, x₃), x₂)) ?_
  exact (hg.comp (by fun_prop)).aemeasurable

end rearr

/-! ## The decomposition of a random MLP -/

variable {k m q : ℕ}

/-- The network rebuilt from the hidden matrices `θ`, the centre image `c` and the residual
matrix `M'`: the last matrix is `reb (b θ) c M'`. -/
noncomputable def netOf (b : HidParam k m → Fin m → ℝ) (θ : HidParam k m) (c : Fin q → ℝ)
    (M' : Matrix (Fin q) (Fin m) ℝ) : MlpParam k m q :=
  (θ.1, θ.2, reb (b θ) c M')

/-- The retained data of one network: the two hidden matrices and the image of the centre under
the last matrix. -/
def netRet (b : HidParam k m → Fin m → ℝ) (θ : MlpParam k m q) : HidParam k m × (Fin q → ℝ) :=
  ((θ.1, θ.2.1), θ.2.2.mulVec (b (θ.1, θ.2.1)))

lemma measurable_netRet {b : HidParam k m → Fin m → ℝ} (hb : Measurable b) :
    Measurable (netRet (q := q) b) := by
  have hh : Measurable (fun θ : MlpParam k m q => ((θ.1, θ.2.1) : HidParam k m)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have h2 : Measurable (fun θ : MlpParam k m q => θ.2.2.mulVec (b (θ.1, θ.2.1))) := by
    have := (measurable_mulVec_joint (n := q) (m := m)).comp
      ((measurable_snd.comp measurable_snd).prodMk (hb.comp hh))
    exact this
  exact hh.prodMk h2

/-- The noise form of the retained data and of the network. -/
noncomputable def netPsi (b : HidParam k m → Fin m → ℝ)
    (x : HidParam k m × ((Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ)) :
    (HidParam k m × (Fin q → ℝ)) × MlpParam k m q :=
  ((x.1, cOf (2 / (m : ℝ)) (b x.1) x.2.1),
    netOf b x.1 (cOf (2 / (m : ℝ)) (b x.1) x.2.1) x.2.2)

lemma measurable_netPsi_comp {α : Type*} [MeasurableSpace α]
    {b : α → HidParam k m → Fin m → ℝ} (hb : Measurable (fun p : α × HidParam k m => b p.1 p.2))
    {θ : α → HidParam k m} {ξ : α → Fin q → ℝ} {M : α → Matrix (Fin q) (Fin m) ℝ}
    (hθ : Measurable θ) (hξ : Measurable ξ) (hM : Measurable M) :
    Measurable (fun a => netPsi (b a) (θ a, (ξ a, M a))) := by
  have hb' : Measurable (fun a => b a (θ a)) := hb.comp (measurable_id.prodMk hθ)
  have hc : Measurable (fun a => cOf (2 / (m : ℝ)) (b a (θ a)) (ξ a)) :=
    measurable_cOf_comp _ hb' hξ
  have hr : Measurable (fun a => reb (b a (θ a)) (cOf (2 / (m : ℝ)) (b a (θ a)) (ξ a)) (M a)) :=
    measurable_reb_comp hb' hc hM
  exact (hθ.prodMk hc).prodMk
    ((measurable_fst.comp hθ).prodMk ((measurable_snd.comp hθ).prodMk hr))

/-- **The regression for a random MLP.** `b` is a measurable function of the two hidden matrices
`θ = (M₁, M₂)`. The pair (retained data `(θ, M₃ b(θ))`, all weights) has the distribution of
(`(θ, c)`, `(M₁, M₂, reb (b θ) c M')`) with `c = (√(2/m)·|b(θ)|)·ξ`, where `θ` (two Gaussian
matrices), `ξ` (standard Gaussian vector) and `M'` (Gaussian matrix) are independent. -/
theorem net_split {b : HidParam k m → Fin m → ℝ} (hb : Measurable b) :
    (mlpGauss k m q).map (fun θ => (netRet b θ, θ)) =
      ((hidGauss k m).prod ((stdGauss (Fin q)).prod (gaussMat q m (2 / (m : ℝ))))).map
        (netPsi b) := by
  have e0 : mlpGauss k m q =
      ((hidGauss k m).prod (gaussMat q m (2 / (m : ℝ)))).map MeasurableEquiv.prodAssoc := by
    unfold mlpGauss hidGauss
    rw [Measure.prodAssoc_prod]
  let G : HidParam k m × ((Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ) →
      (HidParam k m × (Fin q → ℝ)) × MlpParam k m q :=
    fun y => ((y.1, y.2.1), (y.1.1, y.1.2, y.2.2))
  have mG : Measurable G := by fun_prop
  have m1 : Measurable (fun p : HidParam k m × Matrix (Fin q) (Fin m) ℝ =>
      (p.1, (p.2.mulVec (b p.1), p.2))) := by
    have := (measurable_mulVec_joint (n := q) (m := m)).comp
      (measurable_snd.prodMk (hb.comp measurable_fst))
    exact measurable_fst.prodMk (this.prodMk measurable_snd)
  have hc : Measurable (fun p : HidParam k m × (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ =>
      cOf (2 / (m : ℝ)) (b p.1) p.2.1) :=
    measurable_cOf_comp _ (hb.comp measurable_fst) (measurable_fst.comp measurable_snd)
  have m2 : Measurable (fun p : HidParam k m × (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ =>
      (p.1, (cOf (2 / (m : ℝ)) (b p.1) p.2.1,
        reb (b p.1) (cOf (2 / (m : ℝ)) (b p.1) p.2.1) p.2.2))) :=
    measurable_fst.prodMk (hc.prodMk (measurable_reb_comp (hb.comp measurable_fst) hc
      (measurable_snd.comp measurable_snd)))
  have hsp := congrArg (Measure.map G)
    (gauss_split_param (q := q) (hidGauss k m) (2 / (m : ℝ)) hb)
  rw [Measure.map_map mG m1, Measure.map_map mG m2] at hsp
  have mL : Measurable (fun θ : MlpParam k m q => (netRet b θ, θ)) :=
    (measurable_netRet hb).prodMk measurable_id
  rw [e0, Measure.map_map mL MeasurableEquiv.prodAssoc.measurable]
  exact hsp

end BstLean.Part157

open BstLean.Part157 in
#print axioms prod4_comm
open BstLean.Part157 in
#print axioms prod_right_comm
open BstLean.Part157 in
#print axioms net_split
