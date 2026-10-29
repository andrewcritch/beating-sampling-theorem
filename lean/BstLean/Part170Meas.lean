import BstLean.Part169All

/-!
# Part 170 (file `Meas`): the exact-rule errors at the nodes, and their measurability

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, the exact Gaussian-rule errors `Δ_f^exact`, `Δ_ω^exact` at a node
(the split before Lemma `t7:p08:fl`).

* `exFn c g = n(f̄(s_g) − f_G(s_g))`, `exWn c g = n(ω̄(s_g) − ω_G(s_g))`: the exact-rule errors at
  the node `s_g`; `exF c a = exFn c g(a)` (`exF_eq`).
* `mkR wr θ`: the retained value with World data `wr`, Agent hidden matrices `θ`, `c_A = 0` and
  `F = 0`. The errors read only `wr` and `θ` (`exF_mkR`, `exW_mkR`: `rfl`).
* `measurable_exFn_comp`, `measurable_exWn_comp`, **`measurable_exF_joint`**,
  **`measurable_exW_joint`**: joint measurability in the retained value and the index.
-/

namespace BstLean.Part170

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part53 (unitF53 measurable_unitF)
open BstLean.Part136 (HidParam)

variable {n : ℕ}

/-- The exact-rule location error `n(f̄(s_g) − f_G(s_g))` at the node `s_g`. -/
noncomputable def exFn (c : Ret n) (g : ℕ) : ℝ :=
  (n : ℝ) * (fbarS c (nodeS c g) - fGauss c (nodeS c g))

/-- The exact-rule energy error `n(ω̄(s_g) − ω_G(s_g))` at the node `s_g`. -/
noncomputable def exWn (c : Ret n) (g : ℕ) : ℝ :=
  (n : ℝ) * (wbarS c (nodeS c g) - wGauss c (nodeS c g))

lemma exF_eq (c : Ret n) (a : Ix n) : exF c a = exFn c (gIdx c (latC (paperDesignP n) c a)) := rfl

lemma exW_eq (c : Ret n) (a : Ix n) : exW c a = exWn c (gIdx c (latC (paperDesignP n) c a)) := rfl

/-- The retained value with World data `wr` and Agent hidden matrices `θ` (`c_A = 0`, `F = 0`). -/
noncomputable def mkR (wr : WRet n) (θ : AHid n) : Ret n := (wr, ((θ, 0), 0))

lemma measurable_mkR : Measurable (fun p : WRet n × AHid n => mkR p.1 p.2) :=
  measurable_fst.prodMk ((measurable_snd.prodMk measurable_const).prodMk measurable_const)

/-- The errors read only the World data and the Agent hidden matrices. -/
lemma exF_mkR (c : Ret n) (a : Ix n) : exF (mkR c.1 c.2.1.1) a = exF c a := rfl

lemma exW_mkR (c : Ret n) (a : Ix n) : exW (mkR c.1 c.2.1.1) a = exW c a := rfl

/-! ## Measurability -/

lemma measurable_fX_comp {β : Type*} [MeasurableSpace β] {C : β → Ret n} {y : β → Fin n → ℝ}
    (hC : Measurable C) (hy : Measurable y) : Measurable (fun x => fX (C x) (y x)) := by
  unfold fX
  have hθ : Measurable (fun x => ((C x).2.1.1 : HidParam n (mA n))) :=
    measurable_fst.comp (measurable_fst.comp (measurable_snd.comp hC))
  have hh : Measurable (fun x => hid2 (A1 (C x)) (A2 (C x)) (y x)) :=
    BstLean.Part166.continuous_hid2_joint.measurable.comp (hθ.prodMk hy)
  have hb : Measurable (fun x => bR (C x)) := measurable_bR.comp hC
  exact (Finset.measurable_sum _ fun j _ => ((measurable_pi_apply j).comp hh).mul
    ((measurable_pi_apply j).comp hb)).div
    (measurable_const.mul ((continuous_normSq.measurable.comp hb).sqrt))

lemma measurable_wX_comp {β : Type*} [MeasurableSpace β] {C : β → Ret n} {y : β → Fin n → ℝ}
    (hC : Measurable C) (hy : Measurable y) : Measurable (fun x => wX (C x) (y x)) := by
  unfold wX
  have hθ : Measurable (fun x => ((C x).2.1.1 : HidParam n (mA n))) :=
    measurable_fst.comp (measurable_fst.comp (measurable_snd.comp hC))
  have hh : Measurable (fun x => hid2 (A1 (C x)) (A2 (C x)) (y x)) :=
    BstLean.Part166.continuous_hid2_joint.measurable.comp (hθ.prodMk hy)
  exact (continuous_normSq.measurable.comp hh).div_const _

lemma measurable_fbarS_comp {β : Type*} [MeasurableSpace β] {C : β → Ret n} {f : β → ℝ}
    (hC : Measurable C) (hf : Measurable f) : Measurable (fun x => fbarS (C x) (f x)) := by
  unfold fbarS
  exact measurable_int_dir (measurable_fX_comp (hC.comp measurable_fst)
    (measurable_xLat_joint (hC.comp measurable_fst) (hf.comp measurable_fst)
      (measurable_unitF.comp measurable_snd)))

lemma measurable_wbarS_comp {β : Type*} [MeasurableSpace β] {C : β → Ret n} {f : β → ℝ}
    (hC : Measurable C) (hf : Measurable f) : Measurable (fun x => wbarS (C x) (f x)) := by
  unfold wbarS
  exact measurable_int_dir (measurable_wX_comp (hC.comp measurable_fst)
    (measurable_xLat_joint (hC.comp measurable_fst) (hf.comp measurable_fst)
      (measurable_unitF.comp measurable_snd)))

lemma measurable_g2 : Measurable (fun p : ℝ × ℝ =>
    ∫ z, relu (p.1 + p.2 * z) ^ 2 ∂gaussianReal 0 1) := by
  have hF : Measurable (fun q : (ℝ × ℝ) × ℝ => relu (q.1.1 + q.1.2 * q.2) ^ 2) :=
    ((continuous_relu.comp (by fun_prop)).pow 2).measurable
  exact hF.stronglyMeasurable.integral_prod_right'.measurable

lemma measurable_fGauss_comp {β : Type*} [MeasurableSpace β] {C : β → Ret n} {f : β → ℝ}
    (hC : Measurable C) (hf : Measurable f) : Measurable (fun x => fGauss (C x) (f x)) := by
  unfold fGauss
  have hb : Measurable (fun x => bR (C x)) := measurable_bR.comp hC
  refine (Finset.measurable_sum _ fun j _ => ?_).div
    (measurable_const.mul ((continuous_normSq.measurable.comp hb).sqrt))
  exact (BstLean.Part137.measurable_psiS.comp ((measurable_vsig2_comp hC hf).sqrt.prodMk
    (measurable_A2a hC hf j))).mul ((measurable_pi_apply j).comp hb)

lemma measurable_wGauss_comp {β : Type*} [MeasurableSpace β] {C : β → Ret n} {f : β → ℝ}
    (hC : Measurable C) (hf : Measurable f) : Measurable (fun x => wGauss (C x) (f x)) := by
  unfold wGauss
  refine (Finset.measurable_sum _ fun j _ => ?_).div_const _
  exact measurable_g2.comp ((measurable_A2a hC hf j).prodMk (measurable_vsig2_comp hC hf).sqrt)

lemma measurable_nodeS_comp {β : Type*} [MeasurableSpace β] {C : β → Ret n} {g : β → ℕ}
    (hC : Measurable C) (hg : Measurable g) : Measurable (fun x => nodeS (C x) (g x)) := by
  unfold nodeS nodeD
  exact (measurable_nodeL.comp hC).add ((((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp hg).add measurable_const).mul
    (((measurable_nodeH.comp hC).sub (measurable_nodeL.comp hC)).div_const _))

lemma measurable_exFn_comp {β : Type*} [MeasurableSpace β] {C : β → Ret n} {g : β → ℕ}
    (hC : Measurable C) (hg : Measurable g) : Measurable (fun x => exFn (C x) (g x)) := by
  unfold exFn
  have hs := measurable_nodeS_comp hC hg
  exact ((measurable_fbarS_comp hC hs).sub (measurable_fGauss_comp hC hs)).const_mul _

lemma measurable_exWn_comp {β : Type*} [MeasurableSpace β] {C : β → Ret n} {g : β → ℕ}
    (hC : Measurable C) (hg : Measurable g) : Measurable (fun x => exWn (C x) (g x)) := by
  unfold exWn
  have hs := measurable_nodeS_comp hC hg
  exact ((measurable_wbarS_comp hC hs).sub (measurable_wGauss_comp hC hs)).const_mul _

lemma measurable_gIdx_joint {β : Type*} [MeasurableSpace β] {C : β → Ret n} {a : β → Ix n}
    (hC : Measurable C) (ha : Measurable a) :
    Measurable (fun x => gIdx (C x) (latC (paperDesignP n) (C x) (a x))) := by
  unfold gIdx latC
  refine measurable_nodeIdx_comp (Js n) (measurable_nodeL.comp hC) (measurable_nodeH.comp hC) ?_
  refine measurable_latitude_comp ?_ ((paperDesignP n).mtau0.comp hC) ha
  exact (continuous_normSq.measurable.comp (measurable_snd.comp (measurable_fst.comp hC))).sqrt

/-- **Joint measurability of the exact-rule location error.** -/
lemma measurable_exF_joint {β : Type*} [MeasurableSpace β] {C : β → Ret n} {a : β → Ix n}
    (hC : Measurable C) (ha : Measurable a) : Measurable (fun x => exF (C x) (a x)) :=
  measurable_exFn_comp hC (measurable_gIdx_joint hC ha)

/-- **Joint measurability of the exact-rule energy error.** -/
lemma measurable_exW_joint {β : Type*} [MeasurableSpace β] {C : β → Ret n} {a : β → Ix n}
    (hC : Measurable C) (ha : Measurable a) : Measurable (fun x => exW (C x) (a x)) :=
  measurable_exWn_comp hC (measurable_gIdx_joint hC ha)

end BstLean.Part170
