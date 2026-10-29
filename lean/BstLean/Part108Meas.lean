import BstLean.Part108Defs

/-!
# Part 108: measurability (`MeasGen108`, `MeasPhi108`, `MeasPsi108`)

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part108

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

instance sfinite_uniformSphere (N : ℕ) : SFinite (uniformSphere N) := by
  unfold uniformSphere
  infer_instance

theorem measGen108 : MeasGen108 := by
  intro N n d k Θ _ w τ Φ hw hτ hΦ
  have hU : Measurable (fun p : Θ × (Fin N → ℝ) => Φ p.1 (sphProj (bwEval (w p.1) p.2))) := by
    have h1 : Measurable (fun p : Θ × (Fin N → ℝ) => sphProj (bwEval (w p.1) p.2)) :=
      measurable_sphProj.comp (measurable_bwEval_comp (hw.comp measurable_fst) measurable_snd)
    exact hΦ.comp (measurable_fst.prodMk h1)
  have hB : Measurable (fun θ : Θ => Bu (w θ) (Φ θ)) := by
    unfold Bu
    exact (hU.stronglyMeasurable.integral_prod_right' (ν := uniformSphere N)).measurable
  refine ⟨?_, hB, ?_⟩
  · unfold BstLean.Part106.gVal BstLean.Part106.standIn
    refine (Finset.measurable_sum _ fun i _ => ?_).div_const _
    have hi : Measurable (fun p : Θ × Draws N n k => p.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    have hm : Measurable (fun p : Θ × Draws N n k => mixW (w p.1) (0 : CoefIdx N n d → ℝ)) :=
      measurable_mixW2.comp ((hw.comp measurable_fst).prodMk measurable_const)
    have h1 : Measurable (fun p : Θ × Draws N n k =>
        sphProj (bwEval (mixW (w p.1) 0) (p.2 i).1 + τ p.1 • (p.2 i).2)) :=
      measurable_sphProj.comp
        ((measurable_bwEval_comp hm (measurable_fst.comp hi)).add
          ((hτ.comp measurable_fst).smul (measurable_snd.comp hi)))
    exact hΦ.comp (measurable_fst.prodMk h1)
  · unfold Vu
    have hV : Measurable (fun p : Θ × (Fin N → ℝ) =>
        (Φ p.1 (sphProj (bwEval (w p.1) p.2)) - Bu (w p.1) (Φ p.1)) ^ 2) :=
      (hU.sub (hB.comp measurable_fst)).pow_const 2
    exact (hV.stronglyMeasurable.integral_prod_right' (ν := uniformSphere N)).measurable

theorem measPhi108 : MeasPhi108 := by
  intro n dA dF
  unfold BstLean.Part106.phiAF
  have h1 : Measurable (fun p : ((CoefIdx n n dA → ℝ) × (CoefIdx n 1 dF → ℝ)) × (Fin n → ℝ) =>
      bwEval p.1.1 p.2) :=
    measurable_bwEval_comp (measurable_fst.comp measurable_fst) measurable_snd
  exact (measurable_pi_apply 0).comp
    (measurable_bwEval_comp (measurable_snd.comp measurable_fst) h1)

theorem measPsi108 : MeasPsi108 := by
  intro n dA dF hd
  unfold psi Htail
  set T := (ℝ × (CoefIdx n n dA → ℝ) × (CoefIdx n 1 dF → ℝ)) × (Fin n → ℝ)
  have hρ : Measurable (fun p : T => p.1.1) := measurable_fst.comp measurable_fst
  have hF : Measurable (fun p : T => p.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hA : Measurable (fun p : T => p.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hy : Measurable (fun p : T => (p.1.1)⁻¹ • bwEval p.1.2.1 p.2) :=
    hρ.inv.smul (measurable_bwEval_comp hA measurable_snd)
  refine hρ.mul (((?_ : Measurable _).sub ((measurable_pi_apply _).comp hF)).sub
    (Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply _).comp hF).mul ((measurable_pi_apply i).comp hy)))
  exact (measurable_pi_apply 0).comp (measurable_bwEval_comp hF hy)

end BstLean.Part108

#print axioms BstLean.Part108.measGen108
#print axioms BstLean.Part108.measPhi108
#print axioms BstLean.Part108.measPsi108
