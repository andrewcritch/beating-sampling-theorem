import BstLean.Part53Floor_Correction
import BstLean.Part53Floor_Restriction

namespace BstLean.Part53.FloorAssembly

open MeasureTheory
open BstLean.Part41 (varU frob Tens Mono phiM)
open FloorEnergy FloorCorrection

variable {n d : ℕ}

lemma variance_perturbation {μ : Measure (Fin n → ℝ)} (hμ : BstLean.Part40.SphLaw n μ)
    (f g : (Fin n → ℝ) → ℝ) (hf : Continuous f) (hg : Continuous g) :
    varU μ g / 2 - (∫ x, (f x - g x) ^ 2 ∂μ) ≤ varU μ f := by
  letI := hμ.prob
  have hi := sphere_cont_integrable hμ hf
  have hj := sphere_cont_integrable hμ hg
  have he : (∫ x, (f x - g x) ∂μ) = (∫ x, f x ∂μ) - ∫ x, g x ∂μ :=
    integral_sub hi hj
  have hp (x : Fin n → ℝ) :
      (g x - ∫ y, g y ∂μ) ^ 2 / 2 -
        ((f x - g x) - ∫ y, (f y - g y) ∂μ) ^ 2 ≤
          (f x - ∫ y, f y ∂μ) ^ 2 := by
    have hh := floor_quadratic_correction53
      (g x - ∫ y, g y ∂μ) ((f x - g x) - ∫ y, (f y - g y) ∂μ)
    rw [he] at hh
    rw [he]
    convert hh using 1 <;> ring
  have hgc : Continuous (fun x => (g x - ∫ y, g y ∂μ) ^ 2) :=
    (hg.sub continuous_const).pow 2
  have hec : Continuous (fun x => ((f x - g x) - ∫ y, (f y - g y) ∂μ) ^ 2) :=
    ((hf.sub hg).sub continuous_const).pow 2
  have hfc : Continuous (fun x => (f x - ∫ y, f y ∂μ) ^ 2) :=
    (hf.sub continuous_const).pow 2
  have hh := integral_mono
    (sphere_cont_integrable hμ (hgc.div_const 2 |>.sub hec))
    (sphere_cont_integrable hμ hfc) hp
  dsimp only [Pi.sub_apply] at hh
  rw [integral_sub (sphere_cont_integrable hμ (hgc.div_const 2))
    (sphere_cont_integrable hμ hec), integral_div] at hh
  change varU μ g / 2 - varU μ (fun x => f x - g x) ≤ varU μ f at hh
  have hex := sphere_var_expansion hμ (fun x => f x - g x) (hf.sub hg)
  rw [hex] at hh
  nlinarith only [hh, sq_nonneg (∫ x, (f x - g x) ∂μ)]

lemma kernel_variance_perturbation {μ : Measure (Fin n → ℝ)}
    (hμ : BstLean.Part40.SphLaw n μ) (k c : ℕ) (s v : ℝ) (A : Tens n) :
    (∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
      varU μ (baseKernel s (heatA k v A) ⟨c, a, p⟩)) / 2 -
      (∫ x, kernelErrorSq (d := d) k c s v A x ∂μ) ≤
    ∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
      varU μ (energyKernel k s A ⟨c, a, p⟩) := by
  classical
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin c → Fin n)))
    (fun a _ => Finset.sum_le_sum (s := (Finset.univ : Finset (Fin c → Mono n d)))
      (fun p _ => variance_perturbation hμ
        (energyKernel k s A ⟨c, a, p⟩) (baseKernel s (heatA k v A) ⟨c, a, p⟩)
        (energyKernel_continuous _ _ _ _) (baseKernel_continuous _ _ _)))
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div] at hh
  have he : (∫ x, kernelErrorSq (d := d) k c s v A x ∂μ) =
      ∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
        ∫ x, (energyKernel k s A ⟨c, a, p⟩ x -
          baseKernel s (heatA k v A) ⟨c, a, p⟩ x) ^ 2 ∂μ := by
    unfold kernelErrorSq
    have hI (a : Fin c → Fin n) (p : Fin c → Mono n d) : Integrable
        (fun x => (energyKernel k s A ⟨c, a, p⟩ x -
          baseKernel s (heatA k v A) ⟨c, a, p⟩ x) ^ 2) μ :=
      sphere_cont_integrable hμ (((energyKernel_continuous k s A ⟨c, a, p⟩).sub
        (baseKernel_continuous s (heatA k v A) ⟨c, a, p⟩)).pow 2)
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun p _ => hI a p))]
    simp_rw [integral_finsetSum _ (fun p _ => hI _ p)]
  rw [he]
  exact hh

lemma positive_energy_le_total (μ : Measure (Fin n → ℝ)) (k : ℕ) (s : ℝ) (A : Tens n) :
    (∑ c ∈ Finset.Icc 1 k, ∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
      varU μ (energyKernel k s A ⟨c, a, p⟩)) ≤
        ∑ i ∈ energySet n d k, varU μ (energyKernel k s A i) := by
  classical
  unfold energySet
  rw [Finset.sum_sigma]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro c hc
    have := (Finset.mem_Icc.mp hc).2
    exact Finset.mem_range.mpr (by omega)
  · intro c hc hnot
    exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg
      (fun p _ => integral_nonneg (fun _ => sq_nonneg _)))

end BstLean.Part53.FloorAssembly
