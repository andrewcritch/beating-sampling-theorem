import BstLean.Part53Floor_Covariance
import BstLean.Part53Floor_Restriction

namespace BstLean.Part53.FloorMoments

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM phiSq varU)
open BstLean.Part53.FloorEnergy (sphere_cont_integrable sphere_var_expansion)

variable {n d : ℕ}

lemma dens_sph {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (h : DensLaw n μ Λ) : SphLaw n μ := by
  obtain ⟨hp, ρ, -, -, hμ, -⟩ := h
  refine ⟨hp, ?_⟩
  rw [hμ]
  exact (withDensity_absolutelyContinuous _ _).ae_le (BstLean.Part29.uniformSphere_ae_sphere n)

lemma density_integral_upper (hn : 1 ≤ n) {μ : Measure (Fin n → ℝ)} {Λ : ℝ}
    (hμ : DensLaw n μ Λ) (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) :
    (∫ x, f x ∂μ) ≤ Real.exp Λ * (∫ x, f x ∂uniformSphere n) := by
  obtain ⟨hp, ρ, hρm, hρ0, hμρ, hρb⟩ := hμ
  have hσ : SphLaw n (uniformSphere n) :=
    ⟨BstLean.Part29.uniformSphere_isProbability n hn, BstLean.Part29.uniformSphere_ae_sphere n⟩
  have hif := sphere_cont_integrable hσ hf
  have hib : Integrable (fun x => Real.exp Λ * f x) (uniformSphere n) := hif.const_mul _
  have hbound : ∀ᵐ x ∂uniformSphere n, ‖f x * ρ x‖ ≤ Real.exp Λ * f x := by
    filter_upwards [hσ.sphere] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 x) (hρ0 x))]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hρb x hx).2 (hf0 x)
  have hiw : Integrable (fun x => f x * ρ x) (uniformSphere n) :=
    hib.mono' (hf.measurable.mul hρm).aestronglyMeasurable hbound
  have hw : (∫ x, f x ∂μ) = ∫ x, f x * ρ x ∂uniformSphere n := by
    rw [hμρ, integral_withDensity_eq_integral_toReal_smul hρm.ennreal_ofReal (by simp)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp [ENNReal.toReal_ofReal (hρ0 x), mul_comm]
  rw [hw, ← integral_const_mul]
  apply integral_mono_ae hiw hib
  filter_upwards [hσ.sphere] with x hx
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hρb x hx).2 (hf0 x)

private lemma continuous_feature_sq : Continuous (fun x : Fin n → ℝ => phiSq d x) := by
  unfold phiSq
  apply continuous_finsetSum
  intro p hp
  have h : Continuous (fun x : Fin n → ℝ => phiM x p) :=
    continuous_multiset_prod p.2.1 (fun i _ => continuous_apply i)
  exact h.pow 2

private lemma continuous_p4 : Continuous (p4 (n := n)) := by
  unfold p4
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i).pow 4)

/-- The squared moments of the heat-parameter deviation are uniformly small. -/
lemma feature_deviation_moment (hn : 1 ≤ n) {μ : Measure (Fin n → ℝ)} {Λ : ℝ}
    (hμ : DensLaw n μ Λ) (hU : LemmaU53 d) (hS : LemmaS53)
    (i : ℕ) (hi : 1 ≤ i) :
    (∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂μ) ≤
      Real.exp Λ * (d : ℝ) ^ (2 * i) *
        (((8 * i - 1).doubleFactorial : ℝ) / (n : ℝ) ^ (2 * i)) := by
  have hf : Continuous (fun x : Fin n → ℝ => (phiSq d x - c0 d) ^ (2 * i)) :=
    (continuous_feature_sq.sub continuous_const).pow _
  have hf0 (x : Fin n → ℝ) : 0 ≤ (phiSq d x - c0 d) ^ (2 * i) := by
    rw [mul_comm 2 i, pow_mul]
    exact sq_nonneg _
  have hσ : SphLaw n (uniformSphere n) :=
    ⟨BstLean.Part29.uniformSphere_isProbability n hn, BstLean.Part29.uniformSphere_ae_sphere n⟩
  have hp4 (x : Fin n → ℝ) : 0 ≤ p4 x := Finset.sum_nonneg (fun j _ => by positivity)
  have hdev : (∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂uniformSphere n) ≤
      (d : ℝ) ^ (2 * i) * (∫ x, p4 x ^ (2 * i) ∂uniformSphere n) := by
    rw [← integral_const_mul]
    apply integral_mono_ae (sphere_cont_integrable hσ hf)
      (sphere_cont_integrable hσ (continuous_const.mul (continuous_p4.pow _)))
    filter_upwards [hσ.sphere] with x hx
    have hb := hU n x hx
    calc
      _ ≤ ((d : ℝ) * p4 x) ^ (2 * i) := pow_le_pow_left₀ hb.1 hb.2 _
      _ = _ := mul_pow _ _ _
  have hs := hS n hn (2 * i) (by omega)
  have hdf : 4 * (2 * i) - 1 = 8 * i - 1 := by omega
  rw [hdf] at hs
  calc
    _ ≤ Real.exp Λ * (∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂uniformSphere n) :=
      density_integral_upper hn hμ _ hf hf0
    _ ≤ Real.exp Λ * ((d : ℝ) ^ (2 * i) * (∫ x, p4 x ^ (2 * i) ∂uniformSphere n)) :=
      mul_le_mul_of_nonneg_left hdev (Real.exp_pos _).le
    _ ≤ Real.exp Λ * ((d : ℝ) ^ (2 * i) *
        (((8 * i - 1).doubleFactorial : ℝ) / (n : ℝ) ^ (2 * i))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (by positivity)) (Real.exp_pos _).le
    _ = _ := by ring

private def linearFeature (hd : 1 ≤ d) (a : Fin n) : Mono n d :=
  ⟨⟨1, by omega⟩, Sym.oneEquiv a⟩

private lemma linearFeature_eval (hd : 1 ≤ d) (a : Fin n) (x : Fin n → ℝ) :
    phiM x (linearFeature hd a) = x a := by
  change (({a} : Multiset (Fin n)).map x).prod = x a
  simp

private lemma linearFeature_injective (hd : 1 ≤ d) :
    Function.Injective (linearFeature (n := n) hd) := by
  classical
  intro a b h
  have he := congrArg (phiM (fun i => if i = a then (1 : ℝ) else 0)) h
  rw [linearFeature_eval, linearFeature_eval] at he
  by_contra hab
  have hba : b ≠ a := Ne.symm hab
  simp [hba] at he

private lemma sum_on_embedding {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) (H : κ → ℝ)
    (h0 : ∀ b, b ∉ Finset.univ.image f → H b = 0) :
    (∑ b, H b) = ∑ a, H (f a) := by
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image f, H b :=
      (Finset.sum_subset (Finset.subset_univ _) (fun b _ hb => h0 b hb)).symm
    _ = _ := Finset.sum_image (fun a _ b _ h => hf h)

/-- Lemma G and the density upper bound control the squared coordinate mean. -/
lemma coordinate_mean_bound53 (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (hμ : DensLaw n μ Λ) (hG : LemmaG53 d) :
    (∑ i : Fin n, (∫ x, x i ∂μ) ^ 2) ≤ Real.exp Λ * cG d / (n : ℝ) := by
  classical
  let β : Fin n → ℝ := fun i => ∫ x, x i ∂μ
  let a : Mono n d → ℝ := Function.extend (linearFeature hd) β (fun _ => 0)
  let q : ℝ := ∑ i, β i ^ 2
  let ℓ : (Fin n → ℝ) → ℝ := fun x => ∑ i, β i * x i
  have hinj := linearFeature_injective (n := n) hd
  have hae (i : Fin n) : a (linearFeature hd i) = β i := hinj.extend_apply β (fun _ => 0) i
  have ha0 (p : Mono n d) (hp : p ∉ Finset.univ.image (linearFeature hd)) : a p = 0 := by
    apply Function.extend_apply'
    simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hp
  have had : a default = 0 := by
    apply ha0
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i hi
    have he := congrArg (fun p : Mono n d => p.1.val) hi
    change 1 = 0 at he
    omega
  have haq : nsq a = q := by
    unfold nsq q
    rw [sum_on_embedding (linearFeature hd) hinj (fun p => a p ^ 2)
      (fun p hp => by rw [ha0 p hp]; norm_num)]
    simp only [hae]
  have hal (x : Fin n → ℝ) : (∑ p, a p * phiM x p) = ℓ x := by
    rw [sum_on_embedding (linearFeature hd) hinj (fun p => a p * phiM x p)
      (fun p hp => by rw [ha0 p hp]; simp)]
    simp only [hae, linearFeature_eval, ℓ]
  have hℓ : Continuous ℓ := continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))
  have hsph := dens_sph hμ
  have hcoord (i : Fin n) : Integrable (fun x : Fin n → ℝ => x i) μ :=
    sphere_cont_integrable hsph (continuous_apply i)
  have hmean : (∫ x, ℓ x ∂μ) = q := by
    dsimp only [ℓ]
    rw [integral_finsetSum _ (fun i _ => (hcoord i).const_mul (β i))]
    simp only [integral_const_mul, β, q, pow_two]
  have hg := hG n hn a had
  simp_rw [hal] at hg
  rw [haq] at hg
  have hupper : (∫ x, ℓ x ^ 2 ∂μ) ≤ (Real.exp Λ * cG d / (n : ℝ)) * q := by
    calc
      _ ≤ Real.exp Λ * (∫ x, ℓ x ^ 2 ∂uniformSphere n) :=
        density_integral_upper hn hμ _ (hℓ.pow 2) (fun x => sq_nonneg _)
      _ ≤ Real.exp Λ * (cG d / (n : ℝ) * q) :=
        mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le
      _ = _ := by ring
  have hv : 0 ≤ varU μ ℓ := integral_nonneg (fun _ => sq_nonneg _)
  rw [sphere_var_expansion hsph ℓ hℓ, hmean] at hv
  have hq : 0 ≤ q := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hη : 0 ≤ Real.exp Λ * cG d / (n : ℝ) := by unfold cG; positivity
  change q ≤ _
  by_cases hz : q = 0
  · rw [hz]; exact hη
  · have hp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
    nlinarith

end BstLean.Part53.FloorMoments
