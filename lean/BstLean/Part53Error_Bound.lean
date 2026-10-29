import BstLean.Part53Error_Specialize
import BstLean.Part53Error_Feature

namespace BstLean.Part53

open MeasureTheory
open BstLean.Part41 (Tens Mono phiM frob)
open FloorEnergy FloorCorrection

variable {n d : ℕ}

noncomputable def error53_correction_constant (d k : ℕ) (Λ : ℝ) : ℝ :=
  (k + 1 : ℝ) * ∑ c ∈ Finset.range (k + 1),
    ∑ i ∈ ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0,
      correctionConstant d c i Λ

theorem error53_total_correction (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (hμ : DensLaw n μ Λ)
    (hU : LemmaU53 d) (hS : LemmaS53) (hTr : LemmaTr53)
    (k : ℕ) (f0 : ℝ) (T : Tens n) :
    (∑ c ∈ Finset.range (k + 1),
      ∫ x, kernelErrorSq (d := d) k c (sg n d) (c0 d / BstLean.Part36.DD n d)
        (TF k f0 T) x ∂μ) ≤
      error53_correction_constant d k Λ / (n : ℝ) * Ncirc n d k f0 T := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ ∑ c ∈ Finset.range (k + 1), (k + 1 : ℝ) *
        ∑ i ∈ ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0,
          correctionConstant d c i Λ / (n : ℝ) *
            (frob (Tcirc n d k f0 T (c + 2 * i)) /
              BstLean.Part36.DD n d ^ (c + 2 * i)) := by
      apply Finset.sum_le_sum
      intro c hc
      exact kernel_correction_integral hn hd hμ hU hS hTr k c
        (by have := Finset.mem_range.mp hc; omega) (TF k f0 T)
    _ ≤ ∑ c ∈ Finset.range (k + 1), (k + 1 : ℝ) *
        ∑ i ∈ ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0,
          correctionConstant d c i Λ / (n : ℝ) * Ncirc n d k f0 T := by
      apply Finset.sum_le_sum
      intro c hc
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      have hi0 := (Finset.mem_erase.mp hi).1
      have hik := (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).2
      exact mul_le_mul_of_nonneg_left
        (Ncirc_term_le hn k (c + 2 * i) f0 T (Finset.mem_Icc.mpr ⟨by omega, hik⟩))
        (div_nonneg (correctionConstant_nonneg d c i Λ) hn0.le)
    _ = _ := by
      unfold error53_correction_constant
      simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
      rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul]
      ring

noncomputable def error53_main_energy (μ : Measure (Fin n → ℝ)) (s : ℝ)
    (B : Tens n) (c : ℕ) : ℝ :=
  ∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
    ((∫ x, baseKernel s B ⟨c, a, p⟩ x ∂μ) - error53_target_energy s B c a p) ^ 2

lemma error53_main_energy_formula (μ : Measure (Fin n → ℝ)) (s : ℝ)
    (B : Tens n) (c : ℕ) :
    error53_main_energy (d := d) μ s B c = (c.factorial : ℝ) * s ^ (2 * c) * frob (B c) *
      frob (fun p : Fin c → Mono n d => (∫ x, ∏ t, phiM x (p t) ∂μ) -
        ∏ t, error53_e0 (p t)) := by
  classical
  have hfac := Real.sq_sqrt (Nat.cast_nonneg c.factorial : (0 : ℝ) ≤ c.factorial)
  unfold error53_main_energy baseKernel error53_target_energy
  simp_rw [integral_const_mul]
  have ht (a : Fin c → Fin n) (p : Fin c → Mono n d) :
      (Real.sqrt (c.factorial : ℝ) * s ^ c * B c a * (∫ x, ∏ t, phiM x (p t) ∂μ) -
        Real.sqrt (c.factorial : ℝ) * s ^ c * B c a * ∏ t, error53_e0 (p t)) ^ 2 =
      (c.factorial : ℝ) * s ^ (2 * c) * (B c a) ^ 2 *
        ((∫ x, ∏ t, phiM x (p t) ∂μ) - ∏ t, error53_e0 (p t)) ^ 2 := by
    rw [mul_comm 2 c, pow_mul]
    ring_nf
    rw [hfac]
    ring
  simp_rw [ht, ← Finset.mul_sum]
  simp only [frob, Pi.pow_apply]
  rw [← Finset.sum_mul, ← Finset.mul_sum]


lemma error53_mean_perturbation {μ : Measure (Fin n → ℝ)} (hμ : BstLean.Part40.SphLaw n μ)
    (k c : ℕ) (s v : ℝ) (A : Tens n) :
    (∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
      (∫ x, energyKernel k s A ⟨c, a, p⟩ x -
        error53_target_energy s (heatA k v A) c a p ∂μ) ^ 2) ≤
      2 * (∫ x, kernelErrorSq (d := d) k c s v A x ∂μ) +
        2 * error53_main_energy (d := d) μ s (heatA k v A) c := by
  classical
  letI := hμ.prob
  have he (a : Fin c → Fin n) (p : Fin c → Mono n d) :
      (∫ x, energyKernel k s A ⟨c, a, p⟩ x -
        error53_target_energy s (heatA k v A) c a p ∂μ) =
      (∫ x, energyKernel k s A ⟨c, a, p⟩ x -
        baseKernel s (heatA k v A) ⟨c, a, p⟩ x ∂μ) +
      ((∫ x, baseKernel s (heatA k v A) ⟨c, a, p⟩ x ∂μ) -
        error53_target_energy s (heatA k v A) c a p) := by
    rw [integral_sub (sphere_cont_integrable hμ (energyKernel_continuous _ _ _ _))
      (integrable_const _),
      integral_sub (sphere_cont_integrable hμ (energyKernel_continuous _ _ _ _))
        (sphere_cont_integrable hμ (baseKernel_continuous _ _ _))]
    simp
  have hc (a : Fin c → Fin n) (p : Fin c → Mono n d) :=
    (energyKernel_continuous k s A ⟨c, a, p⟩).sub
      (baseKernel_continuous s (heatA k v A) ⟨c, a, p⟩)
  have hh (a : Fin c → Fin n) (p : Fin c → Mono n d) :
      (∫ x, energyKernel k s A ⟨c, a, p⟩ x -
        error53_target_energy s (heatA k v A) c a p ∂μ) ^ 2 ≤
      2 * (∫ x, (energyKernel k s A ⟨c, a, p⟩ x -
        baseKernel s (heatA k v A) ⟨c, a, p⟩ x) ^ 2 ∂μ) +
      2 * ((∫ x, baseKernel s (heatA k v A) ⟨c, a, p⟩ x ∂μ) -
        error53_target_energy s (heatA k v A) c a p) ^ 2 := by
    rw [he]
    have hj := error53_mean_square hμ _ (hc a p)
    simp only [Pi.pow_apply, Pi.sub_apply] at hj
    nlinarith [sq_nonneg ((∫ x, energyKernel k s A ⟨c, a, p⟩ x -
      baseKernel s (heatA k v A) ⟨c, a, p⟩ x ∂μ) -
      ((∫ x, baseKernel s (heatA k v A) ⟨c, a, p⟩ x ∂μ) -
        error53_target_energy s (heatA k v A) c a p))]
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin c → Fin n)))
    (fun a _ => Finset.sum_le_sum (s := (Finset.univ : Finset (Fin c → Mono n d)))
      (fun p _ => hh a p))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hi (a : Fin c → Fin n) (p : Fin c → Mono n d) : Integrable
      (fun x => (energyKernel k s A ⟨c, a, p⟩ x -
        baseKernel s (heatA k v A) ⟨c, a, p⟩ x) ^ 2) μ :=
    sphere_cont_integrable hμ ((hc a p).pow 2)
  have hint : (∫ x, kernelErrorSq (d := d) k c s v A x ∂μ) =
      ∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
        ∫ x, (energyKernel k s A ⟨c, a, p⟩ x -
          baseKernel s (heatA k v A) ⟨c, a, p⟩ x) ^ 2 ∂μ := by
    unfold kernelErrorSq
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun p _ => hi a p))]
    simp_rw [integral_finsetSum _ (fun p _ => hi _ p)]
  rw [hint]
  exact hs

noncomputable def error53_main_constant (d k : ℕ) (Λ : ℝ) : ℝ :=
  ∑ c ∈ Finset.Icc 1 k, (c.factorial : ℝ) *
    (4 * ((d : ℝ) + 1)) ^ c * (Real.exp Λ * cG d)

lemma error53_main_zero {μ : Measure (Fin n → ℝ)} (hμ : BstLean.Part40.SphLaw n μ)
    (s : ℝ) (B : Tens n) : error53_main_energy (d := d) μ s B 0 = 0 := by
  letI := hμ.prob
  rw [error53_main_energy_formula]
  simp [frob]

lemma error53_main_bound (hn : 1 ≤ n) (hd : 2 ≤ d)
    {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (hμ : DensLaw n μ Λ) (hG : LemmaG53 d)
    (k c : ℕ) (hc : c ∈ Finset.Icc 1 k) (f0 : ℝ) (T : Tens n) :
    error53_main_energy (d := d) μ (sg n d) (Tcirc n d k f0 T) c ≤
      ((c.factorial : ℝ) * (4 * ((d : ℝ) + 1)) ^ c * (Real.exp Λ * cG d)) /
        (n : ℝ) * Ncirc n d k f0 T := by
  have hh := error53_feature_tensor hn hd hμ hG c
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD := BstLean.Part36.DD_pos (d := d) hn
  have hf : 0 ≤ frob (Tcirc n d k f0 T c) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hC : 0 ≤ (c.factorial : ℝ) * (4 * ((d : ℝ) + 1)) ^ c *
      (Real.exp Λ * cG d) := by unfold cG; positivity
  rw [error53_main_energy_formula, sg_pow_even hn c]
  calc
    _ ≤ (c.factorial : ℝ) * (1 / BstLean.Part36.DD n d ^ c) *
        frob (Tcirc n d k f0 T c) *
          ((4 * ((d : ℝ) + 1)) ^ c * (Real.exp Λ * cG d / n)) := by
      exact mul_le_mul_of_nonneg_left hh (by positivity)
    _ = ((c.factorial : ℝ) * (4 * ((d : ℝ) + 1)) ^ c * (Real.exp Λ * cG d)) /
        (n : ℝ) * (frob (Tcirc n d k f0 T c) / BstLean.Part36.DD n d ^ c) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Ncirc_term_le hn k c f0 T hc) (div_nonneg hC hn0.le)

theorem error53_total_main (hn : 1 ≤ n) (hd : 2 ≤ d)
    {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (hμ : DensLaw n μ Λ) (hG : LemmaG53 d)
    (k : ℕ) (f0 : ℝ) (T : Tens n) :
    (∑ c ∈ Finset.range (k + 1), error53_main_energy (d := d) μ (sg n d) (Tcirc n d k f0 T) c) ≤
      error53_main_constant d k Λ / (n : ℝ) * Ncirc n d k f0 T := by
  classical
  have he : (∑ c ∈ Finset.range (k + 1),
      error53_main_energy (d := d) μ (sg n d) (Tcirc n d k f0 T) c) =
      ∑ c ∈ Finset.Icc 1 k, error53_main_energy (d := d) μ (sg n d) (Tcirc n d k f0 T) c := by
    rw [Finset.sum_range_succ', error53_main_zero (FloorMoments.dens_sph hμ), add_zero]
    rw [show Finset.Icc 1 k = Finset.Ico 1 (k + 1) by rfl, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.add_comm 1 i]
  rw [he]
  calc
    _ ≤ ∑ c ∈ Finset.Icc 1 k,
        ((c.factorial : ℝ) * (4 * ((d : ℝ) + 1)) ^ c * (Real.exp Λ * cG d)) /
          (n : ℝ) * Ncirc n d k f0 T :=
      Finset.sum_le_sum (fun c hc => error53_main_bound hn hd hμ hG k c hc f0 T)
    _ = _ := by unfold error53_main_constant; rw [← Finset.sum_mul, ← Finset.sum_div]


theorem error53_normalized_bound (hn : 1 ≤ n) (hd : 2 ≤ d)
    {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (hμ : DensLaw n μ Λ)
    (hU : LemmaU53 d) (hS : LemmaS53) (hG : LemmaG53 d) (hTr : LemmaTr53)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (hT : BstLean.Part41.TSymm k T) :
    (∫ Z, (BstLean.Part43.BofQ μ k f0 T (sg n d • Z) -
      g0 n d k f0 T (sg n d • Z)) ^ 2
      ∂BstLean.Part29.stdGauss (BstLean.Part36.CoefIdxD n d)) ≤
    (2 * error53_correction_constant d k Λ + 2 * error53_main_constant d k Λ) /
      (n : ℝ) * Ncirc n d k f0 T := by
  classical
  rw [error53_error_energy_split hn k f0 T hT (FloorMoments.dens_sph hμ)]
  calc
    _ ≤ ∑ c ∈ Finset.range (k + 1),
        (2 * (∫ x, kernelErrorSq (d := d) k c (sg n d)
          (c0 d / BstLean.Part36.DD n d) (TF k f0 T) x ∂μ) +
        2 * error53_main_energy (d := d) μ (sg n d) (Tcirc n d k f0 T) c) := by
      apply Finset.sum_le_sum
      intro c hc
      exact error53_mean_perturbation (FloorMoments.dens_sph hμ) k c (sg n d)
        (c0 d / BstLean.Part36.DD n d) (TF k f0 T)
    _ = 2 * (∑ c ∈ Finset.range (k + 1),
        ∫ x, kernelErrorSq (d := d) k c (sg n d)
          (c0 d / BstLean.Part36.DD n d) (TF k f0 T) x ∂μ) +
        2 * (∑ c ∈ Finset.range (k + 1),
          error53_main_energy (d := d) μ (sg n d) (Tcirc n d k f0 T) c) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (error53_correction_constant d k Λ / (n : ℝ) * Ncirc n d k f0 T) +
        2 * (error53_main_constant d k Λ / (n : ℝ) * Ncirc n d k f0 T) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (error53_total_correction hn (by omega)
          hμ hU hS hTr k f0 T) (by norm_num))
        (mul_le_mul_of_nonneg_left (error53_total_main hn hd hμ hG k f0 T) (by norm_num))
    _ = _ := by ring

end BstLean.Part53
