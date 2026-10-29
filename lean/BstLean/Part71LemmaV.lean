import BstLean.Part59LemmaV
import BstLean.Part71Error

/-!
# Part 71: Lemma V under a chi-square bound

A copy of `Part63LemmaV.lean`. Change: the kernel-correction term is bounded on `μ` directly by
`kernel_correction_W` with the chi-square trace-moment weight `wChi K` (`devW_chi`), in place of the
density transfer `up_integral59x`. The inner sum keeps the filter `c + 2i ≤ k`.
`lemmaV71` proves `LemmaV71 d k K (CV71 d k K) 1`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part71

open BstLean.Part59

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM contr trL frob IsSymmT Tens TSymm fval Pn varU sdU heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (sg c0 aH g0 heatA fvA Ncirc LemmaR53 GaussPolar53)

variable {n d : ℕ}

open BstLean.Part53
open BstLean.Part53.FloorEnergy BstLean.Part53.FloorCorrection

private lemma nc_nonneg59x (hn : 1 ≤ n) (k : ℕ) (A : Tens n) :
    0 ≤ NcA n d k A := by
  apply Finset.sum_nonneg
  intro c hc
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (pow_nonneg (BstLean.Part36.DD_pos (d := d) hn).le _)

private lemma nc_term59x (hn : 1 ≤ n) (k j : ℕ) (A : Tens n)
    (hj : j ∈ Finset.Icc 1 k) :
    frob (heatA k (c0 d / DD n d) A j) / DD n d ^ j ≤ NcA n d k A := by
  apply Finset.single_le_sum _ hj
  intro c hc
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (pow_nonneg (BstLean.Part36.DD_pos (d := d) hn).le _)

private lemma error_bound71 (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} {K : ℝ} (hμ : ChiLaw n μ K)
    (k c : ℕ) (hc : c ≤ k) (A : Tens n) :
    (∫ x, kernelErrorSq (d := d) k c (sg n d) (c0 d / DD n d) A x ∂μ) ≤
      (k + 1 : ℝ) * (∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k), corrW d c i (wChi K)) * NcA n d k A := by
  classical
  let S := ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0
  have hN := nc_nonneg59x (d := d) hn k A
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hC (i : ℕ) : 0 ≤ corrW d c i (wChi K) := corrW_nonneg _ _ _ _ (wChi_nonneg K)
  have hb := kernel_correction_W hn hd (chiLaw_sph hμ) (wChi_nonneg K) (devW_chi hn hμ)
    lemmaTr53 k c hc A
  calc
    _ ≤ (k + 1 : ℝ) * ∑ i ∈ S, corrW d c i (wChi K) / (n : ℝ) *
        (frob (heatA k (c0 d / DD n d) A (c + 2 * i)) / DD n d ^ (c + 2 * i)) := hb
    _ ≤ (k + 1 : ℝ) * ∑ i ∈ S, corrW d c i (wChi K) * NcA n d k A := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      have hi0 := (Finset.mem_erase.mp hi).1
      have hi' := (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).2
      have hj : c + 2 * i ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega, hi'⟩
      have hdiv : corrW d c i (wChi K) / (n : ℝ) ≤ corrW d c i (wChi K) :=
        div_le_self (hC i) hnR
      exact (mul_le_mul_of_nonneg_left (nc_term59x hn k _ A hj)
        (div_nonneg (hC i) (by positivity))).trans
          (mul_le_mul_of_nonneg_right hdiv hN)
    _ ≤ _ := by
      rw [← Finset.sum_mul, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hN
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact (Finset.mem_erase.mp hi).2
      · intro i hi hnot; exact hC i

private lemma base_bound59x (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} (hμ : BstLean.Part40.SphLaw n μ)
    (k c : ℕ) (hc : c ≤ k) (A : Tens n) :
    (∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
      varU μ (baseKernel (sg n d) (heatA k (c0 d / DD n d) A) ⟨c, a, p⟩)) ≤
      (c.factorial : ℝ) * ((d : ℝ) + 1) ^ c * NcA n d k A := by
  classical
  let := hμ.prob
  let B := heatA k (c0 d / DD n d) A
  cases c with
  | zero =>
    simp [baseKernel, varU, nc_nonneg59x hn k A]
  | succ c =>
    have hj : c + 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega, hc⟩
    have hsecond : (∑ a : Fin (c + 1) → Fin n, ∑ p : Fin (c + 1) → Mono n d,
        varU μ (baseKernel (sg n d) B ⟨c + 1, a, p⟩)) ≤
        (∫ x, ((c + 1).factorial : ℝ) * sg n d ^ (2 * (c + 1)) *
          frob (B (c + 1)) * BstLean.Part41.phiSq d x ^ (c + 1) ∂μ) := by
      have hv (a : Fin (c + 1) → Fin n) (p : Fin (c + 1) → Mono n d) :=
        sphere_var_expansion hμ (baseKernel (sg n d) B ⟨c + 1, a, p⟩)
          (baseKernel_continuous _ _ _)
      calc
        _ ≤ ∑ a : Fin (c + 1) → Fin n, ∑ p : Fin (c + 1) → Mono n d,
            ∫ x, baseKernel (sg n d) B ⟨c + 1, a, p⟩ x ^ 2 ∂μ := by
          apply Finset.sum_le_sum; intro a ha
          apply Finset.sum_le_sum; intro p hp
          rw [hv a p]; exact sub_le_self _ (sq_nonneg _)
        _ = _ := by
          have hi (a : Fin (c + 1) → Fin n) (p : Fin (c + 1) → Mono n d) :
              Integrable (fun x => baseKernel (sg n d) B ⟨c + 1, a, p⟩ x ^ 2) μ :=
            sphere_cont_integrable hμ ((baseKernel_continuous _ _ _).pow 2)
          simp_rw [← integral_finsetSum _ (fun p _ =>
            hi _ p)]
          rw [← integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun p _ => hi a p))]
          apply integral_congr_ae
          filter_upwards [] with x
          unfold baseKernel
          simp only [mul_pow]
          rw [Real.sq_sqrt (Nat.cast_nonneg _)]
          simp_rw [← Finset.mul_sum, feature_tensor_sq]
          rw [← pow_mul, mul_comm (c + 1) 2]
          unfold frob
          rw [Finset.mul_sum, Finset.sum_mul]
    have hbound : (∫ x, ((c + 1).factorial : ℝ) * sg n d ^ (2 * (c + 1)) *
        frob (B (c + 1)) * BstLean.Part41.phiSq d x ^ (c + 1) ∂μ) ≤
        ((c + 1).factorial : ℝ) * ((d : ℝ) + 1) ^ (c + 1) *
          (frob (B (c + 1)) / DD n d ^ (c + 1)) := by
      have heconst : ((c + 1).factorial : ℝ) * ((d : ℝ) + 1) ^ (c + 1) *
          (frob (B (c + 1)) / DD n d ^ (c + 1)) =
          ∫ _x : Fin n → ℝ, ((c + 1).factorial : ℝ) * ((d : ℝ) + 1) ^ (c + 1) *
          (frob (B (c + 1)) / DD n d ^ (c + 1)) ∂μ := by simp
      rw [heconst]
      apply integral_mono_ae
        (sphere_cont_integrable hμ (continuous_const.mul (phiSq_continuous.pow _)))
        (integrable_const _)
      filter_upwards [hμ.sphere] with x hx
      have hphi := BstLean.Part43.phiSq_bounds hd x hx
      have hfrob : 0 ≤ frob (B (c + 1)) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hsg : 0 ≤ sg n d ^ (2 * (c + 1)) := by
        rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
      have hh := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith [hphi.1]) hphi.2 (c + 1))
        (show 0 ≤ ((c + 1).factorial : ℝ) * sg n d ^ (2 * (c + 1)) *
          frob (B (c + 1)) from mul_nonneg
            (mul_nonneg (Nat.cast_nonneg _) hsg) hfrob)
      dsimp only [Pi.mul_apply, Pi.pow_apply]
      rw [sg_pow_even hn]
      rw [sg_pow_even hn] at hh
      convert hh using 1; ring
    exact hsecond.trans (hbound.trans (mul_le_mul_of_nonneg_left
      (nc_term59x hn k _ A hj) (by positivity)))

/-- The summand of the Lemma V constant. -/
noncomputable def LV71 (d k : ℕ) (K : ℝ) (c : ℕ) : ℝ := 2 * ((c.factorial : ℝ) * ((d : ℝ) + 1) ^ c) +
    2 * ((k + 1 : ℝ) * ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k), corrW d c i (wChi K))

/-- **The Lemma V constant** `C_V = Σ_{c ≤ k} [2c!(d+1)^c + 2(k+1)Σ_{i ≥ 0, c+2i ≤ k} corr^χ(d,c,i)]`. -/
noncomputable def CV71 (d k : ℕ) (K : ℝ) : ℝ := ∑ c ∈ Finset.range (k + 1), LV71 d k K c

/-- **Lemma V under a chi-square bound.** -/
theorem lemmaV71 (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (K : ℝ) :
    LemmaV71 d k K (CV71 d k K) 1 := by
  classical
  let L (c : ℕ) : ℝ := LV71 d k K c
  show LemmaV71 d k K (∑ c ∈ Finset.range (k + 1), L c) 1
  intro n hn μ hμ A hA
  have hsph := chiLaw_sph hμ
  have he := gaussian_variance_energy53 (d := d) k (sg n d) A hA (lemmaW53 k) hsph
  have hmap (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
      mapMD (sg n d • Z) x = sg n d • linZ Z (fun p => phiM x p) := by
    rw [mapMD_linZ]
    funext a
    simp only [linZ, colM, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  simp_rw [← hmap] at he
  refine ⟨he.1, ?_⟩
  rw [he.2]
  unfold energySet
  rw [Finset.sum_sigma]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro c hc
  have hck : c ≤ k := by have := Finset.mem_range.mp hc; omega
  let B := heatA k (c0 d / DD n d) A
  have hpert : (∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
      varU μ (energyKernel k (sg n d) A ⟨c, a, p⟩)) ≤
      2 * (∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
        varU μ (baseKernel (sg n d) B ⟨c, a, p⟩)) +
      2 * (∫ x, kernelErrorSq (d := d) k c (sg n d) (c0 d / DD n d) A x ∂μ) := by
    have hp (a : Fin c → Fin n) (p : Fin c → Mono n d) :=
      FloorAssembly.variance_perturbation hsph
        (baseKernel (sg n d) B ⟨c, a, p⟩)
        (energyKernel k (sg n d) A ⟨c, a, p⟩)
        (baseKernel_continuous _ _ _) (energyKernel_continuous _ _ _ _)
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin c → Fin n)))
      (fun a _ => Finset.sum_le_sum (s := (Finset.univ : Finset (Fin c → Mono n d)))
        (fun p _ => hp a p))
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div] at hh
    have hi (a : Fin c → Fin n) (p : Fin c → Mono n d) : Integrable
        (fun x => (baseKernel (sg n d) B ⟨c, a, p⟩ x -
          energyKernel k (sg n d) A ⟨c, a, p⟩ x) ^ 2) μ :=
      sphere_cont_integrable hsph (((baseKernel_continuous _ _ _).sub
        (energyKernel_continuous _ _ _ _)).pow 2)
    have hi' : (∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
        ∫ x, (baseKernel (sg n d) B ⟨c, a, p⟩ x -
          energyKernel k (sg n d) A ⟨c, a, p⟩ x) ^ 2 ∂μ) =
        ∫ x, kernelErrorSq (d := d) k c (sg n d) (c0 d / DD n d) A x ∂μ := by
      simp_rw [← integral_finsetSum _ (fun p _ => hi _ p)]
      rw [← integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun p _ => hi a p))]
      apply integral_congr_ae
      filter_upwards [] with x
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [B]
      ring
    rw [hi'] at hh
    linarith
  have hb := base_bound59x hn hd hsph k c hck A
  have herr := error_bound71 hn hd hμ k c hck A
  calc
    _ ≤ _ := hpert
    _ ≤ 2 * ((c.factorial : ℝ) * ((d : ℝ) + 1) ^ c * NcA n d k A) +
        2 * ((k + 1 : ℝ) *
          (∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k), corrW d c i (wChi K)) * NcA n d k A) := by
      linarith
    _ = L c * NcA n d k A := by dsimp [L, LV71]; ring

end BstLean.Part71
