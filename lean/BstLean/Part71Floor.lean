import BstLean.Part71Iface
import BstLean.Part71Transfer
import BstLean.Part71Error
import BstLean.Part59Floor

/-!
# Part 71: Prop F under a chi-square bound, with its explicit threshold

A copy of `Part63Floor.lean`. Changes: the hypothesis is `ChiLaw n μ K`; the coordinate mean is
`Σ_i (E_μ x_i)² ≤ (1+|K|)·cG 2/n` (`chi_coord_mean`, no density bound); the correction constant is
`totW d k [1,k] (wChi K)` (`total_correction_W` with `chi_dev`). The threshold is
`nF71 d k K = ⌊max(2E, 8C_F) + 1⌋₊ + 1`, `E = (1+|K|)·cG 2`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part71

open BstLean.Part59

open BstLean.Part53

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT Tens TSymm fval In41 Pn heavyCount)
open BstLean.Part43 (BofQ varFQ)

variable {n d : ℕ}

private lemma floor_feature_variance (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (hμ : ChiLaw n μ Λ) :
    1 - (1 + |Λ|) * cG 2 / (n : ℝ) ≤
      ∑ p : Mono n d, BstLean.Part41.varU μ (fun x => phiM x p) := by
  have hsph := chiLaw_sph hμ
  let := hsph.prob
  have hc (i : Fin n) : Integrable (fun x : Fin n → ℝ => x i) μ :=
    FloorEnergy.sphere_cont_integrable hsph (continuous_apply i)
  have hc2 (i : Fin n) : Integrable (fun x : Fin n → ℝ => x i ^ 2) μ :=
    FloorEnergy.sphere_cont_integrable hsph ((continuous_apply i).pow 2)
  calc
    _ ≤ 1 - ∑ i : Fin n, (∫ x, x i ∂μ) ^ 2 :=
      sub_le_sub_left (chi_coord_mean hn (chiLaw_abs hμ)) 1
    _ = ∑ i : Fin n, BstLean.Part41.varU μ (fun x => x i) :=
      (sphere_coordinate_variance53 μ hsph.sphere hc hc2).symm
    _ ≤ _ := raw_feature_coordinate_variance53 μ hd

private lemma floor_fixed_tensor_variance (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (hμ : ChiLaw n μ Λ)
    (c : ℕ) (A : (Fin (c + 1) → Fin n) → ℝ) :
    frob A * (1 - (1 + |Λ|) * cG 2 / (n : ℝ)) ≤
      ∑ a : Fin (c + 1) → Fin n, ∑ p : Fin (c + 1) → Mono n d,
        BstLean.Part41.varU μ (fun x => A a * ∏ t, phiM x (p t)) := by
  calc
    _ ≤ frob A * (∑ p : Mono n d, BstLean.Part41.varU μ (fun x => phiM x p)) :=
      mul_le_mul_of_nonneg_left (floor_feature_variance hn hd hμ)
        (Finset.sum_nonneg (fun a _ => sq_nonneg _))
    _ ≤ _ := tensor_coefficient_variance_floor53 μ (fun x p => phiM x p) A default
      phiM_default_floor53 c

private lemma floor_positive_tensor_variance (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (hμ : ChiLaw n μ Λ)
    (c : ℕ) (hc : 1 ≤ c) (A : (Fin c → Fin n) → ℝ) :
    frob A * (1 - (1 + |Λ|) * cG 2 / (n : ℝ)) ≤
      ∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
        BstLean.Part41.varU μ (fun x => A a * ∏ t, phiM x (p t)) := by
  cases c with
  | zero => omega
  | succ c => exact floor_fixed_tensor_variance hn hd hμ c A

private lemma floor_base_energy (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (hμ : ChiLaw n μ Λ)
    (hsmall : (1 + |Λ|) * cG 2 / (n : ℝ) ≤ 1) (k : ℕ) (f0 : ℝ) (T : Tens n) :
    (1 - (1 + |Λ|) * cG 2 / (n : ℝ)) * Ncirc n d k f0 T ≤
      ∑ c ∈ Finset.Icc 1 k, ∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
        BstLean.Part41.varU μ
          (FloorCorrection59x.baseKernel (sg n d) (Tcirc n d k f0 T) ⟨c, a, p⟩) := by
  classical
  unfold Ncirc
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c hc
  let B := Tcirc n d k f0 T c
  let A := fun a : Fin c → Fin n => Real.sqrt (c.factorial : ℝ) * sg n d ^ c * B a
  have hnorm : frob A = (c.factorial : ℝ) * (1 / DD n d ^ c) * frob B := by
    unfold frob A
    simp_rw [mul_pow, ← Finset.mul_sum]
    rw [Real.sq_sqrt (Nat.cast_nonneg c.factorial)]
    have hs : (sg n d ^ c) ^ 2 = 1 / DD n d ^ c := by
      rw [← pow_mul, mul_comm c 2]
      exact FloorCorrection59x.sg_pow_even hn c
    rw [hs]
  have hh := floor_positive_tensor_variance hn hd hμ c (Finset.mem_Icc.mp hc).1 A
  have he : (∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
      BstLean.Part41.varU μ (fun x => A a * ∏ t, phiM x (p t))) =
      ∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
        BstLean.Part41.varU μ
          (FloorCorrection59x.baseKernel (sg n d) (Tcirc n d k f0 T) ⟨c, a, p⟩) := rfl
  rw [he, hnorm] at hh
  have hfac : (1 : ℝ) ≤ c.factorial := by exact_mod_cast Nat.factorial_pos c
  have hD := BstLean.Part36.DD_pos (d := d) hn
  have hB : 0 ≤ frob B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb := mul_le_mul_of_nonneg_right hfac
    (show 0 ≤ (1 - (1 + |Λ|) * cG 2 / (n : ℝ)) * (frob B / DD n d ^ c) from
      mul_nonneg (sub_nonneg.mpr hsmall) (div_nonneg hB (pow_nonneg hD.le c)))
  calc
    _ ≤ (c.factorial : ℝ) * (1 / DD n d ^ c) * frob B *
        (1 - (1 + |Λ|) * cG 2 / (n : ℝ)) := by convert hb using 1 <;> ring
    _ ≤ _ := hh

/-- The chi-square correction constant of Prop F, `C_F = totW d k [1,k] (wChi K)`. -/
noncomputable def CF71 (d k : ℕ) (K : ℝ) : ℝ := totW d k (Finset.Icc 1 k) (wChi K)

/-- **The Prop F threshold** `n_F = ⌊max(2E, 8C_F) + 1⌋₊ + 1`, `E = (1+|K|)·cG 2`. -/
noncomputable def nF71 (d k : ℕ) (K : ℝ) : ℕ :=
  ⌊max (2 * ((1 + |K|) * cG 2)) (8 * CF71 d k K) + 1⌋₊ + 1

/-- **Prop F under a chi-square bound, with its explicit threshold.** -/
theorem propF71 (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (K : ℝ) :
    PropF71 d k K (nF71 d k K) := by
  let Λ := K
  have hW := lemmaW53 k
  have hU := lemmaU53 d
  have hS := lemmaS53
  have hTr := lemmaTr53
  classical
  let C := CF71 d k Λ
  let E := (1 + |Λ|) * cG 2
  have hC : 0 ≤ C := totW_nonneg d k _ _ (wChi_nonneg K)
  have hE : 0 ≤ E := by dsimp [E, cG]; positivity
  set n0 := nF71 d k K with hn0def
  have hn0 : max (2 * E) (8 * C) + 1 < (n0 : ℝ) := by
    have h := Nat.lt_floor_add_one (max (2 * E) (8 * C) + 1)
    rw [hn0def, nF71]
    push_cast
    exact h
  intro n hn μ hμ f0 T hT htop
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hmax : max (2 * E) (8 * C) + 1 < (n : ℝ) := hn0.trans_le hnn
  have hn1R : (1 : ℝ) < n := by
    have hm : 0 ≤ max (2 * E) (8 * C) := le_trans (by positivity) (le_max_left _ _)
    linarith
  have hn1 : 1 ≤ n := by exact_mod_cast hn1R.le
  have hnpos : (0 : ℝ) < n := lt_trans zero_lt_one hn1R
  have hη : E / (n : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hnpos).mpr
    have hm := le_max_left (2 * E) (8 * C)
    linarith
  have hsmall : C / (n : ℝ) ≤ 1 / 8 := by
    apply (div_le_iff₀ hnpos).mpr
    have hm := le_max_right (2 * E) (8 * C)
    linarith
  have hsph := chiLaw_sph hμ
  have hN := FloorCorrection59x.Ncirc_nonneg (d := d) hn1 k f0 T
  have hbase := floor_base_energy hn1 (by omega : 1 ≤ d) hμ
    (show E / (n : ℝ) ≤ 1 by linarith) k f0 T
  have hmain : Ncirc n d k f0 T / 2 ≤
      ∑ c ∈ Finset.Icc 1 k, ∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
        BstLean.Part41.varU μ
          (FloorCorrection59x.baseKernel (sg n d) (Tcirc n d k f0 T) ⟨c, a, p⟩) := by
    have hh := mul_le_mul_of_nonneg_right
      (show (1 / 2 : ℝ) ≤ 1 - E / (n : ℝ) by linarith) hN
    calc
      _ = (1 / 2 : ℝ) * Ncirc n d k f0 T := by ring
      _ ≤ _ := hh
      _ ≤ _ := hbase
  have hcorr := total_correction_W hn1 (by omega : 1 ≤ d) hsph (wChi_nonneg K)
    (devW_chi hn1 hμ) hTr k (Finset.Icc 1 k) (fun c hc => (Finset.mem_Icc.mp hc).2) f0 T
  have hcorrection : (∑ c ∈ Finset.Icc 1 k,
      ∫ x, FloorCorrection59x.kernelErrorSq (d := d) k c (sg n d) (c0 d / DD n d)
        (TF k f0 T) x ∂μ) ≤ Ncirc n d k f0 T / 8 := by
    have hh := mul_le_mul_of_nonneg_right hsmall hN
    exact hcorr.trans (by simpa only [C, CF71, div_eq_mul_inv, mul_comm, one_mul] using hh)
  have hperturb := Finset.sum_le_sum (s := Finset.Icc 1 k)
    (fun c (_ : c ∈ Finset.Icc 1 k) =>
      FloorAssembly.kernel_variance_perturbation (d := d) hsph k c (sg n d)
        (c0 d / DD n d) (TF k f0 T))
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div] at hperturb
  have hfloor : Ncirc n d k f0 T / 8 ≤
      ∑ c ∈ Finset.Icc 1 k, ∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
        BstLean.Part41.varU μ (FloorEnergy.energyKernel k (sg n d) (TF k f0 T) ⟨c, a, p⟩) := by
    change _ ≤ _ at hperturb
    change Ncirc n d k f0 T / 2 ≤
      ∑ c ∈ Finset.Icc 1 k, ∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
        BstLean.Part41.varU μ (FloorCorrection59x.baseKernel (sg n d)
          (heatA k (c0 d / DD n d) (TF k f0 T)) ⟨c, a, p⟩) at hmain
    change (∑ c ∈ Finset.Icc 1 k,
      ∫ x, FloorCorrection.kernelErrorSq (d := d) k c (sg n d) (c0 d / DD n d)
        (TF k f0 T) x ∂μ) ≤ Ncirc n d k f0 T / 8 at hcorrection
    change Ncirc n d k f0 T / 2 ≤
      ∑ c ∈ Finset.Icc 1 k, ∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
        BstLean.Part41.varU μ (FloorCorrection.baseKernel (sg n d)
          (heatA k (c0 d / DD n d) (TF k f0 T)) ⟨c, a, p⟩) at hmain
    linarith
  have henergy := FloorEnergy.varFQ_energy53 (d := d) k (sg n d) f0 T hT hW hsph
  rw [henergy.2]
  exact hfloor.trans (FloorAssembly.positive_energy_le_total μ k (sg n d) (TF k f0 T))

end BstLean.Part71

