import BstLean.Part53Defs
import BstLean.Part53Floor_Restriction
import BstLean.Part53Floor_Energy
import BstLean.Part53Floor_Moments
import BstLean.Part53Floor_Assembly

/-!
# Part 53, wave 1: Prop F, the floor in the Gaussian proxy (§6 of the source)

Specification: `delegations/answers/p53-spec-opus.md` §3.5.
Replace each `sorry` by a proof. Do not edit the statements. Do not use `native_decide` or `axiom`
anywhere. This file imports `Part53Defs` only (a prover may also import finished Part 29–52 files,
but no other Part 53 wave-1 file).

Suggested route.
* (W4) from Lemma W at `(φ(x), φ(x'))` and `(φ(x), φ(x))`: `E_Z Var_μ = Σ_c c! E_μ‖F_c − E_μ F_c‖²`.
* `sd(φ^{⊗c}) ≥ sd(⟨φ, v⟩^{c−1} φ)` (contract with `v = φ̄/‖φ̄‖`), `⟨φ,v⟩ ∈ [1 − 2θ, 1 + θ]`,
  `θ = √((d+1) η_n)`, `sd(φ) = √(tr Σ_μ) ≥ √(1 − η_n)` (Lemma Σ(iii)).
* Correction `β_c` by Lemma Tr and Lemma Σ(v) at `q = 2`; `(a − β)_+² ≥ a²/2 − β²`.
-/

namespace BstLean.Part53

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT Tens TSymm fval In41 Pn heavyCount)
open BstLean.Part43 (BofQ varFQ)

variable {n d : ℕ}

private lemma floor_feature_variance (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (hμ : DensLaw n μ Λ) (hG : LemmaG53 d) :
    1 - Real.exp Λ * cG d / (n : ℝ) ≤
      ∑ p : Mono n d, BstLean.Part41.varU μ (fun x => phiM x p) := by
  have hsph := FloorMoments.dens_sph hμ
  letI := hsph.prob
  have hc (i : Fin n) : Integrable (fun x : Fin n → ℝ => x i) μ :=
    FloorEnergy.sphere_cont_integrable hsph (continuous_apply i)
  have hc2 (i : Fin n) : Integrable (fun x : Fin n → ℝ => x i ^ 2) μ :=
    FloorEnergy.sphere_cont_integrable hsph ((continuous_apply i).pow 2)
  calc
    _ ≤ 1 - ∑ i : Fin n, (∫ x, x i ∂μ) ^ 2 :=
      sub_le_sub_left (FloorMoments.coordinate_mean_bound53 hn hd hμ hG) 1
    _ = ∑ i : Fin n, BstLean.Part41.varU μ (fun x => x i) :=
      (sphere_coordinate_variance53 μ hsph.sphere hc hc2).symm
    _ ≤ _ := raw_feature_coordinate_variance53 μ hd

private lemma floor_fixed_tensor_variance (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (hμ : DensLaw n μ Λ) (hG : LemmaG53 d)
    (c : ℕ) (A : (Fin (c + 1) → Fin n) → ℝ) :
    frob A * (1 - Real.exp Λ * cG d / (n : ℝ)) ≤
      ∑ a : Fin (c + 1) → Fin n, ∑ p : Fin (c + 1) → Mono n d,
        BstLean.Part41.varU μ (fun x => A a * ∏ t, phiM x (p t)) := by
  calc
    _ ≤ frob A * (∑ p : Mono n d, BstLean.Part41.varU μ (fun x => phiM x p)) :=
      mul_le_mul_of_nonneg_left (floor_feature_variance hn hd hμ hG)
        (Finset.sum_nonneg (fun a _ => sq_nonneg _))
    _ ≤ _ := tensor_coefficient_variance_floor53 μ (fun x p => phiM x p) A default
      phiM_default_floor53 c

private lemma floor_positive_tensor_variance (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (hμ : DensLaw n μ Λ) (hG : LemmaG53 d)
    (c : ℕ) (hc : 1 ≤ c) (A : (Fin c → Fin n) → ℝ) :
    frob A * (1 - Real.exp Λ * cG d / (n : ℝ)) ≤
      ∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
        BstLean.Part41.varU μ (fun x => A a * ∏ t, phiM x (p t)) := by
  cases c with
  | zero => omega
  | succ c => exact floor_fixed_tensor_variance hn hd hμ hG c A

private lemma floor_base_energy (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (hμ : DensLaw n μ Λ) (hG : LemmaG53 d)
    (hsmall : Real.exp Λ * cG d / (n : ℝ) ≤ 1) (k : ℕ) (f0 : ℝ) (T : Tens n) :
    (1 - Real.exp Λ * cG d / (n : ℝ)) * Ncirc n d k f0 T ≤
      ∑ c ∈ Finset.Icc 1 k, ∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
        BstLean.Part41.varU μ
          (FloorCorrection.baseKernel (sg n d) (Tcirc n d k f0 T) ⟨c, a, p⟩) := by
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
      exact FloorCorrection.sg_pow_even hn c
    rw [hs]
  have hh := floor_positive_tensor_variance hn hd hμ hG c (Finset.mem_Icc.mp hc).1 A
  have he : (∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
      BstLean.Part41.varU μ (fun x => A a * ∏ t, phiM x (p t))) =
      ∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
        BstLean.Part41.varU μ
          (FloorCorrection.baseKernel (sg n d) (Tcirc n d k f0 T) ⟨c, a, p⟩) := rfl
  rw [he, hnorm] at hh
  have hfac : (1 : ℝ) ≤ c.factorial := by exact_mod_cast Nat.factorial_pos c
  have hD := BstLean.Part36.DD_pos (d := d) hn
  have hB : 0 ≤ frob B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb := mul_le_mul_of_nonneg_right hfac
    (show 0 ≤ (1 - Real.exp Λ * cG d / (n : ℝ)) * (frob B / DD n d ^ c) from
      mul_nonneg (sub_nonneg.mpr hsmall) (div_nonneg hB (pow_nonneg hD.le c)))
  calc
    _ ≤ (c.factorial : ℝ) * (1 / DD n d ^ c) * frob B *
        (1 - Real.exp Λ * cG d / (n : ℝ)) := by convert hb using 1 <;> ring
    _ ≤ _ := hh

/-- **Prop F.** -/
theorem propF53_of (d k : ℕ) (hd : 2 ≤ d) (hk : 1 ≤ k) (Λ : ℝ)
    (hW : LemmaW53 k) (hU : LemmaU53 d) (hS : LemmaS53) (hG : LemmaG53 d) (hTr : LemmaTr53) :
    ∃ n0 : ℕ, PropF53 d k Λ n0 := by
  classical
  let C := FloorCorrection.totalCorrectionConstant d k Λ
  let E := Real.exp Λ * cG d
  have hC : 0 ≤ C := FloorCorrection.totalCorrectionConstant_nonneg d k Λ
  have hE : 0 ≤ E := by dsimp [E, cG]; positivity
  obtain ⟨n0, hn0⟩ := exists_nat_gt (max (2 * E) (8 * C) + 1)
  refine ⟨n0, ?_⟩
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
  have hsph := FloorMoments.dens_sph hμ
  have hN := FloorCorrection.Ncirc_nonneg (d := d) hn1 k f0 T
  have hbase := floor_base_energy hn1 (by omega : 1 ≤ d) hμ hG
    (show E / (n : ℝ) ≤ 1 by linarith) k f0 T
  have hmain : Ncirc n d k f0 T / 2 ≤
      ∑ c ∈ Finset.Icc 1 k, ∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
        BstLean.Part41.varU μ
          (FloorCorrection.baseKernel (sg n d) (Tcirc n d k f0 T) ⟨c, a, p⟩) := by
    have hh := mul_le_mul_of_nonneg_right
      (show (1 / 2 : ℝ) ≤ 1 - E / (n : ℝ) by linarith) hN
    calc
      _ = (1 / 2 : ℝ) * Ncirc n d k f0 T := by ring
      _ ≤ _ := hh
      _ ≤ _ := hbase
  have hcorr := FloorCorrection.total_kernel_correction hn1 (by omega : 1 ≤ d)
    hμ hU hS hTr k f0 T
  have hcorrection : (∑ c ∈ Finset.Icc 1 k,
      ∫ x, FloorCorrection.kernelErrorSq (d := d) k c (sg n d) (c0 d / DD n d)
        (TF k f0 T) x ∂μ) ≤ Ncirc n d k f0 T / 8 := by
    have hh := mul_le_mul_of_nonneg_right hsmall hN
    exact hcorr.trans (by simpa only [C, div_eq_mul_inv, mul_comm, one_mul] using hh)
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
        BstLean.Part41.varU μ (FloorCorrection.baseKernel (sg n d)
          (heatA k (c0 d / DD n d) (TF k f0 T)) ⟨c, a, p⟩) at hmain
    linarith
  have henergy := FloorEnergy.varFQ_energy53 (d := d) k (sg n d) f0 T hT hW hsph
  rw [henergy.2]
  exact hfloor.trans (FloorAssembly.positive_energy_le_total μ k (sg n d) (TF k f0 T))

end BstLean.Part53
