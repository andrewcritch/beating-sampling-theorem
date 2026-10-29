import BstLean.Part72Good

/-!
# Part 72: Prop E under the moment conditions `Good72`

A copy of the end of `Part71Error.lean`, with the feature-operator hypothesis `FeatOp` replaced by
the main-term tensor bounds `featDev μ c ≤ F(c)/n` (`Good72.feat`), and the trace-moment weight
extended by `wExt`. Constant `C_E = 2·totW d k [0,k] w + 2·mainG d k F`,
`mainG d k F = Σ_{c=1}^k c!·F(c)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part72

open MeasureTheory BstLean.Part53
open BstLean.Part59
open BstLean.Part71
open BstLean.Part29 (uniformSphere stdGauss)
open BstLean.Part36 (CoefIdxD DD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM frob Tens TSymm)
open BstLean.Part43 (BofQ)
open FloorEnergy FloorCorrection
variable {n d : ℕ}

/-- `main = Σ_{c=1}^k c!·F(c)`. -/
noncomputable def mainG (k : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ c ∈ Finset.Icc 1 k, (c.factorial : ℝ) * F c

private lemma main_zero {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (s : ℝ) (B : Tens n) : error53_main_energy (d := d) μ s B 0 = 0 := by
  let := hμ.prob
  rw [error53_main_energy_formula]
  simp [frob]

private lemma featDev_nonneg (μ : Measure (Fin n → ℝ)) (c : ℕ) : 0 ≤ featDev d μ c :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private lemma main_bound72 (hn : 1 ≤ n) {k : ℕ}
    {μ : Measure (Fin n → ℝ)} {w F : ℕ → ℝ} {Em : ℝ} (h : Good72 n d k μ w F Em)
    (c : ℕ) (hc : c ∈ Finset.Icc 1 k) (f0 : ℝ) (T : Tens n) :
    error53_main_energy (d := d) μ (sg n d) (Tcirc n d k f0 T) c ≤
      ((c.factorial : ℝ) * F c) / (n : ℝ) * Ncirc n d k f0 T := by
  have hc' := Finset.mem_Icc.mp hc
  have hh : featDev d μ c ≤ F c / n := h.feat c hc'.1 hc'.2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hF : 0 ≤ F c := by
    have := (featDev_nonneg (d := d) μ c).trans hh
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => by linarith [h.2])
  have hD := BstLean.Part36.DD_pos (d := d) hn
  have hf : 0 ≤ frob (Tcirc n d k f0 T c) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hC : 0 ≤ (c.factorial : ℝ) * F c := by positivity
  rw [error53_main_energy_formula, BstLean.Part59.FloorCorrection59x.sg_pow_even hn c]
  calc
    _ ≤ (c.factorial : ℝ) * (1 / BstLean.Part36.DD n d ^ c) *
        frob (Tcirc n d k f0 T c) * (F c / n) := by
      exact mul_le_mul_of_nonneg_left hh (by positivity)
    _ = ((c.factorial : ℝ) * F c) /
        (n : ℝ) * (frob (Tcirc n d k f0 T c) / BstLean.Part36.DD n d ^ c) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (BstLean.Part59.FloorCorrection59x.Ncirc_term_le hn k c f0 T hc) (div_nonneg hC hn0.le)

private theorem total_main72 (hn : 1 ≤ n) {k : ℕ}
    {μ : Measure (Fin n → ℝ)} {w F : ℕ → ℝ} {Em : ℝ} (h : Good72 n d k μ w F Em)
    (f0 : ℝ) (T : Tens n) :
    (∑ c ∈ Finset.range (k + 1), error53_main_energy (d := d) μ (sg n d) (Tcirc n d k f0 T) c) ≤
      mainG k F / (n : ℝ) * Ncirc n d k f0 T := by
  classical
  have he : (∑ c ∈ Finset.range (k + 1),
      error53_main_energy (d := d) μ (sg n d) (Tcirc n d k f0 T) c) =
      ∑ c ∈ Finset.Icc 1 k, error53_main_energy (d := d) μ (sg n d) (Tcirc n d k f0 T) c := by
    rw [Finset.sum_range_succ', main_zero h.sph, add_zero]
    rw [show Finset.Icc 1 k = Finset.Ico 1 (k + 1) by rfl, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.add_comm 1 i]
  rw [he]
  calc
    _ ≤ ∑ c ∈ Finset.Icc 1 k, ((c.factorial : ℝ) * F c) / (n : ℝ) * Ncirc n d k f0 T :=
      Finset.sum_le_sum (fun c hc => main_bound72 hn h c hc f0 T)
    _ = _ := by unfold mainG; rw [← Finset.sum_mul, ← Finset.sum_div]

/-- **Prop E, generic form, under `Good72`.** -/
theorem normalized_bound72 (hn : 1 ≤ n) (hd : 1 ≤ d) {k : ℕ}
    {μ : Measure (Fin n → ℝ)} {w F : ℕ → ℝ} {Em : ℝ} (hw : ∀ i, 0 ≤ w i)
    (h : Good72 n d k μ w F Em) (f0 : ℝ) (T : Tens n) (hT : TSymm k T) :
    (∫ Z, (BofQ μ k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) ^ 2
      ∂stdGauss (CoefIdxD n d)) ≤
    (2 * totW d k (Finset.range (k + 1)) w + 2 * mainG k F) / (n : ℝ) * Ncirc n d k f0 T := by
  classical
  have hsph := h.sph
  rw [error53_error_energy_split hn k f0 T hT hsph]
  calc
    _ ≤ ∑ c ∈ Finset.range (k + 1),
        (2 * (∫ x, kernelErrorSq (d := d) k c (sg n d)
          (c0 d / BstLean.Part36.DD n d) (TF k f0 T) x ∂μ) +
        2 * error53_main_energy (d := d) μ (sg n d) (Tcirc n d k f0 T) c) := by
      apply Finset.sum_le_sum
      intro c hc
      exact error53_mean_perturbation hsph k c (sg n d)
        (c0 d / BstLean.Part36.DD n d) (TF k f0 T)
    _ = 2 * (∑ c ∈ Finset.range (k + 1),
        ∫ x, kernelErrorSq (d := d) k c (sg n d)
          (c0 d / BstLean.Part36.DD n d) (TF k f0 T) x ∂μ) +
        2 * (∑ c ∈ Finset.range (k + 1),
          error53_main_energy (d := d) μ (sg n d) (Tcirc n d k f0 T) c) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (totW d k (Finset.range (k + 1)) w / (n : ℝ) * Ncirc n d k f0 T) +
        2 * (mainG k F / (n : ℝ) * Ncirc n d k f0 T) := by
      refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by norm_num))
        (mul_le_mul_of_nonneg_left (total_main72 hn h f0 T) (by norm_num))
      have hc := total_correction_W hn hd hsph (wExt_nonneg hw) (devW_ext hn hd h) lemmaTr53
        k (Finset.range (k + 1)) (fun c hc => by have := Finset.mem_range.mp hc; omega) f0 T
      rwa [totW_ext] at hc
    _ = _ := by ring

/-- **The Prop E constant** `C_E = 2·totW d k [0,k] w + 2·mainG d k F`. -/
noncomputable def CE72 (d k : ℕ) (w F : ℕ → ℝ) : ℝ :=
  2 * totW d k (Finset.range (k + 1)) w + 2 * mainG k F

/-- **Prop E under `Good72`.** -/
theorem propE72 (d k : ℕ) (hd : 1 ≤ d) (w F : ℕ → ℝ) (Em : ℝ) (hw : ∀ i, 0 ≤ w i) :
    PropE72 (GoodClass d k w F Em) d k (CE72 d k w F) 1 := by
  intro n hn μ hμ f0 T hT _
  exact ⟨BstLean.Part53.error53_integrable hμ.sph k f0 T (sg n d),
    normalized_bound72 hn hd hw hμ f0 T hT⟩

end BstLean.Part72
