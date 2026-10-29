import BstLean.Part132Cos
import BstLean.Part132Defs

/-!
# Part 132, item 3: the World network and the normalization of `x`

Role: `delegations/statements/p132-spec.md`. Paper source: `onW4c-cx.md` §3 ("W_3 and
normalization", "W_2, then W_1", "Zero-event budget"); `onW4-opus-prover.md` 2.4.

* `epsW m = (1 + 5/m)² − 1`: the relative variance of `|h₂|²`.
* `hid2_cos_lower`: for unit inputs `u, u′`:
  `E cos(h₂(u), h₂(u′)) ≥ κ(κ(⟨u, u′⟩)) − (10/m)κ(0) − (5·epsW·λ + 1/λ)/2`, any `λ > 0`.
* `hid2_zero`: `Pr(h₂(u) = 0) ≤ epsW m` (Chebyshev; the paper has the exact value).
* **`world_cos_lower`**: for unit `u, u′` and every `λ > 0`:
  `E_W ⟨x(u), x(u′)⟩ ≥ κ(κ(⟨u, u′⟩)) − eW n m λ`,
  `eW n m λ = 17/n + (10/m)κ(0) + (5·epsW·λ + 1/λ)/2 + 2·epsW`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part132

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130

variable {N m n : ℕ}

/-- The relative variance of `|h₂|²`: `(1 + 5/m)² − 1`. -/
noncomputable def epsW (m : ℕ) : ℝ := (1 + 5 / (m : ℝ)) ^ 2 - 1

lemma epsW_nonneg (m : ℕ) : 0 ≤ epsW m := by
  unfold epsW
  have : (0 : ℝ) ≤ 5 / (m : ℝ) := by positivity
  nlinarith

/-- The error of the lower bound of the cosine of two outputs of `W`. -/
noncomputable def eW (n m : ℕ) (lam : ℝ) : ℝ :=
  17 / (n : ℝ) + 10 / (m : ℝ) * kappa 0 + (5 * epsW m * lam + 1 / lam) / 2 + 2 * epsW m

/-- The scale of `|h₂|²` for a unit input. -/
noncomputable def sH (N m : ℕ) : ℝ := (m : ℝ) / 2 * (2 / (m : ℝ)) * ((m : ℝ) / 2 * (2 / (N : ℝ)))

lemma sH_pos (hN : 1 ≤ N) (hm : 1 ≤ m) : 0 < sH N m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold sH; positivity

section hidden

variable (hN : 1 ≤ N) (hm : 1 ≤ m)
include hN hm

lemma hid2_unit_moments {u : Fin N → ℝ} (hu : normSq u = 1) :
    ∫ θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ, normSq (hid2 θ.1 θ.2 u)
      ∂((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) = sH N m ∧
    ∫ θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ, normSq (hid2 θ.1 θ.2 u) ^ 2
      ∂((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) =
      (1 + epsW m) * sH N m ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [(hid2_sq (m₁ := m) (m₂ := m) (two_div_nonneg N) (two_div_nonneg m) u).2,
    (hid2_four (m₁ := m) (m₂ := m) (two_div_nonneg N) (two_div_nonneg m) u).2, hu]
  unfold sH epsW
  constructor
  · ring
  · field_simp
    ring

lemma hid2_pair {u u' : Fin N → ℝ} (hu : normSq u = 1) (hu' : normSq u' = 1) :
    Integrable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      (nrm (hid2 θ.1 θ.2 u) * nrm (hid2 θ.1 θ.2 u') - sH N m) ^ 2)
      ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) ∧
    ∫ θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ,
      (nrm (hid2 θ.1 θ.2 u) * nrm (hid2 θ.1 θ.2 u') - sH N m) ^ 2
      ∂((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) ≤
      5 * epsW m * sH N m ^ 2 := by
  have hs := (sH_pos hN hm).le
  have hmeas : ∀ u : Fin N → ℝ, Measurable (fun θ : Matrix (Fin m) (Fin N) ℝ ×
      Matrix (Fin m) (Fin m) ℝ => normSq (hid2 θ.1 θ.2 u)) := fun u =>
    (continuous_normSq.comp (continuous_hid2_param u)).measurable
  have h4 : (√(sH N m)) ^ 4 = sH N m ^ 2 := by
    rw [show (√(sH N m)) ^ 4 = ((√(sH N m)) ^ 2) ^ 2 by ring, Real.sq_sqrt hs]
  have key := norm_pair (μ := (gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
    (hmeas u) (hmeas u') (fun θ => normSq_nonneg _) (fun θ => normSq_nonneg _)
    (hid2_four (two_div_nonneg N) (two_div_nonneg m) u).1
    (hid2_four (two_div_nonneg N) (two_div_nonneg m) u').1 (ε := epsW m)
    (Real.sqrt_nonneg (sH N m)) (Real.sqrt_nonneg (sH N m))
    (by rw [(hid2_unit_moments hN hm hu).1, Real.sq_sqrt hs])
    (by rw [(hid2_unit_moments hN hm hu').1, Real.sq_sqrt hs])
    (by rw [(hid2_unit_moments hN hm hu).2, h4])
    (by rw [(hid2_unit_moments hN hm hu').2, h4])
  rw [Real.mul_self_sqrt hs] at key
  exact ⟨key.2.2.2.1, key.2.2.2.2⟩

end hidden

/-- The pointwise first-order lower bound of a cosine `C/P` against the scale `s`. -/
lemma cos_crude {s lam C P : ℝ} (hs : 0 < s) (hl : 0 < lam) (hP0 : 0 ≤ P) (hCP : |C| ≤ P) :
    1 / s * C + -(1 / (2 * lam)) - lam / (2 * s ^ 2) * (P - s) ^ 2 - 0 * C - 0 * C ≤ C / P := by
  rcases eq_or_lt_of_le hP0 with h | h
  · have hC : C = 0 := by rw [← h] at hCP; exact abs_nonpos_iff.mp hCP
    rw [← h, hC]
    have h1 : 0 ≤ lam / (2 * s ^ 2) * (0 - s) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 1 / (2 * lam) := by positivity
    simp only [mul_zero, div_zero, zero_add, sub_zero]
    linarith
  · set t := C / P with ht
    have hC : C = t * P := by rw [ht]; field_simp
    have ht1 : |t| ≤ 1 := by
      rw [ht, abs_div, abs_of_pos h, div_le_one h]; exact hCP
    obtain ⟨t1, t2⟩ := abs_le.mp ht1
    have e : 1 / s * C + -(1 / (2 * lam)) - lam / (2 * s ^ 2) * (P - s) ^ 2 - 0 * C - 0 * C =
        t * (P / s) - (lam / 2 * (1 - P / s) ^ 2 + 1 / (2 * lam)) := by
      rw [hC]; field_simp; ring
    rw [e]
    set w := 1 - P / s with hw
    have e2 : lam / 2 * w ^ 2 + 1 / (2 * lam) + t * w =
        ((lam * w + t) ^ 2 + (1 - t ^ 2)) / (2 * lam) := by field_simp; ring
    have h3 : 0 ≤ ((lam * w + t) ^ 2 + (1 - t ^ 2)) / (2 * lam) :=
      div_nonneg (by nlinarith) (by positivity)
    have e3 : P / s = 1 - w := by rw [hw]; ring
    rw [e3]
    nlinarith

lemma measurable_cosv_hid2 (u u' : Fin N → ℝ) :
    Measurable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')) :=
  Measurable.comp (g := fun p : (Fin m → ℝ) × (Fin m → ℝ) => cosv p.1 p.2)
    (f := fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      (hid2 θ.1 θ.2 u, hid2 θ.1 θ.2 u'))
    measurable_cosv ((continuous_hid2_param u).prodMk (continuous_hid2_param u')).measurable

lemma integrable_cosv_hid2 (u u' : Fin N → ℝ) :
    Integrable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u'))
      ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_cosv_hid2 u u').aestronglyMeasurable (Filter.Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs, abs_le]
  exact cosv_mem _ _

/-- **The hidden layers of `W`**: for unit inputs `u, u′` and every `λ > 0`,
`E cos(h₂(u), h₂(u′)) ≥ κ(κ(⟨u, u′⟩)) − (10/m)κ(0) − (5·epsW·λ + 1/λ)/2`. -/
theorem hid2_cos_lower (hN : 1 ≤ N) (hm : 1 ≤ m) {u u' : Fin N → ℝ} (hu : normSq u = 1)
    (hu' : normSq u' = 1) {lam : ℝ} (hl : 0 < lam) :
    kappa (kappa (dotp u u')) - 10 / (m : ℝ) * kappa 0 - (5 * epsW m * lam + 1 / lam) / 2 ≤
      ∫ θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ,
        cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')
        ∂((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) := by
  have hs := sH_pos hN hm
  obtain ⟨iP, uP⟩ := hid2_pair hN hm hu hu'
  have iC := hid2_dot_integrable (m₁ := m) (m₂ := m) (two_div_nonneg N) (two_div_nonneg m) u u'
  have lC := hid2_dot_lower (m₁ := m) (m₂ := m) (two_div_nonneg N) (two_div_nonneg m) hm u u'
  rw [psi_unit _ hu hu', nrm_of_normSq_one hu, nrm_of_normSq_one hu'] at lC
  obtain ⟨iR, eR⟩ := integral_lin4
    (μ := (gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) iC iP iC iC
    (-(1 / (2 * lam))) (1 / sH N m) (lam / (2 * sH N m ^ 2)) 0 0
  have hmono := integral_mono iR (integrable_cosv_hid2 u u') (fun θ =>
    cos_crude hs hl (nrm_mul_nonneg _ _) (abs_dotp_le_nrm _ _))
  rw [eR] at hmono
  refine le_trans ?_ hmono
  have t1 := mul_le_mul_of_nonneg_left lC (by positivity : (0 : ℝ) ≤ 1 / sH N m)
  have e1 : 1 / sH N m * ((m : ℝ) / 2 * (2 / (m : ℝ)) * ((m : ℝ) / 2 * (2 / (N : ℝ)) *
      ((kappa ∘ kappa) (dotp u u') - 10 / (m : ℝ) * kappa 0 * (1 * 1)))) =
      kappa (kappa (dotp u u')) - 10 / (m : ℝ) * kappa 0 := by
    have : sH N m ≠ 0 := hs.ne'
    have e : (m : ℝ) / 2 * (2 / (m : ℝ)) * ((m : ℝ) / 2 * (2 / (N : ℝ)) *
        ((kappa ∘ kappa) (dotp u u') - 10 / (m : ℝ) * kappa 0 * (1 * 1))) =
        sH N m * (kappa (kappa (dotp u u')) - 10 / (m : ℝ) * kappa 0) := by
      unfold sH; simp only [Function.comp]; ring
    rw [e]; field_simp
  rw [e1] at t1
  have t2 := mul_le_mul_of_nonneg_left uP (by positivity : (0 : ℝ) ≤ lam / (2 * sH N m ^ 2))
  have e2 : lam / (2 * sH N m ^ 2) * (5 * epsW m * sH N m ^ 2) = 5 * epsW m * lam / 2 := by
    have : sH N m ≠ 0 := hs.ne'
    field_simp
  rw [e2] at t2
  have e3 : (5 * epsW m * lam + 1 / lam) / 2 = 5 * epsW m * lam / 2 + 1 / (2 * lam) := by
    field_simp
  rw [e3]
  linarith

lemma measurable_zero_ind (u : Fin N → ℝ) :
    Measurable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      (if normSq (hid2 θ.1 θ.2 u) = 0 then (1 : ℝ) else 0)) :=
  Measurable.ite (measurableSet_eq_fun
    (continuous_normSq.comp (continuous_hid2_param u)).measurable measurable_const)
    measurable_const measurable_const

lemma integrable_zero_ind (u : Fin N → ℝ) :
    Integrable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      (if normSq (hid2 θ.1 θ.2 u) = 0 then (1 : ℝ) else 0))
      ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_zero_ind u).aestronglyMeasurable (Filter.Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs]
  split_ifs <;> simp

/-- **The zero event of the hidden layers**: `Pr(h₂(u) = 0) ≤ epsW m` for a unit input `u`. -/
theorem hid2_zero (hN : 1 ≤ N) (hm : 1 ≤ m) {u : Fin N → ℝ} (hu : normSq u = 1) :
    ∫ θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ,
      (if normSq (hid2 θ.1 θ.2 u) = 0 then (1 : ℝ) else 0)
      ∂((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) ≤ epsW m := by
  have hs := sH_pos hN hm
  obtain ⟨e2, e4⟩ := hid2_unit_moments hN hm hu
  have i2 := (hid2_sq (m₁ := m) (m₂ := m) (two_div_nonneg N) (two_div_nonneg m) u).1
  have i4 := (hid2_four (m₁ := m) (m₂ := m) (two_div_nonneg N) (two_div_nonneg m) u).1
  obtain ⟨iR, eR⟩ := integral_lin4
    (μ := (gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) i4 i2 i2 i2
    1 (1 / sH N m ^ 2) (2 / sH N m) 0 0
  have hpt : ∀ θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ,
      (if normSq (hid2 θ.1 θ.2 u) = 0 then (1 : ℝ) else 0) ≤
      1 / sH N m ^ 2 * normSq (hid2 θ.1 θ.2 u) ^ 2 + 1 - 2 / sH N m * normSq (hid2 θ.1 θ.2 u) -
        0 * normSq (hid2 θ.1 θ.2 u) - 0 * normSq (hid2 θ.1 θ.2 u) := by
    intro θ
    have e : 1 / sH N m ^ 2 * normSq (hid2 θ.1 θ.2 u) ^ 2 + 1 -
        2 / sH N m * normSq (hid2 θ.1 θ.2 u) - 0 * normSq (hid2 θ.1 θ.2 u) -
        0 * normSq (hid2 θ.1 θ.2 u) = (normSq (hid2 θ.1 θ.2 u) / sH N m - 1) ^ 2 := by
      have : sH N m ≠ 0 := hs.ne'
      field_simp; ring
    rw [e]
    split_ifs with h0
    · rw [h0]; simp
    · positivity
  have hmono := integral_mono (integrable_zero_ind u) iR hpt
  rw [eR, e2, e4] at hmono
  refine hmono.trans (le_of_eq ?_)
  have : sH N m ≠ 0 := hs.ne'
  field_simp; ring

/-! ## The whole World network -/

lemma integral_assoc_ge {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) (τ : Measure γ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure τ] {f : α × β × γ → ℝ}
    (hf : Integrable f (μ.prod (ν.prod τ))) {g : α × β → ℝ} (hg : Integrable g (μ.prod ν))
    (h : ∀ a b, g (a, b) ≤ ∫ c, f (a, (b, c)) ∂τ) :
    ∫ z, g z ∂(μ.prod ν) ≤ ∫ ω, f ω ∂(μ.prod (ν.prod τ)) := by
  have e : ∫ ω, f ω ∂(μ.prod (ν.prod τ)) =
      ∫ z, f (MeasurableEquiv.prodAssoc z) ∂((μ.prod ν).prod τ) := by
    rw [← Measure.prodAssoc_prod, integral_map_equiv]
  have hf' : Integrable (fun z => f (MeasurableEquiv.prodAssoc z)) ((μ.prod ν).prod τ) := by
    have h1 : Integrable f (Measure.map MeasurableEquiv.prodAssoc ((μ.prod ν).prod τ)) := by
      rw [Measure.prodAssoc_prod]; exact hf
    exact (integrable_map_equiv _ f).mp h1
  rw [e]
  exact integral_prod_ge hf' hg (fun z => h z.1 z.2)

lemma xW_eq (M₁ : Matrix (Fin m) (Fin N) ℝ) (M₂ : Matrix (Fin m) (Fin m) ℝ)
    (M₃ : Matrix (Fin n) (Fin m) ℝ) (u : Fin N → ℝ) :
    xW ((M₁, M₂, M₃) : MlpParam N m n) u = sphPt (M₃.mulVec (hid2 M₁ M₂ u)) := rfl

lemma dotp_relu_nonneg {ι : Type*} [Fintype ι] (a b : ι → ℝ) : 0 ≤ dotp (reluV a) (reluV b) :=
  Finset.sum_nonneg fun i _ => mul_nonneg (relu_nonneg _) (relu_nonneg _)

lemma measurable_dotp_xW (u u' : Fin N → ℝ) :
    Measurable (fun W : MlpParam N m n => dotp (xW W u) (xW W u')) :=
  measurable_dotp_comp (measurable_xW_comp measurable_id measurable_const)
    (measurable_xW_comp measurable_id measurable_const)

lemma integrable_dotp_xW (hn : 1 ≤ n) (u u' : Fin N → ℝ) :
    Integrable (fun W : MlpParam N m n => dotp (xW W u) (xW W u')) (mlpGauss N m n) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_dotp_xW u u').aestronglyMeasurable (Filter.Eventually.of_forall fun W => ?_)
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨dotp_sphPt_ge hn _ _, dotp_sphPt_le hn _ _⟩

/-- **The World network and the normalization** (paper: `E t_x ≥ q − 16/n − 20/m_W − δ₀`, here
before the average over `u, u′`): for unit vectors `u, u′` of `ℝ^N` and every `λ > 0`,
`E_W ⟨x(u), x(u′)⟩ ≥ κ(κ(⟨u, u′⟩)) − eW n m λ`. -/
theorem world_cos_lower (hN : 1 ≤ N) (hm : 1 ≤ m) (hn : 1 ≤ n) {u u' : Fin N → ℝ}
    (hu : normSq u = 1) (hu' : normSq u' = 1) {lam : ℝ} (hl : 0 < lam) :
    kappa (kappa (dotp u u')) - eW n m lam ≤
      ∫ W : MlpParam N m n, dotp (xW W u) (xW W u') ∂mlpGauss N m n := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨iR, eR⟩ := integral_lin4
    (μ := (gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
    (integrable_cosv_hid2 u u') (integrable_zero_ind u) (integrable_zero_ind u')
    (integrable_zero_ind u') (-(17 / (n : ℝ))) 1 1 1 0
  have key := integral_assoc_ge (gaussMat m N (2 / (N : ℝ))) (gaussMat m m (2 / (m : ℝ)))
    (gaussMat n m (2 / (m : ℝ))) (f := fun W : MlpParam N m n => dotp (xW W u) (xW W u'))
    (integrable_dotp_xW hn u u') iR (fun M₁ M₂ => by
      have h := lin_cos_lower (n := n) (v := 2 / (m : ℝ)) (by positivity) hn (hid2 M₁ M₂ u)
        (hid2 M₁ M₂ u') (dotp_relu_nonneg _ _)
      simp only [xW_eq]
      linarith)
  rw [eR] at key
  refine le_trans ?_ key
  have c1 := hid2_cos_lower hN hm hu hu' hl
  have z1 := hid2_zero hN hm hu
  have z2 := hid2_zero hN hm hu'
  unfold eW
  linarith

end BstLean.Part132

open BstLean.Part132 in
#print axioms hid2_cos_lower
open BstLean.Part132 in
#print axioms world_cos_lower
