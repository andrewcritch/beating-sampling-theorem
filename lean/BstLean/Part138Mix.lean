import BstLean.Part138Gauss
import BstLean.Part137Tau

/-!
# Part 138: the cheap stand-in against the exact stand-in, general form

Role: `delegations/statements/p138-spec.md`. Paper sources: `onW5-opus-prover.md` §4.5
(Lemma D3), `onW16c-cx.md` §5.

`μ` is a probability measure on the inputs `u`, `h(u) ∈ ℝ^m`, `b ∈ ℝ^m`, `c ∈ ℝⁿ`,
`λ(u) = lam b (h u)`, `σ(u) = sig v b (h u)` (Part 134). The exact stand-in
`ν_c = standIn μ h v b c` is the distribution of `sphPt(λ(u)c + σ(u)γ)`.

* `cheapIn c τ₀`: **the cheap stand-in** `ν′`: the distribution of `sphPt(c + τ₀γ)`, `γ` a
  standard Gaussian vector of `ℝⁿ`.
* `pt_hell`: at one input with `λ > 0`: positive scaling inside `sphPt` and `gaussScale138`.
* `mix_cs`: Cauchy–Schwarz over the inputs.
* **`cheap_mix`**: if `K(u) ≥ hellG n (σ(u)/λ(u)) τ₀` at the inputs with `λ(u) > 0` that the user
  calls good, and `K(u) ≥ 1` at the other inputs, then for bounded measurable `φ`:
  `(E_ν φ − E_ν′ φ)² ≤ 2·E_u K·(E_ν φ² + E_ν′ φ²)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part138

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134

variable {n m : ℕ} {U : Type*} [MeasurableSpace U]

/-- **The cheap stand-in `ν′`**: the distribution of `sphPt(c + τ₀γ)`, `γ` a standard Gaussian
vector of `ℝⁿ`. -/
noncomputable def cheapIn (c : Fin n → ℝ) (τ₀ : ℝ) : Measure (Fin n → ℝ) :=
  (stdGauss (Fin n)).map (fun γ => sphPt (c + τ₀ • γ))

lemma measurable_cheapOut (c : Fin n → ℝ) (τ₀ : ℝ) :
    Measurable (fun γ : Fin n → ℝ => sphPt (c + τ₀ • γ)) :=
  measurable_sphPt.comp (measurable_const.add (measurable_const_smul τ₀))

lemma cheapIn_prob (c : Fin n → ℝ) (τ₀ : ℝ) : IsProbabilityMeasure (cheapIn c τ₀) := by
  unfold cheapIn
  exact (Measure.isProbabilityMeasure_map_iff (measurable_cheapOut c τ₀).aemeasurable).2
    inferInstance

lemma integral_cheapIn (c : Fin n → ℝ) (τ₀ : ℝ) {φ : (Fin n → ℝ) → ℝ} (hφ : Measurable φ) :
    ∫ x, φ x ∂cheapIn c τ₀ = ∫ γ, φ (sphPt (c + τ₀ • γ)) ∂stdGauss (Fin n) := by
  unfold cheapIn
  exact integral_map (measurable_cheapOut c τ₀).aemeasurable hφ.aestronglyMeasurable

/-- `(c, τ₀) ↦ E_{ν′} φ` is bounded and measurable in every measurable parameter. -/
lemma bm_cheapIn {Ω : Type*} [MeasurableSpace Ω] {cc : Ω → Fin n → ℝ} (hc : Measurable cc)
    {tt : Ω → ℝ} (ht : Measurable tt) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    BM (fun ω => ∫ x, φ x ∂cheapIn (cc ω) (tt ω)) := by
  have h1 : BM (fun q : Ω × (Fin n → ℝ) => φ (sphPt (cc q.1 + tt q.1 • q.2))) :=
    hφ.comp (measurable_sphPt.comp ((hc.comp measurable_fst).add
      ((ht.comp measurable_fst).smul measurable_snd)))
  have h2 := h1.integral_right (stdGauss (Fin n))
  simp_rw [integral_cheapIn _ _ hφ.meas]
  exact h2

/-- **Item 2 for the images under `sphPt`**: the cheap stand-ins with two scalars and one
centre. For `n ≥ 1`, `τ ≥ 0`, `τ₀ > 0` and bounded measurable `φ`:
`(E_{ν′(c, τ)} φ − E_{ν′(c, τ₀)} φ)² ≤ 2·hellG n τ τ₀·(E_{ν′(c, τ)} φ² + E_{ν′(c, τ₀)} φ²)`. -/
theorem gaussScale138_sph (hn : 1 ≤ n) (c : Fin n → ℝ) {τ τ₀ : ℝ} (hτ : 0 ≤ τ) (hτ₀ : 0 < τ₀)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    (∫ x, φ x ∂cheapIn c τ - ∫ x, φ x ∂cheapIn c τ₀) ^ 2 ≤
      2 * hellG n τ τ₀ * (∫ x, φ x ^ 2 ∂cheapIn c τ + ∫ x, φ x ^ 2 ∂cheapIn c τ₀) := by
  have h := gaussScale138 (ι := Fin n) (by rw [Fintype.card_fin]; omega) c hτ hτ₀
    (hφ.comp measurable_sphPt)
  rw [Fintype.card_fin] at h
  rw [integral_cheapIn c τ hφ.meas, integral_cheapIn c τ₀ hφ.meas,
    integral_cheapIn c τ (hφ.meas.pow_const 2), integral_cheapIn c τ₀ (hφ.meas.pow_const 2)]
  exact h

/-- **One input.** For `λ > 0`, `σ ≥ 0`, `τ₀ > 0`, `n ≥ 2` and bounded measurable `φ`:
`(E φ(sphPt(λc + σγ)) − E φ(sphPt(c + τ₀γ)))² ≤
  2·hellG n (σ/λ) τ₀·(E φ(sphPt(λc + σγ))² + E φ(sphPt(c + τ₀γ))²)`. -/
lemma pt_hell (hn : 2 ≤ n) (c : Fin n → ℝ) {l s τ₀ : ℝ} (hl : 0 < l) (hs : 0 ≤ s)
    (hτ₀ : 0 < τ₀) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    (∫ γ, φ (sphPt (l • c + s • γ)) ∂stdGauss (Fin n) -
        ∫ γ, φ (sphPt (c + τ₀ • γ)) ∂stdGauss (Fin n)) ^ 2 ≤
      2 * hellG n (s / l) τ₀ *
        (∫ γ, φ (sphPt (l • c + s • γ)) ^ 2 ∂stdGauss (Fin n) +
          ∫ γ, φ (sphPt (c + τ₀ • γ)) ^ 2 ∂stdGauss (Fin n)) := by
  have e : ∀ γ : Fin n → ℝ, sphPt (l • c + s • γ) = sphPt (c + (s / l) • γ) := by
    intro γ
    have : l • c + s • γ = l • (c + (s / l) • γ) := by
      rw [smul_add, smul_smul, mul_div_cancel₀ _ hl.ne']
    rw [this, sphPt_smul hl]
  simp_rw [e]
  have h := gaussScale138 (ι := Fin n) (by rw [Fintype.card_fin]; omega) c
    (div_nonneg hs hl.le) hτ₀ (hφ.comp measurable_sphPt)
  rw [Fintype.card_fin] at h
  exact h

lemma bm_sqrt {α : Type*} [MeasurableSpace α] {F : α → ℝ} (hF : BM F) : BM (fun x => √(F x)) := by
  obtain ⟨M, hM⟩ := hF.bdd
  refine ⟨hF.meas.sqrt, √M, fun x => ?_⟩
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt ((le_abs_self _).trans (hM x))

/-- **Cauchy–Schwarz over the inputs**: if `J(u)² ≤ 2K(u)(A(u) + A′)` at every `u`, then
`(E_u J)² ≤ 2·E_u K·(E_u A + A′)`. -/
lemma mix_cs (μ : Measure U) [IsProbabilityMeasure μ] {J A K : U → ℝ} {A' : ℝ}
    (hJ : BM J) (hA : BM A) (hA0 : ∀ u, 0 ≤ A u) (hA'0 : 0 ≤ A')
    (hKm : Measurable K) (hK0 : ∀ u, 0 ≤ K u) (hKi : Integrable K μ)
    (h : ∀ u, J u ^ 2 ≤ 2 * K u * (A u + A')) :
    (∫ u, J u ∂μ) ^ 2 ≤ 2 * (∫ u, K u ∂μ) * (∫ u, A u ∂μ + A') := by
  set f : U → ℝ := fun u => √(K u) with hf
  set g : U → ℝ := fun u => √(2 * (A u + A')) with hg
  have hS0 : ∀ u, 0 ≤ 2 * (A u + A') := fun u => by have := hA0 u; linarith
  have bS : BM (fun u => 2 * (A u + A')) := (BM.const 2).mul (hA.add (BM.const A'))
  have bg : BM g := bm_sqrt bS
  have ef2 : (fun u => f u ^ 2) = K := by
    funext u; simp only [hf]; exact Real.sq_sqrt (hK0 u)
  have eg2 : (fun u => g u ^ 2) = fun u => 2 * (A u + A') := by
    funext u; simp only [hg]; exact Real.sq_sqrt (hS0 u)
  have if2 : Integrable (fun u => f u ^ 2) μ := by rw [ef2]; exact hKi
  have ig2 : Integrable (fun u => g u ^ 2) μ := bg.sq.integrable μ
  have isum : Integrable (fun u => f u ^ 2 + g u ^ 2) μ := if2.add ig2
  have ifg : Integrable (fun u => f u * g u) μ := by
    refine isum.mono' (hKm.sqrt.mul bg.meas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (f u - g u), sq_nonneg (f u + g u)]
  have hpt : ∀ u, |J u| ≤ f u * g u := by
    intro u
    have h1 : J u ^ 2 ≤ (f u * g u) ^ 2 := by
      rw [mul_pow]
      have e1 : f u ^ 2 = K u := congrFun ef2 u
      have e2 : g u ^ 2 = 2 * (A u + A') := congrFun eg2 u
      rw [e1, e2]
      have := h u
      linarith
    exact abs_le_of_sq_le_sq h1 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have h1 : |∫ u, J u ∂μ| ≤ ∫ u, f u * g u ∂μ := by
    refine (abs_integral_le_integral_abs).trans ?_
    exact integral_mono (hJ.integrable μ).abs ifg hpt
  have h2 : (∫ u, J u ∂μ) ^ 2 ≤ (∫ u, f u * g u ∂μ) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 := cs_sq μ if2 ig2 ifg
  have e3 : ∫ u, g u ^ 2 ∂μ = 2 * (∫ u, A u ∂μ + A') := by
    rw [eg2, integral_const_mul, integral_add (hA.integrable μ) (integrable_const _)]
    simp
  rw [ef2, e3] at h3
  calc _ ≤ _ := h2
    _ ≤ _ := h3
    _ = _ := by ring

section main

variable (μ : Measure U) [IsProbabilityMeasure μ]

/-- **The cheap stand-in against the exact stand-in, general form.** `K` is a measurable
integrable function of the input with: at every `u`, either `λ(u) > 0` and
`hellG n (σ(u)/λ(u)) τ₀ ≤ K(u)`, or `1 ≤ K(u)`. Then for bounded measurable `φ`:
`(E_{ν_c} φ − E_{ν′} φ)² ≤ 2·E_u K·(E_{ν_c} φ² + E_{ν′} φ²)`. -/
theorem cheap_mix (hn : 2 ≤ n) (v : ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) {h : U → Fin m → ℝ}
    (hh : Measurable h) {τ₀ : ℝ} (hτ₀ : 0 < τ₀) {K : U → ℝ} (hKm : Measurable K)
    (hKi : Integrable K μ)
    (hK : ∀ u, (0 < lam b (h u) ∧ hellG n (sig v b (h u) / lam b (h u)) τ₀ ≤ K u) ∨ 1 ≤ K u)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    (∫ x, φ x ∂standIn μ h v b c - ∫ x, φ x ∂cheapIn c τ₀) ^ 2 ≤
      2 * (∫ u, K u ∂μ) *
        (∫ x, φ x ^ 2 ∂standIn μ h v b c + ∫ x, φ x ^ 2 ∂cheapIn c τ₀) := by
  have hK0 : ∀ u, 0 ≤ K u := by
    intro u
    rcases hK u with ⟨_, h2⟩ | h2
    · exact (hellG_nonneg _ _ _).trans h2
    · linarith
  have bF : BM (stF φ v b c h) := bm_stF v b c hh hφ
  have bF2 : BM (stF (fun x => φ x ^ 2) v b c h) := bm_stF v b c hh hφ.sq
  set G : ℝ := ∫ γ, φ (sphPt (c + τ₀ • γ)) ∂stdGauss (Fin n) with hG
  set A' : ℝ := ∫ γ, φ (sphPt (c + τ₀ • γ)) ^ 2 ∂stdGauss (Fin n) with hA'
  set J : U → ℝ := fun u => (∫ γ, stF φ v b c h (u, γ) ∂stdGauss (Fin n)) - G with hJ
  set A : U → ℝ := fun u => ∫ γ, stF (fun x => φ x ^ 2) v b c h (u, γ) ∂stdGauss (Fin n)
    with hA
  have bJ : BM J := (bF.integral_right _).sub (BM.const G)
  have bA : BM A := bF2.integral_right _
  have hA0 : ∀ u, 0 ≤ A u := fun u => integral_nonneg fun γ => sq_nonneg _
  have hA'0 : 0 ≤ A' := integral_nonneg fun γ => sq_nonneg _
  have bG : BM (fun γ : Fin n → ℝ => φ (sphPt (c + τ₀ • γ))) :=
    hφ.comp (measurable_cheapOut c τ₀)
  have hpt : ∀ u, J u ^ 2 ≤ 2 * K u * (A u + A') := by
    intro u
    have hsum0 : 0 ≤ A u + A' := add_nonneg (hA0 u) hA'0
    rcases hK u with ⟨hl, h2⟩ | h2
    · have hs : 0 ≤ sig v b (h u) := by unfold sig; positivity
      have h3 := pt_hell (by omega : 2 ≤ n) c hl hs hτ₀ hφ
      have h4 : 2 * hellG n (sig v b (h u) / lam b (h u)) τ₀ * (A u + A') ≤
          2 * K u * (A u + A') :=
        mul_le_mul_of_nonneg_right (by linarith) hsum0
      exact h3.trans h4
    · have bu : BM (fun γ : Fin n → ℝ => stF φ v b c h (u, γ)) :=
        bF.comp measurable_prodMk_left
      have j1 := sq_integral_le (ρ := stdGauss (Fin n)) (bu.sq.integrable _)
      have j2 := sq_integral_le (ρ := stdGauss (Fin n)) (bG.sq.integrable _)
      have j3 : J u ^ 2 ≤ 2 * (A u + A') := by
        simp only [hJ, hA, hA', hG]
        simp only [stF] at j1 ⊢
        nlinarith [sq_nonneg ((∫ γ, φ (sphPt (lam b (h u) • c + sig v b (h u) • γ))
          ∂stdGauss (Fin n)) + ∫ γ, φ (sphPt (c + τ₀ • γ)) ∂stdGauss (Fin n))]
      have : 2 * (A u + A') ≤ 2 * K u * (A u + A') := by nlinarith
      linarith
  have hmix := mix_cs μ bJ bA hA0 hA'0 hKm hK0 hKi hpt
  have e1 : ∫ u, J u ∂μ = ∫ x, φ x ∂standIn μ h v b c - ∫ x, φ x ∂cheapIn c τ₀ := by
    simp only [hJ]
    rw [integral_sub ((bF.integral_right _).integrable μ) (integrable_const _),
      integral_standIn μ v b c hh hφ, integral_cheapIn c τ₀ hφ.meas]
    simp only [stF, integral_const, probReal_univ, one_smul]
    rfl
  have e2 : ∫ u, A u ∂μ = ∫ x, φ x ^ 2 ∂standIn μ h v b c := by
    rw [integral_standIn μ v b c hh hφ.sq]
    rfl
  have e3 : A' = ∫ x, φ x ^ 2 ∂cheapIn c τ₀ := by
    rw [integral_cheapIn c τ₀ (hφ.meas.pow_const 2)]
  rw [e1, e2, e3] at hmix
  exact hmix

end main

end BstLean.Part138

open BstLean.Part138 in
#print axioms cheap_mix
open BstLean.Part138 in
#print axioms gaussScale138_sph
