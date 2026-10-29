import BstLean.Part105Gebelein

/-!
# Part 105: Theorem 1 of round oaW1 in an abstract form

Setting. `(U, μ)` is a probability space of inputs `u`; `(Ω, P)` is a probability space;
`R : Ω → U → ℝ^ι` is a jointly measurable random field such that for all `u, u′` the pair
`(R(u), R(u′))` has the distribution of `(τ X, τ(ρ X + √(1−ρ²) Z))`, `ρ = ρ(u, u′) ∈ [0, 1]`,
`X, Z` independent standard Gaussian vectors (`hlaw`). `f : U → ℝ^ι → ℝ` is bounded and jointly
measurable. `∫ ρ(u, u′) dμ(u′) ≤ lam` for every `u`.

* `Bmu ω = E_u f_u(R(u))`, `Bnu = E_u E_g f_u(τ g)`.
* `abstract_mean`: `E_R Bmu = Bnu` (Step 3).
* `abstract_var`: `E_R (Bmu − Bnu)² ≤ lam · Vnoise`, `Vnoise = E_u Var_g f_u(τ g)` (Steps 4 to 7).
* `Vnoise_le_Vnu`: `Vnoise ≤ Vnu = E_{u,g} (f_u(τ g) − Bnu)²` (Step 8).

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part105

open MeasureTheory
open BstLean.Part29 (stdGauss)

section abstract

set_option linter.unusedSectionVars false

variable {U Ω : Type*} [MeasurableSpace U] [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
  (μ : Measure U) [IsProbabilityMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]
  (R : Ω → U → ι → ℝ) (ρ : U → U → ℝ) (τ lam : ℝ) (f : U → (ι → ℝ) → ℝ)

/-- `E_u f_u(R(u))` for one realization `ω` of the field. -/
noncomputable def Bmu (ω : Ω) : ℝ := ∫ u, f u (R ω u) ∂μ

/-- The noise mean `m(u) = E_g f_u(τ g)`. -/
noncomputable def mNoise (u : U) : ℝ := ∫ g, f u (τ • g) ∂stdGauss ι

/-- `E_u E_g f_u(τ g)`. -/
noncomputable def Bnu : ℝ := ∫ u, mNoise τ f u ∂μ

/-- `E_u Var_g f_u(τ g)`. -/
noncomputable def Vnoise : ℝ := ∫ u, ∫ g, (f u (τ • g) - mNoise τ f u) ^ 2 ∂stdGauss ι ∂μ

/-- `E_{u,g} (f_u(τ g) − Bnu)²`: the variance under the stand-in. -/
noncomputable def Vnu : ℝ := ∫ u, ∫ g, (f u (τ • g) - Bnu μ τ f) ^ 2 ∂stdGauss ι ∂μ

variable (hR : Measurable (fun p : Ω × U => R p.1 p.2))
  (hρm : Measurable (fun p : U × U => ρ p.1 p.2))
  (hρ0 : ∀ u u', 0 ≤ ρ u u') (hρ1 : ∀ u u', ρ u u' ≤ 1) (hρs : ∀ u u', ρ u u' = ρ u' u)
  (hlam : ∀ u, ∫ u', ρ u u' ∂μ ≤ lam)
  (hlaw : ∀ u u', P.map (fun ω => (R ω u, R ω u')) =
    ((stdGauss ι).prod (stdGauss ι)).map
      (fun p => (τ • p.1, τ • (ρ u u' • p.1 + sC (ρ u u') • p.2))))
  (hf : BM (fun p : U × (ι → ℝ) => f p.1 p.2))

omit [IsProbabilityMeasure P] in
include hR in
lemma meas_pairR (u u' : U) : Measurable (fun ω => (R ω u, R ω u')) :=
  (hR.comp (measurable_id.prodMk measurable_const)).prodMk
    (hR.comp (measurable_id.prodMk measurable_const))

omit [IsProbabilityMeasure P] in
include hR hlaw in
/-- The pair distribution, as an identity of integrals. -/
lemma pair_integral (u u' : U) (H : (ι → ℝ) × (ι → ℝ) → ℝ) (hH : Measurable H) :
    ∫ ω, H (R ω u, R ω u') ∂P =
      ∫ p, H (τ • p.1, τ • (ρ u u' • p.1 + sC (ρ u u') • p.2))
        ∂((stdGauss ι).prod (stdGauss ι)) := by
  have hm2 : Measurable (fun p : (ι → ℝ) × (ι → ℝ) =>
      (τ • p.1, τ • (ρ u u' • p.1 + sC (ρ u u') • p.2))) :=
    (measurable_fst.const_smul τ).prodMk ((meas_comb _ _).const_smul τ)
  rw [← integral_map (meas_pairR R hR u u').aemeasurable hH.aestronglyMeasurable, hlaw u u',
    integral_map hm2.aemeasurable hH.aestronglyMeasurable]

omit [IsProbabilityMeasure P] in
include hR hlaw in
/-- The distribution at one point: `R(u) ∼ τ g`. -/
lemma single_integral (u : U) (H : (ι → ℝ) → ℝ) (hH : Measurable H) :
    ∫ ω, H (R ω u) ∂P = ∫ g, H (τ • g) ∂stdGauss ι := by
  have := pair_integral P R ρ τ hR hlaw u u (fun p => H p.1) (hH.comp measurable_fst)
  rw [this, integral_fun_fst (fun x : ι → ℝ => H (τ • x))]
  simp

omit [IsProbabilityMeasure μ] in
include hf in
lemma meas_f_left (u : U) : Measurable (f u) :=
  hf.meas.comp (measurable_const.prodMk measurable_id)

omit [IsProbabilityMeasure μ] in
include hf in
lemma bm_f_left (u : U) : BM (f u) := hf.comp (measurable_const.prodMk measurable_id)

omit [IsProbabilityMeasure μ] in
include hf in
lemma bm_ftau : BM (fun p : U × (ι → ℝ) => f p.1 (τ • p.2)) :=
  hf.comp (measurable_fst.prodMk (measurable_snd.const_smul τ))

omit [IsProbabilityMeasure μ] in
include hf in
lemma bm_mNoise : BM (mNoise τ f) := (bm_ftau τ f hf).integral_right (stdGauss ι)

include hR hlaw hf in
/-- **Theorem 1 (a), abstract form**: `E_R E_u f_u(R(u)) = E_u E_g f_u(τ g)`. -/
theorem abstract_mean : ∫ ω, Bmu μ R f ω ∂P = Bnu μ τ f := by
  have hb : BM (fun p : Ω × U => f p.2 (R p.1 p.2)) := hf.comp (measurable_snd.prodMk hR)
  unfold Bmu Bnu
  rw [integral_integral_swap (hb.integrable (P.prod μ))]
  congr 1
  funext u
  exact single_integral P R ρ τ hR hlaw u (f u) (meas_f_left f hf u)

/-- The centred function `k_u(z) = f_u(z) − m(u)`. -/
noncomputable def kc (u : U) (z : ι → ℝ) : ℝ := f u z - mNoise τ f u

/-- The noise variance `v(u) = Var_g f_u(τ g)`. -/
noncomputable def vNoise (u : U) : ℝ := ∫ g, kc τ f u (τ • g) ^ 2 ∂stdGauss ι

omit [IsProbabilityMeasure μ] in
include hf in
lemma bm_kc : BM (fun p : U × (ι → ℝ) => kc τ f p.1 p.2) :=
  hf.sub ((bm_mNoise τ f hf).comp measurable_fst)

omit [IsProbabilityMeasure μ] in
include hf in
lemma bm_vNoise : BM (vNoise τ f) :=
  (((bm_kc τ f hf).comp (measurable_fst.prodMk (measurable_snd.const_smul τ))).sq).integral_right
    (stdGauss ι)

omit [IsProbabilityMeasure μ] in
lemma vNoise_nonneg (u : U) : 0 ≤ vNoise τ f u := integral_nonneg fun _ => sq_nonneg _

omit [IsProbabilityMeasure μ] in
include hf in
lemma kc_mean (u : U) : ∫ g, kc τ f u (τ • g) ∂stdGauss ι = 0 := by
  unfold kc
  rw [integral_sub (((bm_f_left f hf u).comp (measurable_const_smul τ)).integrable _)
    (integrable_const _)]
  simp [mNoise]

include hR hρ0 hρ1 hlaw hf in
/-- Steps 4 and 6: the covariance of two values of the field. -/
lemma cov_le (u u' : U) :
    ∫ ω, kc τ f u (R ω u) * kc τ f u' (R ω u') ∂P ≤
      ρ u u' * ((vNoise τ f u + vNoise τ f u') / 2) := by
  have bk : ∀ u, BM (kc τ f u) := fun u =>
    (bm_kc τ f hf).comp (measurable_const.prodMk measurable_id)
  have bF : ∀ u, BM (fun x : ι → ℝ => kc τ f u (τ • x)) := fun u =>
    (bk u).comp (measurable_const_smul τ)
  have h1 := pair_integral P R ρ τ hR hlaw u u'
    (fun p => kc τ f u p.1 * kc τ f u' p.2)
    (((bk u).comp measurable_fst).mul ((bk u').comp measurable_snd)).meas
  rw [h1]
  have hρabs : |ρ u u'| ≤ 1 := by rw [abs_of_nonneg (hρ0 u u')]; exact hρ1 u u'
  have h2 := gebelein (ι := ι) hρabs (bF u) (bF u')
  rw [kc_mean τ f hf u, kc_mean τ f hf u'] at h2
  simp only [sub_zero, zero_mul, abs_of_nonneg (hρ0 u u')] at h2
  have h3 := (le_abs_self _).trans h2
  refine h3.trans ?_
  have ha := vNoise_nonneg τ f u
  have hb := vNoise_nonneg τ f u'
  have h4 : Real.sqrt (vNoise τ f u) * Real.sqrt (vNoise τ f u') ≤
      (vNoise τ f u + vNoise τ f u') / 2 := by
    nlinarith [sq_nonneg (Real.sqrt (vNoise τ f u) - Real.sqrt (vNoise τ f u')),
      Real.sq_sqrt ha, Real.sq_sqrt hb]
  calc ρ u u' * Real.sqrt (∫ x, kc τ f u (τ • x) ^ 2 ∂stdGauss ι) *
        Real.sqrt (∫ x, kc τ f u' (τ • x) ^ 2 ∂stdGauss ι)
      = ρ u u' * (Real.sqrt (vNoise τ f u) * Real.sqrt (vNoise τ f u')) := by
        unfold vNoise; ring
    _ ≤ ρ u u' * ((vNoise τ f u + vNoise τ f u') / 2) :=
        mul_le_mul_of_nonneg_left h4 (hρ0 u u')

include hR hρm hρ0 hρ1 hρs hlam hlaw hf in
/-- **Theorem 1 (b), abstract form**: `E_R (Bmu − Bnu)² ≤ lam · E_u Var_g f_u(τ g)`. -/
theorem abstract_var :
    ∫ ω, (Bmu μ R f ω - Bnu μ τ f) ^ 2 ∂P ≤ lam * Vnoise μ τ f := by
  have bK := bm_kc τ f hf
  have bm := bm_mNoise τ f hf
  have bv := bm_vNoise τ f hf
  have bfR : BM (fun p : Ω × U => f p.2 (R p.1 p.2)) := hf.comp (measurable_snd.prodMk hR)
  have bfRω : ∀ ω, BM (fun u => f u (R ω u)) := fun ω =>
    bfR.comp (measurable_const.prodMk measurable_id)
  -- the difference as one integral
  have hD : ∀ ω, Bmu μ R f ω - Bnu μ τ f = ∫ u, kc τ f u (R ω u) ∂μ := by
    intro ω
    unfold Bmu Bnu kc
    rw [integral_sub ((bfRω ω).integrable _) (bm.integrable _)]
  -- the square as a double integral
  set G : Ω × (U × U) → ℝ := fun p => kc τ f p.2.1 (R p.1 p.2.1) * kc τ f p.2.2 (R p.1 p.2.2)
    with hG
  have bKR : BM (fun p : Ω × U => kc τ f p.2 (R p.1 p.2)) := bK.comp (measurable_snd.prodMk hR)
  have bG : BM G :=
    (bKR.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (bKR.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hsq : ∀ ω, (Bmu μ R f ω - Bnu μ τ f) ^ 2 = ∫ q, G (ω, q) ∂(μ.prod μ) := by
    intro ω
    rw [hD ω, pow_two]
    exact (integral_prod_mul (μ := μ) (ν := μ) (fun u => kc τ f u (R ω u))
      (fun u => kc τ f u (R ω u))).symm
  simp_rw [hsq]
  rw [integral_integral_swap (bG.integrable (P.prod (μ.prod μ)))]
  -- pointwise covariance bound
  set Bd : U × U → ℝ := fun q => ρ q.1 q.2 * ((vNoise τ f q.1 + vNoise τ f q.2) / 2) with hBd
  have bρ : BM (fun q : U × U => ρ q.1 q.2) :=
    ⟨hρm, 1, fun q => by rw [abs_of_nonneg (hρ0 _ _)]; exact hρ1 _ _⟩
  have b1 : BM (fun q : U × U => ρ q.1 q.2 * vNoise τ f q.1) := bρ.mul (bv.comp measurable_fst)
  have b2 : BM (fun q : U × U => ρ q.1 q.2 * vNoise τ f q.2) := bρ.mul (bv.comp measurable_snd)
  have hmono : ∫ q, ∫ ω, G (ω, q) ∂P ∂(μ.prod μ) ≤ ∫ q, Bd q ∂(μ.prod μ) := by
    refine integral_mono ((bG.integral_left P).integrable _) ?_ ?_
    · have : Bd = fun q => (1 / 2) * (ρ q.1 q.2 * vNoise τ f q.1) +
          (1 / 2) * (ρ q.1 q.2 * vNoise τ f q.2) := by funext q; simp only [hBd]; ring
      rw [this]
      exact ((((BM.const _).mul b1).add ((BM.const _).mul b2))).integrable _
    · intro q
      exact cov_le P R ρ τ f hR hρ0 hρ1 hlaw hf q.1 q.2
  refine hmono.trans ?_
  have hI1 : ∫ q, ρ q.1 q.2 * vNoise τ f q.1 ∂(μ.prod μ) ≤ lam * ∫ u, vNoise τ f u ∂μ := by
    rw [integral_prod _ (b1.integrable _), ← integral_const_mul]
    refine integral_mono ((b1.integral_right μ).integrable _) ((BM.const lam).mul bv |>.integrable _) ?_
    intro u
    simp only [integral_mul_const]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hlam u) (vNoise_nonneg τ f u) |>.trans_eq (mul_comm _ _)
  have hI2 : ∫ q, ρ q.1 q.2 * vNoise τ f q.2 ∂(μ.prod μ) ≤ lam * ∫ u, vNoise τ f u ∂μ := by
    rw [integral_prod_symm _ (b2.integrable _), ← integral_const_mul]
    refine integral_mono ((b2.integral_left μ).integrable _) ((BM.const lam).mul bv |>.integrable _) ?_
    intro u'
    simp only [integral_mul_const]
    have : ∫ u, ρ u u' ∂μ ≤ lam := by
      have := hlam u'
      simp_rw [hρs u'] at this
      exact this
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left this (vNoise_nonneg τ f u') |>.trans_eq (mul_comm _ _)
  have hsplit : ∫ q, Bd q ∂(μ.prod μ) =
      (1 / 2) * ∫ q, ρ q.1 q.2 * vNoise τ f q.1 ∂(μ.prod μ) +
        (1 / 2) * ∫ q, ρ q.1 q.2 * vNoise τ f q.2 ∂(μ.prod μ) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (((BM.const _).mul b1).integrable _) (((BM.const _).mul b2).integrable _)]
    congr 1
    funext q
    simp only [hBd]; ring
  rw [hsplit]
  have hV : Vnoise μ τ f = ∫ u, vNoise τ f u ∂μ := rfl
  rw [hV]
  linarith

include hf in
/-- Step 8: the mean noise variance is at most the variance under the stand-in. -/
theorem Vnoise_le_Vnu : Vnoise μ τ f ≤ Vnu μ τ f := by
  have bK := bm_kc τ f hf
  have bft := bm_ftau τ f hf
  unfold Vnoise Vnu
  refine integral_mono ((bm_vNoise τ f hf).integrable _)
    (((bft.sub (BM.const (Bnu μ τ f))).sq.integral_right (stdGauss ι)).integrable _) ?_
  intro u
  set c := Bnu μ τ f
  set m := mNoise τ f u with hm
  have bfu : BM (fun g : ι → ℝ => f u (τ • g)) :=
    (bm_f_left f hf u).comp (measurable_const_smul τ)
  have hk0 := kc_mean τ f hf u
  have e : (fun g : ι → ℝ => (f u (τ • g) - c) ^ 2) = fun g =>
      (f u (τ • g) - m) ^ 2 + ((2 * (m - c)) * kc τ f u (τ • g) + (m - c) ^ 2) := by
    funext g; simp only [kc, ← hm]; ring
  have bk : BM (fun g : ι → ℝ => kc τ f u (τ • g)) := bfu.sub (BM.const _)
  show ∫ g, (f u (τ • g) - m) ^ 2 ∂stdGauss ι ≤ ∫ g, (f u (τ • g) - c) ^ 2 ∂stdGauss ι
  rw [e, integral_add ((bfu.sub (BM.const m)).sq.integrable _)
    ((((BM.const _).mul bk).add (BM.const _)).integrable _),
    integral_add (((BM.const _).mul bk).integrable _) (integrable_const _),
    integral_const_mul, hk0]
  simp only [mul_zero, zero_add, integral_const, probReal_univ, one_smul]
  nlinarith [sq_nonneg (m - c)]

end abstract

end BstLean.Part105
