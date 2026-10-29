import BstLean.Part134Split

/-!
# Part 134, item 2: the mean identity of the stand-in (`s1_mean`)

Role: `delegations/statements/p134-spec.md`, item 2 (paper Theorem S1, part (b)).
Do not use `sorry`, `native_decide` or `axiom`.

`μ` is a probability measure on a measurable space `U` (the input `u`; for the World network
`U = ℝ^N` and `μ = uniformSphere N`), `h : U → ℝ^m` is a measurable function (the last hidden
vector; `h = hid2 M₁ M₂`), `M` is an `n × m` Gaussian matrix with entry variance `v`, `b ≠ 0`.

* `muM μ h M`: the distribution of `x = sphPt (M h(u))`, `u ~ μ` (`muWn_eq_muM`: this is `μ_W`).
* `standIn μ h v b c`: the stand-in distribution `ν_c`: the distribution of
  `sphPt (λ(u)·c + σ(u)·γ)`, `u ~ μ`, `γ` an independent standard Gaussian vector of `ℝⁿ`.
* `s1_mean_pt`: for every `c` and every hidden vector `h`: the conditional distribution of the
  output given `c` is that of `λ c + σ γ` (inside every measurable test function).
* `s1_mean_cond`: the same, integrated over `u`: `E[E_{μ_W} φ | c] = E_{ν_c} φ`, with `M`
  replaced by `glue b c (M' P)` (see `s1_disint`).
* `s1_mean_test`: the conditional mean identity against every bounded measurable function of `c`.
* `s1_mean`: the identity of integrals `E_M E_{μ_W} φ = E_c E_{ν_c} φ`.
* `s1_mean_mlp`: `s1_mean` for the World network.
-/

namespace BstLean.Part134

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105 (BM)
open BstLean.Part130

variable {n m : ℕ} {U : Type*} [MeasurableSpace U]

/-- The distribution of `x = sphPt (M h(u))`, `u ~ μ`: the input distribution `μ_W` of the
network with last matrix `M` and last hidden vector `h(u)`. -/
noncomputable def muM (μ : Measure U) (h : U → Fin m → ℝ) (M : Matrix (Fin n) (Fin m) ℝ) :
    Measure (Fin n → ℝ) :=
  μ.map (fun u => sphPt (M.mulVec (h u)))

/-- **The stand-in distribution `ν_c`**: the distribution of `sphPt (λ(u)·c + σ(u)·γ)`,
`u ~ μ`, `γ` an independent standard Gaussian vector of `ℝⁿ`; `λ(u) = lam b (h u)`,
`σ(u) = sig v b (h u)`. -/
noncomputable def standIn (μ : Measure U) (h : U → Fin m → ℝ) (v : ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  (μ.prod (stdGauss (Fin n))).map
    (fun p => sphPt (lam b (h p.1) • c + sig v b (h p.1) • p.2))

/-! ## Measurability -/

lemma measurable_lam (b : Fin m → ℝ) : Measurable (lam b) := by
  unfold lam
  exact (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).mul_const _).div_const _

lemma measurable_res (b : Fin m → ℝ) : Measurable (res b) := by
  unfold res
  exact measurable_id.sub ((measurable_lam b).smul_const b)

lemma measurable_sig (v : ℝ) (b : Fin m → ℝ) : Measurable (sig v b) := by
  unfold sig
  exact (measurable_normSq.comp (measurable_res b)).sqrt.const_mul _

lemma measurable_mulVec_joint :
    Measurable (fun p : Matrix (Fin n) (Fin m) ℝ × (Fin m → ℝ) => p.1.mulVec p.2) := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ fun j _ =>
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst)).mul
      ((measurable_pi_apply j).comp measurable_snd)

lemma glue_res (b : Fin m → ℝ) (c : Fin n → ℝ) (M : Matrix (Fin n) (Fin m) ℝ) (h : Fin m → ℝ) :
    (glue b c (M * projPerp b)).mulVec h = lam b h • c + M.mulVec (res b h) := by
  rw [glue_mulVec, mul_projPerp_mulVec]

/-- `(M, u) ↦ λ(u)·c + M r(u)` is measurable. -/
lemma measurable_condOut {h : U → Fin m → ℝ} (hh : Measurable h) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Measurable (fun q : Matrix (Fin n) (Fin m) ℝ × U =>
      lam b (h q.2) • c + q.1.mulVec (res b (h q.2))) :=
  (((measurable_lam b).comp (hh.comp measurable_snd)).smul_const c).add
    (measurable_mulVec_joint.comp
      (measurable_fst.prodMk ((measurable_res b).comp (hh.comp measurable_snd))))

/-- `(u, γ) ↦ λ(u)·c + σ(u)·γ` is measurable. -/
lemma measurable_standOut {h : U → Fin m → ℝ} (hh : Measurable h) (v : ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) :
    Measurable (fun p : U × (Fin n → ℝ) => lam b (h p.1) • c + sig v b (h p.1) • p.2) :=
  (((measurable_lam b).comp (hh.comp measurable_fst)).smul_const c).add
    (((measurable_sig v b).comp (hh.comp measurable_fst)).smul measurable_snd)

lemma measurable_out {h : U → Fin m → ℝ} (hh : Measurable h) :
    Measurable (fun q : Matrix (Fin n) (Fin m) ℝ × U => q.1.mulVec (h q.2)) :=
  measurable_mulVec_joint.comp (measurable_fst.prodMk (hh.comp measurable_snd))

/-! ## The conditional distribution at one input -/

/-- **Theorem S1 (b), at one input.** For every `c`, every hidden vector `h` and every measurable
`φ`: with `M = glue b c (M' P)` (the matrix given `c`; `M'` a Gaussian matrix),
`E φ(sphPt(M h)) = E_γ φ(sphPt(λ c + σ γ))`. -/
theorem s1_mean_pt (v : ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (h : Fin m → ℝ)
    {φ : (Fin n → ℝ) → ℝ} (hφ : Measurable φ) :
    ∫ M', φ (sphPt ((glue b c (M' * projPerp b)).mulVec h)) ∂gaussMat n m v =
      ∫ γ, φ (sphPt (lam b h • c + sig v b h • γ)) ∂stdGauss (Fin n) := by
  simp_rw [glue_res]
  set g : (Fin n → ℝ) → ℝ := fun y => φ (sphPt (lam b h • c + y)) with hg
  have hgm : Measurable g :=
    hφ.comp (measurable_sphPt.comp (measurable_const.add measurable_id))
  have hs : Measurable (fun ξ : Fin n → ℝ => sig v b h • ξ) :=
    (continuous_id.const_smul (sig v b h)).measurable
  calc ∫ M', g (M'.mulVec (res b h)) ∂gaussMat n m v
      = ∫ y, g y ∂(gaussMat n m v).map (fun M => M.mulVec (res b h)) :=
        (integral_map (measurable_mulVec_right _).aemeasurable hgm.aestronglyMeasurable).symm
    _ = ∫ y, g y ∂(stdGauss (Fin n)).map (fun ξ => sig v b h • ξ) := by
        rw [gaussMat_mulVec]; rfl
    _ = ∫ γ, g (sig v b h • γ) ∂stdGauss (Fin n) :=
        integral_map hs.aemeasurable hgm.aestronglyMeasurable

variable (μ : Measure U) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma integral_muM {h : U → Fin m → ℝ} (hh : Measurable h) {φ : (Fin n → ℝ) → ℝ}
    (hφ : Measurable φ) (M : Matrix (Fin n) (Fin m) ℝ) :
    ∫ x, φ x ∂muM μ h M = ∫ u, φ (sphPt (M.mulVec (h u))) ∂μ :=
  integral_map (measurable_sphPt.comp ((measurable_mulVec_left M).comp hh)).aemeasurable
    hφ.aestronglyMeasurable

/-- `E_{ν_c} φ = E_u E_γ φ(sphPt(λ(u) c + σ(u) γ))`. -/
lemma integral_standIn (v : ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) {h : U → Fin m → ℝ}
    (hh : Measurable h) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ x, φ x ∂standIn μ h v b c =
      ∫ u, (∫ γ, φ (sphPt (lam b (h u) • c + sig v b (h u) • γ)) ∂stdGauss (Fin n)) ∂μ := by
  have hm : Measurable (fun p : U × (Fin n → ℝ) =>
      sphPt (lam b (h p.1) • c + sig v b (h p.1) • p.2)) :=
    measurable_sphPt.comp (measurable_standOut hh v b c)
  have hG : BM (fun p : U × (Fin n → ℝ) =>
      φ (sphPt (lam b (h p.1) • c + sig v b (h p.1) • p.2))) := hφ.comp hm
  unfold standIn
  rw [integral_map hm.aemeasurable hφ.meas.aestronglyMeasurable, integral_prod _ (hG.integrable _)]

/-- `M ↦ E_{μ_M} φ` is bounded and measurable. -/
lemma bm_muM {h : U → Fin m → ℝ} (hh : Measurable h) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    BM (fun M : Matrix (Fin n) (Fin m) ℝ => ∫ x, φ x ∂muM μ h M) := by
  have h1 : BM (fun q : Matrix (Fin n) (Fin m) ℝ × U => φ (sphPt (q.1.mulVec (h q.2)))) :=
    hφ.comp (measurable_sphPt.comp (measurable_out hh))
  have h2 := h1.integral_right μ
  have e : (fun M : Matrix (Fin n) (Fin m) ℝ => ∫ x, φ x ∂muM μ h M) =
      fun M => ∫ u, φ (sphPt (M.mulVec (h u))) ∂μ := by
    funext M; exact integral_muM μ hh hφ.meas M
  rw [e]; exact h2

/-- **Theorem S1 (b), the conditional mean.** For every `c`: with `M = glue b c (M' P)` (the
matrix given `c = M b`, see `s1_disint`), `E_{M'} E_{μ_M} φ = E_{ν_c} φ`. -/
theorem s1_mean_cond (v : ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) {h : U → Fin m → ℝ}
    (hh : Measurable h) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ M', (∫ x, φ x ∂muM μ h (glue b c (M' * projPerp b))) ∂gaussMat n m v =
      ∫ x, φ x ∂standIn μ h v b c := by
  simp_rw [integral_muM μ hh hφ.meas, glue_res]
  have hF : BM (fun q : Matrix (Fin n) (Fin m) ℝ × U =>
      φ (sphPt (lam b (h q.2) • c + q.1.mulVec (res b (h q.2))))) :=
    hφ.comp (measurable_sphPt.comp (measurable_condOut hh b c))
  rw [integral_integral_swap (hF.integrable ((gaussMat n m v).prod μ)),
    integral_standIn μ v b c hh hφ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have := s1_mean_pt v b c (h u) hφ.meas
  simp_rw [glue_res] at this
  exact this

/-- `c ↦ E_{ν_c} φ` is bounded and measurable. -/
lemma bm_standIn (v : ℝ) (b : Fin m → ℝ) {h : U → Fin m → ℝ}
    (hh : Measurable h) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    BM (fun c : Fin n → ℝ => ∫ x, φ x ∂standIn μ h v b c) := by
  have e : (fun c : Fin n → ℝ => ∫ x, φ x ∂standIn μ h v b c) =
      fun c => ∫ M', (∫ x, φ x ∂muM μ h (glue b c (M' * projPerp b))) ∂gaussMat n m v := by
    funext c; exact (s1_mean_cond μ v b c hh hφ).symm
  rw [e]
  have h1 : BM (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      ∫ x, φ x ∂muM μ h (glue b p.1 (p.2 * projPerp b))) :=
    (bm_muM μ hh hφ).comp ((measurable_glue b).comp
      (measurable_fst.prodMk ((measurable_mul_right _).comp measurable_snd)))
  exact h1.integral_right (gaussMat n m v)

/-- **Theorem S1 (b), the conditional mean identity against every test function of `c`.** For
every bounded measurable `k`: `E[k(M b)·E_{μ_M} φ] = E_c[k(c)·E_{ν_c} φ]`, `c ~ N(0, v|b|² I_n)`.
This is the statement `E[E_{μ_M} φ | M b = c] = E_{ν_c} φ` for almost every `c`. -/
theorem s1_mean_test (v : ℝ) {b : Fin m → ℝ} (hb : b ≠ 0) {h : U → Fin m → ℝ}
    (hh : Measurable h) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) {k : (Fin n → ℝ) → ℝ} (hk : BM k) :
    ∫ M, k (M.mulVec b) * (∫ x, φ x ∂muM μ h M) ∂gaussMat n m v =
      ∫ c, k c * (∫ x, φ x ∂standIn μ h v b c) ∂cDist n v b := by
  have hΨ : BM (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      k p.1 * ∫ x, φ x ∂muM μ h p.2) :=
    (hk.comp measurable_fst).mul ((bm_muM μ hh hφ).comp measurable_snd)
  have hm1 : Measurable (fun M : Matrix (Fin n) (Fin m) ℝ => (M.mulVec b, M)) :=
    (measurable_mulVec_right b).prodMk measurable_id
  have hm2 : Measurable (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      (p.1, glue b p.1 (p.2 * projPerp b))) :=
    measurable_fst.prodMk ((measurable_glue b).comp
      (measurable_fst.prodMk ((measurable_mul_right _).comp measurable_snd)))
  have e1 : ∫ M, k (M.mulVec b) * (∫ x, φ x ∂muM μ h M) ∂gaussMat n m v =
      ∫ p, k p.1 * (∫ x, φ x ∂muM μ h p.2) ∂(gaussMat n m v).map (fun M => (M.mulVec b, M)) :=
    (integral_map hm1.aemeasurable hΨ.meas.aestronglyMeasurable).symm
  rw [e1, s1_disint v hb, integral_map hm2.aemeasurable hΨ.meas.aestronglyMeasurable,
    integral_prod _ ((hΨ.comp hm2).integrable _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
  simp only []
  rw [integral_const_mul, s1_mean_cond μ v b c hh hφ]

/-- **Theorem S1 (b), the mean identity** (`E_{M} E_{μ_M} φ = E_c E_{ν_c} φ`): for `b ≠ 0` and
bounded measurable `φ`, with `c ~ N(0, v|b|²·I_n)`. -/
theorem s1_mean (v : ℝ) {b : Fin m → ℝ} (hb : b ≠ 0) {h : U → Fin m → ℝ}
    (hh : Measurable h) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ M, (∫ x, φ x ∂muM μ h M) ∂gaussMat n m v =
      ∫ c, (∫ x, φ x ∂standIn μ h v b c) ∂cDist n v b := by
  have := s1_mean_test μ v hb hh hφ (BM.const (α := Fin n → ℝ) 1)
  simpa using this

/-- **`s1_mean` with every integral written out**:
`∫∫ φ(sphPt(M h(u))) dM dμ(u) = ∫∫∫ φ(sphPt(λ(u) c + σ(u) γ)) dγ dμ(u) dc`. -/
theorem s1_mean_explicit (v : ℝ) {b : Fin m → ℝ} (hb : b ≠ 0) {h : U → Fin m → ℝ}
    (hh : Measurable h) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ u, (∫ M, φ (sphPt (M.mulVec (h u))) ∂gaussMat n m v) ∂μ =
      ∫ c, (∫ u, (∫ γ, φ (sphPt (lam b (h u) • c + sig v b (h u) • γ)) ∂stdGauss (Fin n)) ∂μ)
        ∂cDist n v b := by
  have h1 : BM (fun q : Matrix (Fin n) (Fin m) ℝ × U => φ (sphPt (q.1.mulVec (h q.2)))) :=
    hφ.comp (measurable_sphPt.comp (measurable_out hh))
  have key := s1_mean μ v hb hh hφ
  simp_rw [integral_muM μ hh hφ.meas] at key
  rw [integral_integral_swap (h1.integrable ((gaussMat n m v).prod μ))] at key
  rw [key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
  exact integral_standIn μ v b c hh hφ

/-! ## The World network -/

lemma continuous_hid2 {k m₁ m₂ : ℕ} (M₁ : Matrix (Fin m₁) (Fin k) ℝ)
    (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ) : Continuous (hid2 M₁ M₂) := by
  unfold hid2
  exact continuous_reluV.comp ((Continuous.matrix_mulVec continuous_const continuous_id).comp
    (continuous_reluV.comp (Continuous.matrix_mulVec continuous_const continuous_id)))

/-- `μ_W` of Part 130 is `muM` with `μ` uniform on the sphere and `h` the last hidden vector. -/
theorem muWn_eq_muM {N m₁ : ℕ} (M₁ : Matrix (Fin m₁) (Fin N) ℝ) (M₂ : Matrix (Fin m) (Fin m₁) ℝ)
    (M₃ : Matrix (Fin n) (Fin m) ℝ) :
    (uniformSphere N).map (fun u => sphPt (mlp2 M₁ M₂ M₃ u)) =
      muM (uniformSphere N) (hid2 M₁ M₂) M₃ := rfl

/-- **Theorem S1 (b) for the World network** `W = (M₁, M₂, M₃)`, `M₃` Gaussian with variance
`2/m`, `(M₁, M₂)` fixed, `b ≠ 0`: `E_{M₃} E_{μ_W} φ = E_c E_{ν_c} φ`. -/
theorem s1_mean_mlp {N : ℕ} (hN : 1 ≤ N) (M₁ : Matrix (Fin m) (Fin N) ℝ)
    (M₂ : Matrix (Fin m) (Fin m) ℝ) {b : Fin m → ℝ} (hb : b ≠ 0)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ M₃, (∫ x, φ x ∂muWn ((M₁, M₂, M₃) : MlpParam N m n)) ∂gaussMat n m (2 / (m : ℝ)) =
      ∫ c, (∫ x, φ x ∂standIn (uniformSphere N) (hid2 M₁ M₂) (2 / (m : ℝ)) b c)
        ∂cDist n (2 / (m : ℝ)) b := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  exact s1_mean (uniformSphere N) (2 / (m : ℝ)) hb (continuous_hid2 M₁ M₂).measurable hφ

end BstLean.Part134

open BstLean.Part134 in
#print axioms s1_mean_pt
open BstLean.Part134 in
#print axioms s1_mean_cond
open BstLean.Part134 in
#print axioms s1_mean_test
open BstLean.Part134 in
#print axioms s1_mean
open BstLean.Part134 in
#print axioms s1_mean_explicit
open BstLean.Part134 in
#print axioms s1_mean_mlp
