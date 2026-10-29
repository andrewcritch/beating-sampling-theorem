import BstLean.Part134All
import BstLean.Part136Det
import BstLean.Part137Hat2

/-!
# Part 149, item 1: the stand-in theorem for an UNNORMALIZED output

Do not use `sorry`, `native_decide` or `axiom`.

Role: `delegations/statements/p149-spec.md`, item 1 (paper: Theorem S1-A of round onW42). Part 134
has the stand-in theorem for the normalized output `sphPt (M h(u))` and a bounded test function.
For the Agent network `A` the test function is `F`, applied to the unnormalized output `A₃ a₂(x)`,
and `F` is not bounded. This file has:

* `outTrue μ h ψ M = E_u ψ(M h(u))` and `outStand μ h v b ψ c = E_u E_γ ψ(λ(u)·c + σ(u)·γ)`.
* `standIn_mse_bdd`: for a bounded measurable `ψ`:
  `E_M (outTrue M − outStand (M b))² ≤ L · E_c E_u Var_γ ψ(λ(u)c + σ(u)γ)` (from `s1_var_family` and
  `s1_disint` of Part 134).
* `standIn_lint`: the same for a measurable `ψ` with `ψ(y)² ≤ C(1 + |y|²)` and a bounded hidden
  map, with the variance replaced by the second moment about `ψ(λ(u)c)`, in `ℝ≥0∞` (so that no
  integrability is a hypothesis). The proof truncates `ψ` and uses Fatou's lemma.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part134

variable {n m : ℕ} {U : Type*} [MeasurableSpace U]

/-- `E_u ψ(M h(u))`: the mean of the test function `ψ` of the unnormalized output. -/
noncomputable def outTrue (μ : Measure U) (h : U → Fin m → ℝ) (ψ : (Fin n → ℝ) → ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∫ u, ψ (M.mulVec (h u)) ∂μ

/-- `E_u E_γ ψ(λ(u)·c + σ(u)·γ)`: the mean of `ψ` over the stand-in with centre `c`. -/
noncomputable def outStand (μ : Measure U) (h : U → Fin m → ℝ) (v : ℝ) (b : Fin m → ℝ)
    (ψ : (Fin n → ℝ) → ℝ) (c : Fin n → ℝ) : ℝ :=
  ∫ u, ∫ γ, ψ (lam b (h u) • c + sig v b (h u) • γ) ∂stdGauss (Fin n) ∂μ

/-- `((c, u), γ) ↦ λ(u)·c + σ(u)·γ` is measurable. -/
lemma measurable_standOut3 {h : U → Fin m → ℝ} (hh : Measurable h) (v : ℝ) (b : Fin m → ℝ) :
    Measurable (fun q : ((Fin n → ℝ) × U) × (Fin n → ℝ) =>
      lam b (h q.1.2) • q.1.1 + sig v b (h q.1.2) • q.2) :=
  (((measurable_lam b).comp (hh.comp (measurable_snd.comp measurable_fst))).smul
    (measurable_fst.comp measurable_fst)).add
    (((measurable_sig v b).comp (hh.comp (measurable_snd.comp measurable_fst))).smul measurable_snd)

lemma var_le_sq_sub {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    {X : α → ℝ} (hX : BM X) (a : ℝ) : Var[X; P] ≤ ∫ x, (X x - a) ^ 2 ∂P := by
  rw [var_bm P hX]
  have i2 := hX.sq.integrable P
  have i1 := hX.integrable P
  have e2 : ∫ x, (X x - a) ^ 2 ∂P = ∫ x, X x ^ 2 ∂P - 2 * a * ∫ x, X x ∂P + a ^ 2 := by
    have e : (fun x => (X x - a) ^ 2) = fun x => (X x ^ 2 - 2 * a * X x) + a ^ 2 := by
      funext x; ring
    rw [e, integral_add (f := fun x => X x ^ 2 - 2 * a * X x) (g := fun _ => a ^ 2)
      (i2.sub (i1.const_mul _)) (integrable_const _),
      integral_sub (f := fun x => X x ^ 2) (g := fun x => 2 * a * X x) i2 (i1.const_mul _),
      integral_const_mul]
    simp
  rw [e2]
  nlinarith [sq_nonneg (∫ x, X x ∂P - a)]

section bounded

variable (μ : Measure U) [IsProbabilityMeasure μ]

lemma bm_outTrue {h : U → Fin m → ℝ} (hh : Measurable h) {ψ : (Fin n → ℝ) → ℝ} (hψ : BM ψ) :
    BM (fun M : Matrix (Fin n) (Fin m) ℝ => outTrue μ h ψ M) :=
  BM.integral_right (H := fun q : Matrix (Fin n) (Fin m) ℝ × U => ψ (q.1.mulVec (h q.2)))
    (hψ.comp (measurable_out hh)) μ

lemma bm_outStand {h : U → Fin m → ℝ} (hh : Measurable h) (v : ℝ) (b : Fin m → ℝ)
    {ψ : (Fin n → ℝ) → ℝ} (hψ : BM ψ) :
    BM (fun c : Fin n → ℝ => outStand μ h v b ψ c) := by
  have b1 : BM (fun q : ((Fin n → ℝ) × U) × (Fin n → ℝ) =>
      ψ (lam b (h q.1.2) • q.1.1 + sig v b (h q.1.2) • q.2)) :=
    hψ.comp (measurable_standOut3 hh v b)
  have b2 := b1.integral_right (stdGauss (Fin n))
  exact BM.integral_right (H := fun p : (Fin n → ℝ) × U =>
    ∫ γ, ψ (lam b (h p.2) • p.1 + sig v b (h p.2) • γ) ∂stdGauss (Fin n)) b2 μ

/-- **The stand-in theorem for an unnormalized output, bounded test function.** `μ` a
probability measure on the inputs, `h` the measurable hidden map, `b ≠ 0` the centre, `M` a
Gaussian matrix with entry variance `v`, `L` a frame bound of the unit residual directions. Then
`E_M (E_u ψ(M h(u)) − E_u E_γ ψ(λ(u)·M b + σ(u)·γ))² ≤ L · E_c E_u Var_γ ψ(λ(u)c + σ(u)γ)`,
`c ~ N(0, v|b|²·I_n)`. -/
theorem standIn_mse_bdd (v : ℝ) {b : Fin m → ℝ} (hb : b ≠ 0) {h : U → Fin m → ℝ}
    (hh : Measurable h) {ψ : (Fin n → ℝ) → ℝ} (hψ : BM ψ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : Fin m → ℝ, ∫ u, (∑ j, eDir b (h u) j * w j) ^ 2 ∂μ ≤ L * ∑ j, w j ^ 2) :
    ∫ M, (outTrue μ h ψ M - outStand μ h v b ψ (M.mulVec b)) ^ 2 ∂gaussMat n m v ≤
      L * ∫ c, (∫ u, Var[fun γ => ψ (lam b (h u) • c + sig v b (h u) • γ); stdGauss (Fin n)] ∂μ)
        ∂cDist n v b := by
  have bT := bm_outTrue (n := n) μ hh hψ
  have bN := bm_outStand (n := n) μ hh v b hψ
  have bΘ : BM (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      (outTrue μ h ψ p.2 - outStand μ h v b ψ p.1) ^ 2) :=
    ((bT.comp measurable_snd).sub (bN.comp measurable_fst)).sq
  have hm1 : Measurable (fun M : Matrix (Fin n) (Fin m) ℝ => (M.mulVec b, M)) :=
    (measurable_mulVec_right b).prodMk measurable_id
  have hm2 : Measurable (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      (p.1, glue b p.1 (p.2 * projPerp b))) :=
    measurable_fst.prodMk ((measurable_glue b).comp
      (measurable_fst.prodMk ((measurable_mul_right _).comp measurable_snd)))
  have e1 : ∫ M, (outTrue μ h ψ M - outStand μ h v b ψ (M.mulVec b)) ^ 2 ∂gaussMat n m v =
      ∫ p, (outTrue μ h ψ p.2 - outStand μ h v b ψ p.1) ^ 2
        ∂(gaussMat n m v).map (fun M => (M.mulVec b, M)) :=
    (integral_map hm1.aemeasurable bΘ.meas.aestronglyMeasurable).symm
  rw [e1, s1_disint v hb, integral_map hm2.aemeasurable bΘ.meas.aestronglyMeasurable,
    integral_prod _ ((bΘ.comp hm2).integrable _), ← integral_const_mul]
  -- the variance as a bounded measurable function of `(c, u)`
  have b1 : BM (fun q : ((Fin n → ℝ) × U) × (Fin n → ℝ) =>
      ψ (lam b (h q.1.2) • q.1.1 + sig v b (h q.1.2) • q.2)) :=
    hψ.comp (measurable_standOut3 hh v b)
  have hvar : ∀ (c : Fin n → ℝ) (u : U),
      Var[fun γ => ψ (lam b (h u) • c + sig v b (h u) • γ); stdGauss (Fin n)] =
        ∫ γ, ψ (lam b (h u) • c + sig v b (h u) • γ) ^ 2 ∂stdGauss (Fin n) -
          (∫ γ, ψ (lam b (h u) • c + sig v b (h u) • γ) ∂stdGauss (Fin n)) ^ 2 := by
    intro c u
    exact var_bm (stdGauss (Fin n)) (X := fun γ => ψ (lam b (h u) • c + sig v b (h u) • γ))
      (b1.comp (measurable_prodMk_left (x := (c, u))))
  have bV : BM (fun p : (Fin n → ℝ) × U =>
      ∫ γ, ψ (lam b (h p.2) • p.1 + sig v b (h p.2) • γ) ^ 2 ∂stdGauss (Fin n) -
        (∫ γ, ψ (lam b (h p.2) • p.1 + sig v b (h p.2) • γ) ∂stdGauss (Fin n)) ^ 2) :=
    (b1.sq.integral_right (stdGauss (Fin n))).sub (b1.integral_right (stdGauss (Fin n))).sq
  have bR : BM (fun c : Fin n → ℝ => L * ∫ u,
      Var[fun γ => ψ (lam b (h u) • c + sig v b (h u) • γ); stdGauss (Fin n)] ∂μ) := by
    simp_rw [hvar]
    exact (BM.const L).mul (bV.integral_right μ)
  refine integral_mono ((bΘ.comp hm2).integral_right _ |>.integrable _) (bR.integrable _)
    fun c => ?_
  simp only []
  -- fixed `c`
  set g : U × (Fin n → ℝ) → ℝ := fun p => ψ (lam b (h p.1) • c + p.2) with hg
  have bg : BM g := hψ.comp
    ((((measurable_lam b).comp (hh.comp measurable_fst)).smul_const c).add measurable_snd)
  have hfam := s1_var_family (n := n) μ v b hh bg hL0 hL
  have bΦ : BM (fun M' : Matrix (Fin n) (Fin m) ℝ => ∫ u, g (u, M'.mulVec (res b (h u))) ∂μ) := by
    have : BM (fun q : Matrix (Fin n) (Fin m) ℝ × U => g (q.2, q.1.mulVec (res b (h q.2)))) :=
      bg.comp (measurable_snd.prodMk (measurable_mulVec_joint.comp
        (measurable_fst.prodMk ((measurable_res b).comp (hh.comp measurable_snd)))))
    exact this.integral_right μ
  have eT : ∀ M' : Matrix (Fin n) (Fin m) ℝ,
      outTrue μ h ψ (glue b c (M' * projPerp b)) = ∫ u, g (u, M'.mulVec (res b (h u))) ∂μ := by
    intro M'
    unfold outTrue
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hg]
    rw [glue_res]
  have emean : ∫ M' : Matrix (Fin n) (Fin m) ℝ, (∫ u, g (u, M'.mulVec (res b (h u))) ∂μ)
      ∂gaussMat n m v = outStand μ h v b ψ c := by
    have bq : BM (fun q : Matrix (Fin n) (Fin m) ℝ × U => g (q.2, q.1.mulVec (res b (h q.2)))) :=
      bg.comp (measurable_snd.prodMk (measurable_mulVec_joint.comp
        (measurable_fst.prodMk ((measurable_res b).comp (hh.comp measurable_snd)))))
    rw [integral_integral_swap
      (f := fun (M' : Matrix (Fin n) (Fin m) ℝ) (u : U) => g (u, M'.mulVec (res b (h u))))
      (bq.integrable _)]
    unfold outStand
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only []
    have hgu : Measurable (fun w : Fin n → ℝ => g (u, w)) := bg.meas.comp measurable_prodMk_left
    rw [layer_transfer v (res b (h u)) hgu]
    rfl
  have hv := hfam
  rw [var_bm' (gaussMat n m v) bΦ, emean] at hv
  simp_rw [eT]
  exact hv

end bounded

/-! ## Truncation -/

/-- `ψ` cut to `[−K, K]`. -/
noncomputable def clampF (K : ℝ) (ψ : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun y => max (-K) (min K (ψ y))

lemma bm_clampF {K : ℝ} (hK : 0 ≤ K) {ψ : (Fin n → ℝ) → ℝ} (hψ : Measurable ψ) :
    BM (clampF K ψ) := by
  refine ⟨measurable_const.max (measurable_const.min hψ), K, fun y => ?_⟩
  unfold clampF
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma clampF_abs_le {K : ℝ} (hK : 0 ≤ K) (ψ : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) :
    |clampF K ψ y| ≤ |ψ y| := by
  unfold clampF
  rw [abs_le]
  have h1 := neg_abs_le (ψ y)
  have h2 := le_abs_self (ψ y)
  have h3 := abs_nonneg (ψ y)
  constructor
  · rcases le_total K (ψ y) with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; linarith
    · rw [min_eq_right h]; exact le_trans h1 (le_max_right _ _)
  · refine max_le (by linarith) ?_
    exact (min_le_right _ _).trans h2

lemma clampF_eq {K : ℝ} {ψ : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ} (h : |ψ y| ≤ K) :
    clampF K ψ y = ψ y := by
  unfold clampF
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

lemma clampF_lip (K : ℝ) (ψ : (Fin n → ℝ) → ℝ) (y y' : Fin n → ℝ) :
    (clampF K ψ y - clampF K ψ y') ^ 2 ≤ (ψ y - ψ y') ^ 2 := by
  have h : |clampF K ψ y - clampF K ψ y'| ≤ |ψ y - ψ y'| := by
    unfold clampF
    have h1 := abs_max_sub_max_le_max (-K) (min K (ψ y)) (-K) (min K (ψ y'))
    have h2 := abs_min_sub_min_le_max K (ψ y) K (ψ y')
    simp only [sub_self, abs_zero] at h1 h2
    exact (h1.trans (le_of_eq (max_eq_right (abs_nonneg _)))).trans
      (h2.trans (le_of_eq (max_eq_right (abs_nonneg _))))
  rw [← sq_abs (clampF K ψ y - clampF K ψ y'), ← sq_abs (ψ y - ψ y')]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- Dominated convergence for the truncations. -/
lemma tendsto_clamp_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ψ : (Fin n → ℝ) → ℝ} (hψ : Measurable ψ) {q : Ω → Fin n → ℝ} (hq : Measurable q)
    {G : Ω → ℝ} (hG : Integrable G P) (hle : ∀ ω, |ψ (q ω)| ≤ G ω) :
    Tendsto (fun K : ℕ => ∫ ω, clampF (K : ℝ) ψ (q ω) ∂P) atTop (𝓝 (∫ ω, ψ (q ω) ∂P)) := by
  refine tendsto_integral_of_dominated_convergence G (fun K => ?_) hG (fun K => ?_) ?_
  · exact ((bm_clampF (Nat.cast_nonneg K) hψ).meas.comp hq).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact (clampF_abs_le (Nat.cast_nonneg K) ψ (q ω)).trans (hle ω)
  · refine Filter.Eventually.of_forall fun ω => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈|ψ (q ω)|⌉₊] with K hK
    refine (clampF_eq ?_).symm
    exact (Nat.le_ceil _).trans (by exact_mod_cast hK)

/-! ## The unbounded test function -/

lemma normSq_mulVec_le (M : Matrix (Fin n) (Fin m) ℝ) (t : Fin m → ℝ) :
    normSq (M.mulVec t) ≤ (∑ i, ∑ j, M i j ^ 2) * normSq t := by
  unfold normSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j) t

lemma normSq_add_le {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    normSq (x + y) ≤ 2 * normSq x + 2 * normSq y := by
  unfold normSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (x i - y i)]

lemma normSq_res_le {b : Fin m → ℝ} (hb : b ≠ 0) (h : Fin m → ℝ) : normSq (res b h) ≤ normSq h := by
  rw [BstLean.Part136.normSq_res (normSq_ne_zero hb)]
  have : 0 ≤ (∑ j, h j * b j) ^ 2 / normSq b := div_nonneg (sq_nonneg _) (normSq_nonneg _)
  linarith

lemma lam_sq_le {b : Fin m → ℝ} (hb : b ≠ 0) (h : Fin m → ℝ) :
    lam b h ^ 2 ≤ normSq h / normSq b := by
  have hb0 : 0 < normSq b := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm (normSq_ne_zero hb))
  unfold lam
  rw [div_pow, div_le_div_iff₀ (by positivity) hb0]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ h b
  have : (∑ j, h j * b j) ^ 2 ≤ normSq h * normSq b := cs
  nlinarith

section step

variable (μ : Measure U) [IsProbabilityMeasure μ]

/-- The bound of `standIn_mse_bdd` for a bounded `φ` that is a contraction of `ψ`, with the
second moment of `ψ` on the right, in `ℝ≥0∞`. -/
lemma standIn_lint_bdd (v : ℝ) {b : Fin m → ℝ} (hb : b ≠ 0) {h : U → Fin m → ℝ}
    (hh : Measurable h) {φ ψ : (Fin n → ℝ) → ℝ} (hφ : BM φ)
    (hlip : ∀ y y', (φ y - φ y') ^ 2 ≤ (ψ y - ψ y') ^ 2) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : Fin m → ℝ, ∫ u, (∑ j, eDir b (h u) j * w j) ^ 2 ∂μ ≤ L * ∑ j, w j ^ 2) :
    ∫⁻ M, ENNReal.ofReal ((outTrue μ h φ M - outStand μ h v b φ (M.mulVec b)) ^ 2)
        ∂gaussMat n m v ≤
      ENNReal.ofReal L * ∫⁻ c, (∫⁻ u, (∫⁻ γ, ENNReal.ofReal
        ((ψ (lam b (h u) • c + sig v b (h u) • γ) - ψ (lam b (h u) • c)) ^ 2)
          ∂stdGauss (Fin n)) ∂μ) ∂cDist n v b := by
  have bΘ : BM (fun M : Matrix (Fin n) (Fin m) ℝ =>
      (outTrue μ h φ M - outStand μ h v b φ (M.mulVec b)) ^ 2) :=
    ((bm_outTrue μ hh hφ).sub
      ((bm_outStand (n := n) μ hh v b hφ).comp (measurable_mulVec_right b))).sq
  have hA := standIn_mse_bdd (n := n) μ v hb hh hφ hL0 hL
  have b1 : BM (fun q : ((Fin n → ℝ) × U) × (Fin n → ℝ) =>
      φ (lam b (h q.1.2) • q.1.1 + sig v b (h q.1.2) • q.2)) :=
    hφ.comp (measurable_standOut3 hh v b)
  have b0 : BM (fun q : ((Fin n → ℝ) × U) × (Fin n → ℝ) =>
      φ (lam b (h q.1.2) • q.1.1)) :=
    hφ.comp (((measurable_lam b).comp (hh.comp (measurable_snd.comp measurable_fst))).smul
      (measurable_fst.comp measurable_fst))
  have bD : BM (fun q : ((Fin n → ℝ) × U) × (Fin n → ℝ) =>
      (φ (lam b (h q.1.2) • q.1.1 + sig v b (h q.1.2) • q.2) -
        φ (lam b (h q.1.2) • q.1.1)) ^ 2) := (b1.sub b0).sq
  have bD1 := bD.integral_right (stdGauss (Fin n))
  have bD2 := BM.integral_right (H := fun p : (Fin n → ℝ) × U =>
    ∫ γ, (φ (lam b (h p.2) • p.1 + sig v b (h p.2) • γ) -
        φ (lam b (h p.2) • p.1)) ^ 2 ∂stdGauss (Fin n)) bD1 μ
  -- the variance is at most the second moment about `ψ_K(λ c)`
  have hvle : ∀ (c : Fin n → ℝ) (u : U),
      Var[fun γ => φ (lam b (h u) • c + sig v b (h u) • γ); stdGauss (Fin n)] ≤
        ∫ γ, (φ (lam b (h u) • c + sig v b (h u) • γ) -
          φ (lam b (h u) • c)) ^ 2 ∂stdGauss (Fin n) := by
    intro c u
    exact var_le_sq_sub (stdGauss (Fin n))
      (X := fun γ => φ (lam b (h u) • c + sig v b (h u) • γ))
      (b1.comp (measurable_prodMk_left (x := (c, u)))) _
  have hreal : ∫ M, (outTrue μ h (φ) M -
      outStand μ h v b (φ) (M.mulVec b)) ^ 2 ∂gaussMat n m v ≤
      L * ∫ c, (∫ u, (∫ γ, (φ (lam b (h u) • c + sig v b (h u) • γ) -
          φ (lam b (h u) • c)) ^ 2 ∂stdGauss (Fin n)) ∂μ) ∂cDist n v b := by
    refine hA.trans (mul_le_mul_of_nonneg_left ?_ hL0)
    have hvar : ∀ (c : Fin n → ℝ) (u : U),
        Var[fun γ => φ (lam b (h u) • c + sig v b (h u) • γ);
          stdGauss (Fin n)] =
        ∫ γ, φ (lam b (h u) • c + sig v b (h u) • γ) ^ 2 ∂stdGauss (Fin n) -
          (∫ γ, φ (lam b (h u) • c + sig v b (h u) • γ)
            ∂stdGauss (Fin n)) ^ 2 := by
      intro c u
      exact var_bm (stdGauss (Fin n))
        (X := fun γ => φ (lam b (h u) • c + sig v b (h u) • γ))
        (b1.comp (measurable_prodMk_left (x := (c, u))))
    have bV : BM (fun p : (Fin n → ℝ) × U =>
        ∫ γ, φ (lam b (h p.2) • p.1 + sig v b (h p.2) • γ) ^ 2
            ∂stdGauss (Fin n) -
          (∫ γ, φ (lam b (h p.2) • p.1 + sig v b (h p.2) • γ)
            ∂stdGauss (Fin n)) ^ 2) :=
      (b1.sq.integral_right (stdGauss (Fin n))).sub (b1.integral_right (stdGauss (Fin n))).sq
    have bVc : BM (fun c : Fin n → ℝ => ∫ u,
        Var[fun γ => φ (lam b (h u) • c + sig v b (h u) • γ);
          stdGauss (Fin n)] ∂μ) := by
      simp_rw [hvar]
      exact bV.integral_right μ
    have iVc : Integrable (fun c : Fin n → ℝ => ∫ u,
        Var[fun γ => φ (lam b (h u) • c + sig v b (h u) • γ);
          stdGauss (Fin n)] ∂μ) (cDist n v b) := bVc.integrable _
    have iDc : Integrable (fun c : Fin n → ℝ => ∫ u, (∫ γ,
        (φ (lam b (h u) • c + sig v b (h u) • γ) - φ (lam b (h u) • c)) ^ 2
          ∂stdGauss (Fin n)) ∂μ) (cDist n v b) := bD2.integrable _
    refine integral_mono iVc iDc fun c => ?_
    have bVu : BM (fun u : U =>
        Var[fun γ => φ (lam b (h u) • c + sig v b (h u) • γ);
          stdGauss (Fin n)]) := by
      simp_rw [hvar]
      have h0 := bV.comp (measurable_prodMk_left (x := c))
      simp only [] at h0
      exact h0
    have iVu : Integrable (fun u : U =>
        Var[fun γ => φ (lam b (h u) • c + sig v b (h u) • γ);
          stdGauss (Fin n)]) μ := bVu.integrable _
    have iDu : Integrable (fun u : U => ∫ γ,
        (φ (lam b (h u) • c + sig v b (h u) • γ) - φ (lam b (h u) • c)) ^ 2
          ∂stdGauss (Fin n)) μ :=
      (bD1.comp (measurable_prodMk_left (x := c))).integrable _
    exact integral_mono iVu iDu fun u => hvle c u
  -- to `ℝ≥0∞`
  have e1 : ∫⁻ M, ENNReal.ofReal ((outTrue μ h φ M - outStand μ h v b φ (M.mulVec b)) ^ 2)
      ∂gaussMat n m v = ENNReal.ofReal (∫ M,
      (outTrue μ h (φ) M -
        outStand μ h v b (φ) (M.mulVec b)) ^ 2 ∂gaussMat n m v) :=
    (ofReal_integral_eq_lintegral_ofReal (bΘ.integrable _)
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
  rw [e1]
  refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
  rw [ENNReal.ofReal_mul hL0]
  refine mul_le_mul' le_rfl ?_
  rw [ofReal_integral_eq_lintegral_ofReal (bD2.integrable _)
    (Filter.Eventually.of_forall fun c => integral_nonneg fun u =>
      integral_nonneg fun γ => sq_nonneg _)]
  refine lintegral_mono fun c => ?_
  rw [ofReal_integral_eq_lintegral_ofReal
    ((bD1.comp (measurable_prodMk_left (x := c))).integrable _)
    (Filter.Eventually.of_forall fun u => integral_nonneg fun γ => sq_nonneg _)]
  refine lintegral_mono fun u => ?_
  rw [ofReal_integral_eq_lintegral_ofReal
    ((bD.comp (measurable_prodMk_left (x := (c, u)))).integrable _)
    (Filter.Eventually.of_forall fun γ => sq_nonneg _)]
  exact lintegral_mono fun γ => ENNReal.ofReal_le_ofReal (hlip _ _)

end step

section unbounded

variable (μ : Measure U) [IsProbabilityMeasure μ]

/-- **The stand-in theorem for an unnormalized output and an unbounded test function.** `ψ`
measurable with `ψ(y)² ≤ C(1 + |y|²)`; the hidden map is bounded (`|h(u)|² ≤ H`). Then, in
`ℝ≥0∞`: `E_M (E_u ψ(M h(u)) − E_u E_γ ψ(λ(u)·M b + σ(u)·γ))² ≤
L · E_c E_u E_γ (ψ(λ(u)c + σ(u)γ) − ψ(λ(u)c))²`. -/
theorem standIn_lint {v : ℝ} (hv : 0 ≤ v) {b : Fin m → ℝ} (hb : b ≠ 0) {h : U → Fin m → ℝ}
    (hh : Measurable h) {H : ℝ} (hH : ∀ u, normSq (h u) ≤ H)
    {ψ : (Fin n → ℝ) → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ y, ψ y ^ 2 ≤ C * (1 + normSq y))
    {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : Fin m → ℝ, ∫ u, (∑ j, eDir b (h u) j * w j) ^ 2 ∂μ ≤ L * ∑ j, w j ^ 2) :
    ∫⁻ M, ENNReal.ofReal ((outTrue μ h ψ M - outStand μ h v b ψ (M.mulVec b)) ^ 2)
        ∂gaussMat n m v ≤
      ENNReal.ofReal L * ∫⁻ c, (∫⁻ u, (∫⁻ γ, ENNReal.ofReal
        ((ψ (lam b (h u) • c + sig v b (h u) • γ) - ψ (lam b (h u) • c)) ^ 2)
          ∂stdGauss (Fin n)) ∂μ) ∂cDist n v b := by
  have hb0 : 0 < normSq b := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm (normSq_ne_zero hb))
  obtain ⟨u0⟩ := μ.nonempty_of_neZero
  have hH0 : 0 ≤ H := (normSq_nonneg _).trans (hH u0)
  have hC0 : 0 ≤ C := by
    have := hC 0
    have h1 : (0 : ℝ) ≤ ψ 0 ^ 2 := sq_nonneg _
    have h2 : normSq (0 : Fin n → ℝ) = 0 := by simp [normSq]
    rw [h2] at this
    nlinarith
  set R : ℝ≥0∞ := ∫⁻ c, (∫⁻ u, (∫⁻ γ, ENNReal.ofReal
        ((ψ (lam b (h u) • c + sig v b (h u) • γ) - ψ (lam b (h u) • c)) ^ 2)
          ∂stdGauss (Fin n)) ∂μ) ∂cDist n v b with hR
  set f : ℕ → Matrix (Fin n) (Fin m) ℝ → ℝ≥0∞ := fun K M =>
    ENNReal.ofReal ((outTrue μ h (clampF (K : ℝ) ψ) M -
      outStand μ h v b (clampF (K : ℝ) ψ) (M.mulVec b)) ^ 2) with hf
  have bK : ∀ K : ℕ, BM (clampF (K : ℝ) ψ) := fun K => bm_clampF (Nat.cast_nonneg K) hψ
  have bΘ : ∀ K : ℕ, BM (fun M : Matrix (Fin n) (Fin m) ℝ =>
      (outTrue μ h (clampF (K : ℝ) ψ) M -
        outStand μ h v b (clampF (K : ℝ) ψ) (M.mulVec b)) ^ 2) := fun K =>
    ((bm_outTrue μ hh (bK K)).sub
      ((bm_outStand (n := n) μ hh v b (bK K)).comp (measurable_mulVec_right b))).sq
  have mf : ∀ K, Measurable (f K) := fun K => ENNReal.measurable_ofReal.comp (bΘ K).meas
  -- Step 1: the bound for every truncation
  have step1 : ∀ K : ℕ, ∫⁻ M, f K M ∂gaussMat n m v ≤ ENNReal.ofReal L * R := fun K =>
    standIn_lint_bdd μ v hb hh (bK K) (clampF_lip _ _) hL0 hL
  -- Step 2: pointwise convergence
  have habs : ∀ y : Fin n → ℝ, |ψ y| ≤ 1 + C * (1 + normSq y) := by
    intro y
    have h1 := hC y
    have h2 : |ψ y| ≤ 1 + ψ y ^ 2 := by
      have := sq_abs (ψ y)
      nlinarith [sq_nonneg (|ψ y| - 1), abs_nonneg (ψ y)]
    linarith
  have step2 : ∀ M : Matrix (Fin n) (Fin m) ℝ, Tendsto (fun K => f K M) atTop
      (𝓝 (ENNReal.ofReal ((outTrue μ h ψ M - outStand μ h v b ψ (M.mulVec b)) ^ 2))) := by
    intro M
    have t1 : Tendsto (fun K : ℕ => outTrue μ h (clampF (K : ℝ) ψ) M) atTop
        (𝓝 (outTrue μ h ψ M)) := by
      unfold outTrue
      refine tendsto_clamp_integral μ hψ ((measurable_mulVec_left M).comp hh)
        (G := fun _ => 1 + C * (1 + (∑ i, ∑ j, M i j ^ 2) * H)) (integrable_const _) fun u => ?_
      refine (habs _).trans ?_
      have h1 := normSq_mulVec_le M (h u)
      have h2 : (∑ i, ∑ j, M i j ^ 2) * normSq (h u) ≤ (∑ i, ∑ j, M i j ^ 2) * H :=
        mul_le_mul_of_nonneg_left (hH u)
          (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
      have h3 : C * (1 + normSq (M.mulVec (h u))) ≤ C * (1 + (∑ i, ∑ j, M i j ^ 2) * H) :=
        mul_le_mul_of_nonneg_left (by linarith) hC0
      linarith
    have t2 : Tendsto (fun K : ℕ => outStand μ h v b (clampF (K : ℝ) ψ) (M.mulVec b)) atTop
        (𝓝 (outStand μ h v b ψ (M.mulVec b))) := by
      set c := M.mulVec b with hc
      set q : U × (Fin n → ℝ) → Fin n → ℝ :=
        fun p => lam b (h p.1) • c + sig v b (h p.1) • p.2 with hq
      have mq : Measurable q := measurable_standOut hh v b c
      set G : U × (Fin n → ℝ) → ℝ := fun p =>
        1 + C * (1 + (2 * (H / normSq b * normSq c) + 2 * (v * H * normSq p.2))) with hG
      have iG : Integrable G (μ.prod (stdGauss (Fin n))) := by
        have i1 : Integrable (fun p : U × (Fin n → ℝ) => normSq p.2) (μ.prod (stdGauss (Fin n))) :=
          (BstLean.Part137.gauss_normSq n).1.comp_snd μ
        have e : G = fun p : U × (Fin n → ℝ) =>
            (1 + C * (1 + 2 * (H / normSq b * normSq c))) + (C * (2 * (v * H))) * normSq p.2 := by
          funext p; simp only [hG]; ring
        rw [e]
        exact (integrable_const _).add (i1.const_mul _)
      have hle : ∀ p, |ψ (q p)| ≤ G p := by
        intro p
        refine (habs _).trans ?_
        have h1 : normSq (q p) ≤ 2 * normSq (lam b (h p.1) • c) +
            2 * normSq (sig v b (h p.1) • p.2) := normSq_add_le _ _
        rw [normSq_smul, normSq_smul] at h1
        have h2 : lam b (h p.1) ^ 2 ≤ H / normSq b :=
          (lam_sq_le hb _).trans (div_le_div_of_nonneg_right (hH p.1) hb0.le)
        have h3 : sig v b (h p.1) ^ 2 ≤ v * H := by
          unfold sig
          rw [mul_pow, Real.sq_sqrt hv, Real.sq_sqrt (normSq_nonneg _)]
          exact mul_le_mul_of_nonneg_left ((normSq_res_le hb _).trans (hH p.1)) hv
        have h4 : lam b (h p.1) ^ 2 * normSq c ≤ H / normSq b * normSq c :=
          mul_le_mul_of_nonneg_right h2 (normSq_nonneg _)
        have h5 : sig v b (h p.1) ^ 2 * normSq p.2 ≤ v * H * normSq p.2 :=
          mul_le_mul_of_nonneg_right h3 (normSq_nonneg _)
        have h6 : C * (1 + normSq (q p)) ≤
            C * (1 + (2 * (H / normSq b * normSq c) + 2 * (v * H * normSq p.2))) :=
          mul_le_mul_of_nonneg_left (by linarith) hC0
        simp only [hG]
        linarith
      have iψ : Integrable (fun p => ψ (q p)) (μ.prod (stdGauss (Fin n))) :=
        Integrable.mono' iG (hψ.comp mq).aestronglyMeasurable
          (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hle p)
      have eK : ∀ K : ℕ, outStand μ h v b (clampF (K : ℝ) ψ) c =
          ∫ p, clampF (K : ℝ) ψ (q p) ∂(μ.prod (stdGauss (Fin n))) := by
        intro K
        unfold outStand
        exact (integral_prod (fun p : U × (Fin n → ℝ) => clampF (K : ℝ) ψ (q p))
          (((bK K).comp mq).integrable _)).symm
      have e0 : outStand μ h v b ψ c = ∫ p, ψ (q p) ∂(μ.prod (stdGauss (Fin n))) := by
        unfold outStand
        exact (integral_prod (fun p : U × (Fin n → ℝ) => ψ (q p)) iψ).symm
      simp_rw [eK]
      rw [e0]
      exact tendsto_clamp_integral _ hψ mq iG hle
    have t3 := ((t1.sub t2).pow 2)
    exact (ENNReal.continuous_ofReal.tendsto _).comp t3
  -- Step 3: Fatou
  calc ∫⁻ M, ENNReal.ofReal ((outTrue μ h ψ M - outStand μ h v b ψ (M.mulVec b)) ^ 2)
        ∂gaussMat n m v
      = ∫⁻ M, liminf (fun K => f K M) atTop ∂gaussMat n m v :=
        lintegral_congr fun M => ((step2 M).liminf_eq).symm
    _ ≤ liminf (fun K => ∫⁻ M, f K M ∂gaussMat n m v) atTop := lintegral_liminf_le mf
    _ ≤ ENNReal.ofReal L * R :=
        liminf_le_of_frequently_le' (Filter.Frequently.of_forall step1)

end unbounded

end BstLean.Part149

open BstLean.Part149 in
#print axioms standIn_mse_bdd
open BstLean.Part149 in
#print axioms standIn_lint
