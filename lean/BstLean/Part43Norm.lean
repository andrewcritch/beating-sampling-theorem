import BstLean.Part43Defs

/-!
# Part 43, wave 1: Lemma norm for every law on the sphere

Paper: `proofs/option-m/43-arbitrary-degree-every-diagonal-bingham.tex`. Specification:
`delegations/answers/p43-spec-opus.md`. Replace each `sorry` by a proof. Do not edit the statements.
Do not use `native_decide` or `axiom` anywhere.

Suggested route.
* Copy `Part41Norm.norm_det` with `uniformSphere n` replaced by `μ`: `f(Mφ) − f₀ = 𝒫 + Σ_j (ρ^j − 1)
  D^{−j/2} u_j`, and `sd_μ` is a seminorm on bounded measurable functions (`φ` is bounded on the
  sphere, `μ` is a probability).
-/

namespace BstLean.Part43

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD rhoD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT mset wordOf Tens TSymm fval varU sdU
  levels cQ kapQ muQ aT Nn uJ Pcal r2 rhoZ cS Bfix Pn epsS baseline thetaT rhoBar Kc GamP etaR etaK Lk
  orbSize heavyCount bQ In41)
open BstLean.Part40 (SphLaw SignSym)

variable {n d : ℕ}

section seminorm
variable {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]

private lemma continuous_lp (hμ : SphLaw n μ) (h : (Fin n → ℝ) → ℝ) (hc : Continuous h) :
    MemLp h 2 μ := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : Fin n → ℝ) 1).image hc).isBounded.exists_norm_le
  apply MemLp.of_bound hc.aestronglyMeasurable C
  filter_upwards [hμ.sphere] with x hx
  apply hC
  apply Set.mem_image_of_mem
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  rw [Real.norm_eq_abs]
  have hi : x i ^ 2 ≤ 1 := by
    rw [← hx]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

omit [IsProbabilityMeasure μ] in
private lemma continuous_map (M : CoefIdxD n d → ℝ) (i : Fin n) :
    Continuous (fun x => BstLean.Part36.mapMD M x i) := by
  unfold BstLean.Part36.mapMD
  apply continuous_finsetSum
  intro j _
  apply continuous_finsetSum
  intro b _
  apply Continuous.const_mul
  exact continuous_multiset_prod b.1 (fun i _ => continuous_apply i)

omit [IsProbabilityMeasure μ] in
private lemma continuous_u (T : Tens n) (j : ℕ) (M : CoefIdxD n d → ℝ) :
    Continuous (uJ T j M) := by
  unfold uJ contr
  apply continuous_finsetSum
  intro w _
  apply Continuous.const_mul
  exact continuous_finsetProd _ (fun i _ => continuous_map M (w i))

omit [IsProbabilityMeasure μ] in
private lemma l2_norm (h : (Fin n → ℝ) → ℝ) (hh : MemLp h 2 μ) :
    ‖hh.toLp h‖ = Real.sqrt (∫ x, h x ^ 2 ∂μ) := by
  have he : ‖hh.toLp h‖ ^ 2 = ∫ x, h x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hh.coeFn_toLp] with x hx
    simp [hx, Real.norm_eq_abs, sq_abs]
  rw [← he, Real.sqrt_sq (norm_nonneg _)]

private noncomputable def centerLp (h : (Fin n → ℝ) → ℝ)
    (hh : MemLp h 2 μ) : Lp ℝ 2 μ :=
  (hh.sub (memLp_const (∫ x, h x ∂μ))).toLp _

private lemma sd_norm (h : (Fin n → ℝ) → ℝ) (hh : MemLp h 2 μ) :
    sdU μ h = ‖centerLp h hh‖ := by
  symm
  exact l2_norm _ _

private lemma center_add (h g : (Fin n → ℝ) → ℝ)
    (hh : MemLp h 2 μ) (hg : MemLp g 2 μ) :
    centerLp (h + g) (hh.add hg) = centerLp h hh + centerLp g hg := by
  apply Lp.ext
  filter_upwards [(hh.add hg).sub (memLp_const (∫ x, (h + g) x ∂μ)) |>.coeFn_toLp,
    (hh.sub (memLp_const (∫ x, h x ∂μ))).coeFn_toLp,
    (hg.sub (memLp_const (∫ x, g x ∂μ))).coeFn_toLp,
    Lp.coeFn_add (centerLp h hh) (centerLp g hg)] with x h1 h2 h3 h4
  change _ = _ at h1 h2 h3
  rw [h4]
  simp only [Pi.add_apply]
  unfold centerLp
  rw [h2, h3, h1]
  simp only [Pi.add_apply, Pi.sub_apply, integral_add (hh.integrable (by norm_num)) (hg.integrable (by norm_num))]
  ring

private lemma sd_add_le (h g : (Fin n → ℝ) → ℝ)
    (hh : MemLp h 2 μ) (hg : MemLp g 2 μ) :
    sdU μ (h + g) ≤ sdU μ h + sdU μ g := by
  rw [sd_norm _ (hh.add hg), sd_norm _ hh, sd_norm _ hg, center_add]
  exact norm_add_le _ _

private lemma sd_mul (c : ℝ) (h : (Fin n → ℝ) → ℝ)
    (hh : MemLp h 2 μ) :
    sdU μ (fun x => c * h x) = |c| * sdU μ h := by
  have he : centerLp (fun x => c * h x) (hh.const_mul c) = c • centerLp h hh := by
    apply Lp.ext
    filter_upwards [((hh.const_mul c).sub (memLp_const (∫ x, c * h x ∂μ))).coeFn_toLp,
      (hh.sub (memLp_const (∫ x, h x ∂μ))).coeFn_toLp,
      Lp.coeFn_smul c (centerLp h hh)] with x h1 h2 h3
    rw [h3]
    simp only [Pi.smul_apply, smul_eq_mul]
    unfold centerLp
    rw [h2, h1]
    simp [integral_const_mul, mul_sub, Pi.sub_apply]
  rw [sd_norm _ (hh.const_mul c), he, norm_smul, Real.norm_eq_abs, sd_norm _ hh]

private lemma sd_sum_le {ι : Type*} (s : Finset ι) (h : ι → (Fin n → ℝ) → ℝ)
    (hh : ∀ i ∈ s, MemLp (h i) 2 μ) :
    sdU μ (fun x => ∑ i ∈ s, h i x) ≤ ∑ i ∈ s, sdU μ (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sdU, varU]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (sd_add_le _ _ (hh i (Finset.mem_insert_self _ _))
      (memLp_finsetSum _ (fun j hj => hh j (Finset.mem_insert_of_mem hj)))).trans
      (add_le_add_right (ih (fun j hj => hh j (Finset.mem_insert_of_mem hj))) _)

private lemma sd_shift (c : ℝ) (h : (Fin n → ℝ) → ℝ)
    (hh : MemLp h 2 μ) :
    sdU μ (fun x => c + h x) = sdU μ h := by
  unfold sdU varU
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    rw [integral_add (integrable_const c) (hh.integrable (by norm_num))]
    simp

end seminorm


/-- **Lemma norm** under `μ`. -/
theorem norm_det43 (hn : 1 ≤ n) {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (k : ℕ) (f0 : ℝ) (T : Tens n)
    (Z : CoefIdxD n d → ℝ) (hZ : Z ≠ 0) :
    sdU μ (Pcal k T Z) -
        ∑ j ∈ Finset.Icc 1 k, |rhoZ Z ^ j - 1| * (sdU μ (uJ T j Z) / Real.sqrt (DD n d) ^ j) ≤
      Real.sqrt (varFQ μ k f0 T (unitOfD Z)) := by
  classical
  let := hμ.prob
  have hD : 0 < DD n d := by
    unfold DD
    have : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, ⟨0, by omega⟩)⟩⟩
    exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (DD n d) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hD)
  have hu (j : ℕ) (x : Fin n → ℝ) :
      uJ T j (unitOfD Z) x = rhoZ Z ^ j / Real.sqrt (DD n d) ^ j * uJ T j Z x := by
    have hm (i : Fin n) : BstLean.Part36.mapMD (unitOfD Z) x i =
        (1 / Real.sqrt (r2 Z)) * BstLean.Part36.mapMD Z x i := by
      unfold BstLean.Part36.mapMD BstLean.Part36.coefD unitOfD
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> simp [r2] <;> ring
    unfold uJ contr
    simp_rw [hm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    have he : rhoZ Z ^ j / Real.sqrt (DD n d) ^ j = (1 / Real.sqrt (r2 Z)) ^ j := by
      rw [rhoZ, ← div_pow]
      congr 1
      rw [div_div, mul_comm]
      simpa only [mul_one] using mul_div_mul_left 1 (Real.sqrt (r2 Z)) hs
    rw [he]
    ring
  let H : (Fin n → ℝ) → ℝ := fun x => ∑ j ∈ Finset.Icc 1 k, uJ T j (unitOfD Z) x
  let E : (Fin n → ℝ) → ℝ := fun x => ∑ j ∈ Finset.Icc 1 k,
    ((1 - rhoZ Z ^ j) / Real.sqrt (DD n d) ^ j) * uJ T j Z x
  have hH : MemLp H 2 μ :=
    memLp_finsetSum _ (fun j _ => continuous_lp hμ _ (continuous_u T j _))
  have hE : MemLp E 2 μ :=
    memLp_finsetSum _ (fun j _ => (continuous_lp hμ _ (continuous_u T j Z)).const_mul _)
  have heq : Pcal k T Z = H + E := by
    funext x
    dsimp [Pcal, H, E]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hu]
    ring
  have hbound : sdU μ E ≤
      ∑ j ∈ Finset.Icc 1 k, |rhoZ Z ^ j - 1| *
        (sdU μ (uJ T j Z) / Real.sqrt (DD n d) ^ j) := by
    apply (sd_sum_le _ _ (fun j _ => (continuous_lp hμ _ (continuous_u T j Z)).const_mul _)).trans
    apply Finset.sum_le_sum
    intro j _
    rw [sd_mul _ _ (continuous_lp hμ _ (continuous_u T j Z)), abs_div,
      abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _), abs_sub_comm]
    exact le_of_eq (by ring)
  have hsd : sdU μ H = Real.sqrt (varFQ μ k f0 T (unitOfD Z)) := by
    symm
    exact sd_shift f0 H hH
  have ht := sd_add_le H E hH hE
  rw [← heq, hsd] at ht
  linarith


end BstLean.Part43

