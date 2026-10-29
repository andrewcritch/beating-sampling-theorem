import BstLean.Part53Defs
import BstLean.Part41Norm

namespace BstLean.Part53.T2Aux

open MeasureTheory
open scoped ENNReal
open BstLean.Part36 (CoefIdxD DD mapMD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Tens uJ contr varU sdU fval)
variable {n d : ℕ}
variable {μ : Measure (Fin n → ℝ)}

lemma sphere_memLp (hμ : SphLaw n μ) {h : (Fin n → ℝ) → ℝ}
    (hc : Continuous h) : MemLp h 2 μ := by
  let := hμ.prob
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

lemma continuous_map (M : CoefIdxD n d → ℝ) (i : Fin n) :
    Continuous (fun x => BstLean.Part36.mapMD M x i) := by
  unfold BstLean.Part36.mapMD
  apply continuous_finsetSum
  intro j _
  apply continuous_finsetSum
  intro b _
  apply Continuous.const_mul
  exact continuous_multiset_prod b.1 (fun i _ => continuous_apply i)

lemma continuous_u (T : Tens n) (j : ℕ) (M : CoefIdxD n d → ℝ) :
    Continuous (uJ T j M) := by
  unfold uJ contr
  apply continuous_finsetSum
  intro w _
  apply Continuous.const_mul
  exact continuous_finsetProd _ (fun i _ => continuous_map M (w i))

section
variable [IsProbabilityMeasure μ]

lemma l2_norm (h : (Fin n → ℝ) → ℝ) (hh : MemLp h 2 μ) :
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

lemma sd_norm (h : (Fin n → ℝ) → ℝ) (hh : MemLp h 2 μ) :
    sdU μ h = ‖centerLp h hh‖ := by
  symm
  exact l2_norm _ _

lemma center_add (h g : (Fin n → ℝ) → ℝ)
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

lemma sd_add_le (h g : (Fin n → ℝ) → ℝ)
    (hh : MemLp h 2 μ) (hg : MemLp g 2 μ) :
    sdU μ (h + g) ≤ sdU μ h + sdU μ g := by
  rw [sd_norm _ (hh.add hg), sd_norm _ hh, sd_norm _ hg, center_add]
  exact norm_add_le _ _

lemma sd_mul (c : ℝ) (h : (Fin n → ℝ) → ℝ)
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

lemma sd_sum_le {ι : Type*} (s : Finset ι) (h : ι → (Fin n → ℝ) → ℝ)
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

lemma sd_shift (c : ℝ) (h : (Fin n → ℝ) → ℝ)
    (hh : MemLp h 2 μ) :
    sdU μ (fun x => c + h x) = sdU μ h := by
  unfold sdU varU
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    rw [integral_add (integrable_const c) (hh.integrable (by norm_num))]
    simp


end

private lemma map_smul (Z : CoefIdxD n d → ℝ) (l : ℝ) (x : Fin n → ℝ) :
    mapMD (l • Z) x = l • mapMD Z x := by
  funext a
  unfold mapMD BstLean.Part36.coefD
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro β _
  split_ifs <;> simp [mul_assoc]

lemma uJ_smul (T : Tens n) (j : ℕ) (l : ℝ) (W : CoefIdxD n d → ℝ)
    (x : Fin n → ℝ) : uJ T j (l • W) x = l ^ j * uJ T j W x := by
  unfold uJ contr
  simp_rw [map_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

noncomputable def radialDefect (μ : Measure (Fin n → ℝ)) (k : ℕ) (T : Tens n)
    (W : CoefIdxD n d → ℝ) (l : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, |l ^ j - 1| * sdU μ (uJ T j W)

lemma radial_sd_comparison (hμ : SphLaw n μ) (k : ℕ) (f0 : ℝ) (T : Tens n)
    (W : CoefIdxD n d → ℝ) (l : ℝ) :
    Real.sqrt (BstLean.Part43.varFQ μ k f0 T (l • W)) ≤
      Real.sqrt (BstLean.Part43.varFQ μ k f0 T W) + radialDefect μ k T W l := by
  classical
  let := hμ.prob
  let H := fun x => fval k f0 T (mapMD W x)
  let E := fun x => ∑ j ∈ Finset.Icc 1 k, (l ^ j - 1) * uJ T j W x
  have hU (j : ℕ) : MemLp (uJ T j W) 2 μ := sphere_memLp hμ (continuous_u T j W)
  have hH : MemLp H 2 μ :=
    (memLp_const f0).add (memLp_finsetSum _ (fun j _ => hU j))
  have hE : MemLp E 2 μ :=
    memLp_finsetSum _ (fun j _ => (hU j).const_mul _)
  have heq : (fun x => fval k f0 T (mapMD (l • W) x)) = H + E := by
    funext x
    change f0 + ∑ j ∈ Finset.Icc 1 k, uJ T j (l • W) x =
      (f0 + ∑ j ∈ Finset.Icc 1 k, uJ T j W x) +
        ∑ j ∈ Finset.Icc 1 k, (l ^ j - 1) * uJ T j W x
    simp_rw [uJ_smul]
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hb : sdU μ E ≤ radialDefect μ k T W l := by
    apply (sd_sum_le _ _ (fun j _ => (hU j).const_mul _)).trans
    apply Finset.sum_le_sum
    intro j _
    rw [sd_mul _ _ (hU j)]
  have ha := sd_add_le H E hH hE
  rw [← heq] at ha
  exact ha.trans (add_le_add le_rfl hb)

end BstLean.Part53.T2Aux
