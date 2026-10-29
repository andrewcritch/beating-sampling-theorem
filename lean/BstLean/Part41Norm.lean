import BstLean.Part41Defs
import BstLean.Part40Imported

/-!
# Part 41, wave 1: normalization and the radius (Lemmas `norm`, `radius`)

Paper: Lemmas `norm` and `radius` of `proofs/option-m/41-arbitrary-degree.tex`.
Specification: `delegations/answers/p41-spec-opus.md`. Do not use `native_decide`.

Routes. `norm_det`: `mapMD (unitOfD Z) x = r⁻¹ mapMD Z x`, so `f(Mφ) − f₀ = Σ_j D^{−j/2} ρ^j u_j`
`= 𝒫 + Σ_j D^{−j/2}(ρ^j − 1) u_j`; `sd` is a seminorm on `L²(uniformSphere)` (polynomials are bounded on
the sphere). `radius_event`: `r² ∼ χ²_D`; Part 40's `chisq_upper` and `chisq_lower` (as in Part 40's
`norm_event`). `radius_det`: `ρ² ∈ [1/(1+η_r), 1/(1−η_r)]`, then `a + 1/a ≥ 2`.
-/

namespace BstLean.Part41

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD)

variable {n d : ℕ}

section seminorm
variable [IsProbabilityMeasure (uniformSphere n)]

private lemma continuous_lp (h : (Fin n → ℝ) → ℝ) (hc : Continuous h) :
    MemLp h 2 (uniformSphere n) := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : Fin n → ℝ) 1).image hc).isBounded.exists_norm_le
  apply MemLp.of_bound hc.aestronglyMeasurable C
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
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

omit [IsProbabilityMeasure (uniformSphere n)] in
private lemma continuous_map (M : CoefIdxD n d → ℝ) (i : Fin n) :
    Continuous (fun x => BstLean.Part36.mapMD M x i) := by
  unfold BstLean.Part36.mapMD
  apply continuous_finsetSum
  intro j _
  apply continuous_finsetSum
  intro b _
  apply Continuous.const_mul
  exact continuous_multiset_prod b.1 (fun i _ => continuous_apply i)

omit [IsProbabilityMeasure (uniformSphere n)] in
private lemma continuous_u (T : Tens n) (j : ℕ) (M : CoefIdxD n d → ℝ) :
    Continuous (uJ T j M) := by
  unfold uJ contr
  apply continuous_finsetSum
  intro w _
  apply Continuous.const_mul
  exact continuous_finsetProd _ (fun i _ => continuous_map M (w i))

omit [IsProbabilityMeasure (uniformSphere n)] in
private lemma l2_norm (h : (Fin n → ℝ) → ℝ) (hh : MemLp h 2 (uniformSphere n)) :
    ‖hh.toLp h‖ = Real.sqrt (∫ x, h x ^ 2 ∂uniformSphere n) := by
  have he : ‖hh.toLp h‖ ^ 2 = ∫ x, h x ^ 2 ∂uniformSphere n := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hh.coeFn_toLp] with x hx
    simp [hx, Real.norm_eq_abs, sq_abs]
  rw [← he, Real.sqrt_sq (norm_nonneg _)]

private noncomputable def centerLp (h : (Fin n → ℝ) → ℝ)
    (hh : MemLp h 2 (uniformSphere n)) : Lp ℝ 2 (uniformSphere n) :=
  (hh.sub (memLp_const (∫ x, h x ∂uniformSphere n))).toLp _

private lemma sd_norm (h : (Fin n → ℝ) → ℝ) (hh : MemLp h 2 (uniformSphere n)) :
    sdU (uniformSphere n) h = ‖centerLp h hh‖ := by
  symm
  exact l2_norm _ _

private lemma center_add (h g : (Fin n → ℝ) → ℝ)
    (hh : MemLp h 2 (uniformSphere n)) (hg : MemLp g 2 (uniformSphere n)) :
    centerLp (h + g) (hh.add hg) = centerLp h hh + centerLp g hg := by
  apply Lp.ext
  filter_upwards [(hh.add hg).sub (memLp_const (∫ x, (h + g) x ∂uniformSphere n)) |>.coeFn_toLp,
    (hh.sub (memLp_const (∫ x, h x ∂uniformSphere n))).coeFn_toLp,
    (hg.sub (memLp_const (∫ x, g x ∂uniformSphere n))).coeFn_toLp,
    Lp.coeFn_add (centerLp h hh) (centerLp g hg)] with x h1 h2 h3 h4
  change _ = _ at h1 h2 h3
  rw [h4]
  simp only [Pi.add_apply]
  unfold centerLp
  rw [h2, h3, h1]
  simp only [Pi.add_apply, Pi.sub_apply, integral_add (hh.integrable (by norm_num)) (hg.integrable (by norm_num))]
  ring

private lemma sd_add_le (h g : (Fin n → ℝ) → ℝ)
    (hh : MemLp h 2 (uniformSphere n)) (hg : MemLp g 2 (uniformSphere n)) :
    sdU (uniformSphere n) (h + g) ≤ sdU (uniformSphere n) h + sdU (uniformSphere n) g := by
  rw [sd_norm _ (hh.add hg), sd_norm _ hh, sd_norm _ hg, center_add]
  exact norm_add_le _ _

private lemma sd_mul (c : ℝ) (h : (Fin n → ℝ) → ℝ)
    (hh : MemLp h 2 (uniformSphere n)) :
    sdU (uniformSphere n) (fun x => c * h x) = |c| * sdU (uniformSphere n) h := by
  have he : centerLp (fun x => c * h x) (hh.const_mul c) = c • centerLp h hh := by
    apply Lp.ext
    filter_upwards [((hh.const_mul c).sub (memLp_const (∫ x, c * h x ∂uniformSphere n))).coeFn_toLp,
      (hh.sub (memLp_const (∫ x, h x ∂uniformSphere n))).coeFn_toLp,
      Lp.coeFn_smul c (centerLp h hh)] with x h1 h2 h3
    rw [h3]
    simp only [Pi.smul_apply, smul_eq_mul]
    unfold centerLp
    rw [h2, h1]
    simp [integral_const_mul, mul_sub, Pi.sub_apply]
  rw [sd_norm _ (hh.const_mul c), he, norm_smul, Real.norm_eq_abs, sd_norm _ hh]

private lemma sd_sum_le {ι : Type*} (s : Finset ι) (h : ι → (Fin n → ℝ) → ℝ)
    (hh : ∀ i ∈ s, MemLp (h i) 2 (uniformSphere n)) :
    sdU (uniformSphere n) (fun x => ∑ i ∈ s, h i x) ≤ ∑ i ∈ s, sdU (uniformSphere n) (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sdU, varU]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (sd_add_le _ _ (hh i (Finset.mem_insert_self _ _))
      (memLp_finsetSum _ (fun j hj => hh j (Finset.mem_insert_of_mem hj)))).trans
      (add_le_add_right (ih (fun j hj => hh j (Finset.mem_insert_of_mem hj))) _)

private lemma sd_shift (c : ℝ) (h : (Fin n → ℝ) → ℝ)
    (hh : MemLp h 2 (uniformSphere n)) :
    sdU (uniformSphere n) (fun x => c + h x) = sdU (uniformSphere n) h := by
  unfold sdU varU
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    rw [integral_add (integrable_const c) (hh.integrable (by norm_num))]
    simp

end seminorm

/-- **Lemma `norm`**: `sd_x f(Mφ) ≥ sd_x 𝒫 − Σ_j |ρ^j − 1| D^{−j/2} sd_x u_j`. -/
theorem norm_det (hn : 1 ≤ n) (k : ℕ) (f0 : ℝ) (T : Tens n) (Z : CoefIdxD n d → ℝ) (hZ : Z ≠ 0) :
    sdU (uniformSphere n) (Pcal k T Z) -
        ∑ j ∈ Finset.Icc 1 k, |rhoZ Z ^ j - 1| * (sdU (uniformSphere n) (uJ T j Z) / Real.sqrt (DD n d) ^ j) ≤
      Real.sqrt (varF k f0 T (unitOfD Z)) := by
  classical
  let := BstLean.Part29.uniformSphere_isProbability n hn
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
  have hH : MemLp H 2 (uniformSphere n) :=
    memLp_finsetSum _ (fun j _ => continuous_lp _ (continuous_u T j _))
  have hE : MemLp E 2 (uniformSphere n) :=
    memLp_finsetSum _ (fun j _ => (continuous_lp _ (continuous_u T j Z)).const_mul _)
  have heq : Pcal k T Z = H + E := by
    funext x
    dsimp [Pcal, H, E]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hu]
    ring
  have hbound : sdU (uniformSphere n) E ≤
      ∑ j ∈ Finset.Icc 1 k, |rhoZ Z ^ j - 1| *
        (sdU (uniformSphere n) (uJ T j Z) / Real.sqrt (DD n d) ^ j) := by
    apply (sd_sum_le _ _ (fun j _ => (continuous_lp _ (continuous_u T j Z)).const_mul _)).trans
    apply Finset.sum_le_sum
    intro j _
    rw [sd_mul _ _ (continuous_lp _ (continuous_u T j Z)), abs_div,
      abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _), abs_sub_comm]
    exact le_of_eq (by ring)
  have hsd : sdU (uniformSphere n) H = Real.sqrt (varF k f0 T (unitOfD Z)) := by
    symm
    exact sd_shift f0 H hH
  have ht := sd_add_le H E hH hE
  rw [← heq, hsd] at ht
  linarith

/-- **Lemma `radius`**, the event: `Pr{|r²/D − 1| > η_r} ≤ 2e^{−x}`. -/
theorem radius_event (hn : 1 ≤ n) (x : ℝ) (hx : 0 < x) :
    stdGauss (CoefIdxD n d) {Z | etaR n d x < |r2 Z / DD n d - 1|} ≤ ENNReal.ofReal (2 * Real.exp (-x)) := by
  have hcard : 0 < Fintype.card (CoefIdxD n d) := by
    have hpos : 0 < DD n d := by
      unfold DD
      have : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, ⟨0, by omega⟩)⟩⟩
      exact_mod_cast Fintype.card_pos
    unfold DD at hpos
    exact_mod_cast hpos
  have hD : 0 < DD n d := by unfold DD; exact_mod_cast hcard
  have hDe : DD n d * etaR n d x = 2 * Real.sqrt (x * DD n d) + 2 * x := by
    unfold etaR; field_simp
  have hsq : Real.sqrt (x * DD n d) = Real.sqrt ((Fintype.card (CoefIdxD n d) : ℝ) * x) := by
    rw [mul_comm]; rfl
  have hsub : {Z : CoefIdxD n d → ℝ | etaR n d x < |r2 Z / DD n d - 1|} ⊆
      {z | 2 * Real.sqrt ((Fintype.card (CoefIdxD n d) : ℝ) * x) + 2 * x ≤
        ∑ i, z i ^ 2 - (Fintype.card (CoefIdxD n d) : ℝ)} ∪
      {z | 2 * Real.sqrt ((Fintype.card (CoefIdxD n d) : ℝ) * x) ≤
        (Fintype.card (CoefIdxD n d) : ℝ) - ∑ i, z i ^ 2} := by
    intro Z hZ
    simp only [Set.mem_ofPred_eq] at hZ
    have hr : r2 Z = ∑ i, Z i ^ 2 := rfl
    have hDc : DD n d = (Fintype.card (CoefIdxD n d) : ℝ) := rfl
    have hs0 : 0 ≤ Real.sqrt (x * DD n d) := Real.sqrt_nonneg _
    rcases lt_abs.mp hZ with h | h
    · left
      simp only [Set.mem_ofPred_eq]
      rw [← hsq, ← hr, ← hDc]
      have h1 : etaR n d x * DD n d < r2 Z - DD n d := by
        have := (lt_div_iff₀ hD).mp (by linarith : etaR n d x + 1 < r2 Z / DD n d)
        linarith
      nlinarith
    · right
      simp only [Set.mem_ofPred_eq]
      rw [← hsq, ← hr, ← hDc]
      have h1 : r2 Z / DD n d < 1 - etaR n d x := by linarith
      have h2 := (div_lt_iff₀ hD).mp h1
      nlinarith
  calc stdGauss (CoefIdxD n d) {Z | etaR n d x < |r2 Z / DD n d - 1|}
      ≤ stdGauss (CoefIdxD n d) _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-x)) + ENNReal.ofReal (Real.exp (-x)) :=
        add_le_add (BstLean.Part40.chisq_upper hcard x hx) (BstLean.Part40.chisq_lower hcard x hx)
    _ = ENNReal.ofReal (2 * Real.exp (-x)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]; ring_nf

/-- **Lemma `radius`**, on the event: `|ρ^j − 1| ≤ η_k` for every `j ≤ k`. -/
theorem radius_det (hn : 1 ≤ n) (k : ℕ) (x : ℝ) (hx : 0 < x) (hlt : etaR n d x < 1)
    (Z : CoefIdxD n d → ℝ) (hZ : |r2 Z / DD n d - 1| ≤ etaR n d x) (j : ℕ) (hj : j ≤ k) :
    |rhoZ Z ^ j - 1| ≤ etaK n d k x := by
  have hD : 0 < DD n d := by
    unfold DD
    have : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, ⟨0, by omega⟩)⟩⟩
    exact_mod_cast Fintype.card_pos
  have he : 0 ≤ etaR n d x := by unfold etaR; positivity
  let a := Real.sqrt (1 - etaR n d x)
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = 1 - etaR n d x := Real.sq_sqrt (by linarith)
  have ha1 : a ≤ 1 := by nlinarith
  have hbounds := abs_le.mp hZ
  have hr : 0 < r2 Z := by
    have := (le_div_iff₀ hD).mp (show 1 - etaR n d x ≤ r2 Z / DD n d by linarith)
    nlinarith
  have hrho : 0 ≤ rhoZ Z := by unfold rhoZ; positivity
  have hrho2 : rhoZ Z ^ 2 = DD n d / r2 Z := by
    unfold rhoZ
    rw [div_pow, Real.sq_sqrt hD.le, Real.sq_sqrt hr.le]
  have hlo : a ≤ rhoZ Z := by
    have hupper := (div_le_iff₀ hD).mp (show r2 Z / DD n d ≤ 1 + etaR n d x by linarith)
    have hmul : (1 - etaR n d x) * r2 Z ≤ DD n d := by
      nlinarith [sq_nonneg (etaR n d x)]
    have : a ^ 2 ≤ rhoZ Z ^ 2 := by rw [ha2, hrho2]; exact (le_div_iff₀ hr).mpr hmul
    nlinarith
  have hhi : rhoZ Z ≤ 1 / a := by
    have hlower := (le_div_iff₀ hD).mp (show 1 - etaR n d x ≤ r2 Z / DD n d by linarith)
    have hh : rhoZ Z ^ 2 * a ^ 2 ≤ 1 := by
      rw [ha2, hrho2]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hr).mpr
      nlinarith
    apply (le_div_iff₀ ha).mpr
    nlinarith [sq_nonneg (rhoZ Z * a - 1)]
  have hpowlo : a ^ k ≤ rhoZ Z ^ j := by
    exact (pow_le_pow_of_le_one ha.le ha1 hj).trans (pow_le_pow_left₀ ha.le hlo j)
  have hpowhi : rhoZ Z ^ j ≤ 1 / a ^ k := by
    have hbase : 1 ≤ 1 / a := (le_div_iff₀ ha).mpr (by linarith)
    have := (pow_le_pow_left₀ hrho hhi j).trans (pow_le_pow_right₀ hbase hj)
    simpa only [div_pow, one_pow] using this
  have hak : 0 < a ^ k := pow_pos ha _
  have hrec : 2 ≤ a ^ k + 1 / a ^ k := by
    have hh : 2 - a ^ k ≤ 1 / a ^ k := by
      apply (le_div_iff₀ hak).mpr
      nlinarith [sq_nonneg (a ^ k - 1)]
    linarith
  have hsqrt : Real.sqrt ((1 - etaR n d x) ^ k) = a ^ k := by
    rw [← ha2, ← pow_mul, mul_comm 2 k, pow_mul]
    exact Real.sqrt_sq (pow_nonneg ha.le _)
  unfold etaK
  rw [hsqrt, abs_le]
  constructor <;> linarith


end BstLean.Part41
