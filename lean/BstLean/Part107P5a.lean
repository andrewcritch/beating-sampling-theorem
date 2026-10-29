import BstLean.Part107Defs

/-!
# Part 107 (P5), tools: the two-point statistic as an integral over `(u, u′)`
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part105

lemma dot_sphProj_self_le {n : ℕ} (y : Fin n → ℝ) : dot (sphProj y) (sphProj y) ≤ 1 := by
  unfold dot sphProj
  simp only [Pi.smul_apply, smul_eq_mul]
  have hS0 : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h : ∑ i, 1 / Real.sqrt (∑ i, y i ^ 2) * y i * (1 / Real.sqrt (∑ i, y i ^ 2) * y i) =
      (1 / Real.sqrt (∑ i, y i ^ 2)) ^ 2 * ∑ i, y i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h]
  rcases eq_or_lt_of_le hS0 with h0 | h0
  · rw [← h0]; simp
  · rw [one_div, inv_pow, Real.sq_sqrt hS0, inv_mul_cancel₀ h0.ne']

lemma abs_cosA_le {n : ℕ} (g g' : Fin n → ℝ) : |cosA g g'| ≤ 1 := by
  unfold cosA
  rw [← sq_le_one_iff_abs_le_one]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (sphProj g) (sphProj g')
  rw [← dot_self_eq, ← dot_self_eq] at h
  have h1 := dot_sphProj_self_le g
  have h2 := dot_sphProj_self_le g'
  have h3 : 0 ≤ dot (sphProj g) (sphProj g) := by
    rw [dot_self_eq]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have h4 : 0 ≤ dot (sphProj g') (sphProj g') := by
    rw [dot_self_eq]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have h5 : (dot (sphProj g) (sphProj g')) ^ 2 ≤
      dot (sphProj g) (sphProj g) * dot (sphProj g') (sphProj g') := h
  nlinarith

lemma abs_aR_le {n : ℕ} (r : ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) : |aR r p| ≤ 1 := abs_cosA_le _ _

lemma measurable_cosA2 {n : ℕ} :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => cosA p.1 p.2) :=
  measurable_dot2.comp
    ((measurable_sphProj.comp measurable_fst).prodMk (measurable_sphProj.comp measurable_snd))

lemma measurable_aR {n : ℕ} (r : ℝ) : Measurable (aR (n := n) r) :=
  measurable_cosA2.comp
    (measurable_fst.prodMk ((measurable_fst.const_smul r).add (measurable_snd.const_smul (sC r))))

/-- `ψ` composed with the clamp to `[−1, 1]`. -/
noncomputable def clampF (ψ : ℝ → ℝ) : ℝ → ℝ := fun a => ψ (max (-1) (min 1 a))

lemma clampF_eq (ψ : ℝ → ℝ) {a : ℝ} (ha : |a| ≤ 1) : clampF ψ a = ψ a := by
  obtain ⟨h1, h2⟩ := abs_le.mp ha
  unfold clampF
  rw [min_eq_right h2, max_eq_right h1]

lemma clampF_BM {ψ : ℝ → ℝ} (hψ : Measurable ψ) (C : ℝ) (hC : ∀ a, |a| ≤ 1 → |ψ a| ≤ C) :
    BM (clampF ψ) := by
  refine ⟨hψ.comp (measurable_const.max (measurable_const.min measurable_id)), C, fun a => ?_⟩
  refine hC _ (abs_le.mpr ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩)

/-- `E_W ψ(x·x′)` at a pair `z = (u, u′)`. -/
noncomputable def Tw (N n d : ℕ) (σ : ℝ) (ψ : ℝ → ℝ) (z : (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  ∫ W, ψ (cosA (bwEval W z.1) (bwEval W z.2)) ∂bwGauss N n d σ

/-- `E[ψ(a) | r]`. -/
noncomputable def Mr (n : ℕ) (ψ : ℝ → ℝ) (r : ℝ) : ℝ := ∫ p, ψ (aR r p) ∂gg n

lemma Mr_clamp (n : ℕ) (ψ : ℝ → ℝ) (r : ℝ) : Mr n (clampF ψ) r = Mr n ψ r := by
  unfold Mr
  exact integral_congr_ae (Filter.Eventually.of_forall fun p => clampF_eq ψ (abs_aR_le r p))

lemma twoPt_clamp (N n d : ℕ) (σ : ℝ) (ψ : ℝ → ℝ) :
    twoPt N n d σ (clampF ψ) = twoPt N n d σ ψ := by
  unfold twoPt
  simp_rw [clampF_eq ψ (abs_cosA_le _ _)]

lemma BM_aR {n : ℕ} {ψ : ℝ → ℝ} (hψ : BM ψ) (r : ℝ) : BM (fun p => ψ (aR (n := n) r p)) :=
  hψ.comp (measurable_aR r)

section
variable {N n d : ℕ} {σ : ℝ} {ψ : ℝ → ℝ}

lemma mG1 : Measurable (fun q : (CoefIdx N n d → ℝ) × ((Fin N → ℝ) × (Fin N → ℝ)) =>
    (q.1, q.2.1)) := by fun_prop

lemma mG2 : Measurable (fun q : (CoefIdx N n d → ℝ) × ((Fin N → ℝ) × (Fin N → ℝ)) =>
    (q.1, q.2.2)) := by fun_prop

lemma mG3 : Measurable (fun q : (CoefIdx N n d → ℝ) × ((Fin N → ℝ) × (Fin N → ℝ)) =>
    bwEval q.1 q.2.1) := (measurable_bwEval2 (k := N) (q := n) (d := d)).comp mG1

lemma mG4 : Measurable (fun q : (CoefIdx N n d → ℝ) × ((Fin N → ℝ) × (Fin N → ℝ)) =>
    bwEval q.1 q.2.2) := (measurable_bwEval2 (k := N) (q := n) (d := d)).comp mG2

lemma measurable_G :
    Measurable (fun q : (CoefIdx N n d → ℝ) × ((Fin N → ℝ) × (Fin N → ℝ)) =>
      cosA (bwEval q.1 q.2.1) (bwEval q.1 q.2.2)) := by
  have h : Measurable (fun q : (CoefIdx N n d → ℝ) × ((Fin N → ℝ) × (Fin N → ℝ)) =>
      ((bwEval q.1 q.2.1 : Fin n → ℝ), (bwEval q.1 q.2.2 : Fin n → ℝ))) :=
    Measurable.prodMk mG3 mG4
  have h2 := Measurable.comp (measurable_cosA2 (n := n)) h
  exact h2

lemma BM_G (hψ : BM ψ) :
    BM (fun q : (CoefIdx N n d → ℝ) × ((Fin N → ℝ) × (Fin N → ℝ)) =>
      ψ (cosA (bwEval q.1 q.2.1) (bwEval q.1 q.2.2))) :=
  hψ.comp measurable_G

lemma BM_Tw (hψ : BM ψ) : BM (Tw N n d σ ψ) := (BM_G hψ).integral_left (bwGauss N n d σ)

lemma twoPt_prod (hN : 1 ≤ N) (hψ : BM ψ) :
    twoPt N n d σ ψ = ∫ z, Tw N n d σ ψ z ∂(uniformSphere N).prod (uniformSphere N) := by
  have := uniformSphere_isProbability N hN
  have hG := BM_G (N := N) (n := n) (d := d) hψ
  have h1 : ∀ W : CoefIdx N n d → ℝ,
      ∫ u, ∫ u', ψ (cosA (bwEval W u) (bwEval W u')) ∂uniformSphere N ∂uniformSphere N =
        ∫ z : (Fin N → ℝ) × (Fin N → ℝ), ψ (cosA (bwEval W z.1) (bwEval W z.2))
          ∂(uniformSphere N).prod (uniformSphere N) := fun W =>
    (integral_prod _ ((hG.comp (measurable_prodMk_left (x := W))).integrable _)).symm
  unfold twoPt
  simp_rw [h1]
  rw [integral_integral_swap]
  · rfl
  · exact hG.integrable _

lemma ae_unit (hN : 1 ≤ N) : ∀ᵐ z ∂(uniformSphere N).prod (uniformSphere N),
    dot z.1 z.1 = 1 ∧ dot z.2 z.2 = 1 := by
  have := uniformSphere_isProbability N hN
  have h := uniformSphere_ae_sphere N
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := uniformSphere N)
    (ν := uniformSphere N)).ae h, (Measure.quasiMeasurePreserving_snd (μ := uniformSphere N)
    (ν := uniformSphere N)).ae h] with z h1 h2
  rw [dot_self_eq, dot_self_eq]
  exact ⟨h1, h2⟩

lemma int_of_unit_bdd (hN : 1 ≤ N) {f : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} (hf : Measurable f)
    (C : ℝ) (h : ∀ z : (Fin N → ℝ) × (Fin N → ℝ), dot z.1 z.1 = 1 → dot z.2 z.2 = 1 → |f z| ≤ C) :
    Integrable f ((uniformSphere N).prod (uniformSphere N)) := by
  have := uniformSphere_isProbability N hN
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_unit hN] with z hz
  simpa using h z hz.1 hz.2

/-- The workhorse: a bound of `E[ψ(a) | r(t)]` for unit `u, u′` gives a bound of `twoPt`. -/
theorem twoPt_le (hT : TwoPoint107) (hN : 1 ≤ N) (hσ : σ ≠ 0) (hψ : BM ψ)
    (Φ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ)
    (hΦ : Integrable Φ ((uniformSphere N).prod (uniformSphere N)))
    (hle : ∀ z : (Fin N → ℝ) × (Fin N → ℝ), dot z.1 z.1 = 1 → dot z.2 z.2 = 1 →
      Mr n ψ (rW d (dot z.1 z.2)) ≤ Φ z) :
    twoPt N n d σ ψ ≤ ∫ z, Φ z ∂(uniformSphere N).prod (uniformSphere N) := by
  have := uniformSphere_isProbability N hN
  rw [twoPt_prod hN hψ]
  refine integral_mono_ae ((BM_Tw hψ).integrable _) hΦ ?_
  filter_upwards [ae_unit hN] with z hz
  have : Tw N n d σ ψ z = Mr n ψ (rW d (dot z.1 z.2)) :=
    hT N n d σ z.1 z.2 ψ hσ hz.1 hz.2 hψ.meas
  rw [this]
  exact hle z hz.1 hz.2

end

end BstLean.Part107
