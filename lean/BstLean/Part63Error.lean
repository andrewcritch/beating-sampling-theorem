import BstLean.Part59Error

/-!
# Part 63: Prop E with its explicit constant, every `d ≥ 1`

A copy of the `d = 1` proof of `Part59Error.lean` (same private helpers), run at every `d ≥ 1`. It uses
`Part59.ErrorAux59x.normalized_bound59x`, whose feature constant is `d + 1`. `propE63` proves
`PropE59 d k K (CE63 d k K) 1`, with `CE63 = 10·|2·corrE + 2·main|` at `Λ = log(2(|K|+1))`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part63

open BstLean.Part59

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM colM contr trL frob IsSymmT Tens TSymm fval Pn varU sdU heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (sg c0 aH g0 heatA fvA Ncirc DensLaw)

variable {n d : ℕ}

private lemma sph_of_up59x {μ : Measure (Fin n → ℝ)} {K : ℝ} (h : UpLaw n μ K) : SphLaw n μ := by
  obtain ⟨hp, ρ, -, -, hμ, -⟩ := h
  refine ⟨hp, ?_⟩
  rw [hμ]
  exact (withDensity_absolutelyContinuous _ _).ae_le (BstLean.Part29.uniformSphere_ae_sphere n)

private lemma cont_integrable59x {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f μ := by
  let := hμ.prob
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hμ.sphere] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

private lemma fval_cont59x (k : ℕ) (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) :
    Continuous (fun x => fval k f0 T (mapMD M x)) := by
  classical
  unfold fval contr mapMD BstLean.Part36.coefD BstLean.Part36.monoVal
  fun_prop

/-- The uniform law is a `DensLaw` for every `Λ ≥ 0`. -/
private lemma unif_dens59x (hn : 1 ≤ n) (Λ : ℝ) (hΛ : 0 ≤ Λ) : DensLaw n (uniformSphere n) Λ := by
  refine ⟨BstLean.Part29.uniformSphere_isProbability n hn, fun _ => 1, measurable_const,
    fun _ => zero_le_one, ?_, fun x _ => ⟨?_, ?_⟩⟩
  · simp
  · rw [Real.exp_le_one_iff]; linarith
  · exact Real.one_le_exp hΛ

/-- The mixture `(μ + σ)/2` of an `UpLaw` with the uniform law is a `DensLaw`. -/
private lemma mix_dens59x (hn : 1 ≤ n) {μ : Measure (Fin n → ℝ)} {K : ℝ} (hμ : UpLaw n μ K) :
    DensLaw n ((2 : ℝ≥0∞)⁻¹ • μ + (2 : ℝ≥0∞)⁻¹ • uniformSphere n) (Real.log (2 * (|K| + 1))) := by
  obtain ⟨hp, ρ, hm, h0, hμeq, hb⟩ := hμ
  have hσ := BstLean.Part29.uniformSphere_isProbability n hn
  have hpos : (0 : ℝ) < 2 * (|K| + 1) := by positivity
  refine ⟨⟨?_⟩, fun x => (ρ x + 1) / 2, (hm.add measurable_const).div_const 2,
    fun x => by have := h0 x; positivity, ?_, fun x hx => ⟨?_, ?_⟩⟩
  · simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    exact ENNReal.inv_two_add_inv_two
  · rw [hμeq]
    have hfun : (fun x => ENNReal.ofReal ((ρ x + 1) / 2)) =
        (2 : ℝ≥0∞)⁻¹ • (fun x => ENNReal.ofReal (ρ x)) + (2 : ℝ≥0∞)⁻¹ • (fun _ => (1 : ℝ≥0∞)) := by
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_add (h0 x) zero_le_one]
      simp [ENNReal.div_eq_inv_mul, mul_add]
    rw [hfun, withDensity_add_left ((hm.ennreal_ofReal).const_smul _), withDensity_smul _ hm.ennreal_ofReal,
      withDensity_smul _ measurable_const]
    simp [withDensity_const]
  · rw [Real.exp_neg, Real.exp_log hpos]
    have := h0 x
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith [abs_nonneg K]
  · rw [Real.exp_log hpos]
    have := hb x hx
    nlinarith [le_abs_self K, abs_nonneg K]

/-- `B` is affine in the law. -/
private lemma B_mix59x (hn : 1 ≤ n) {μ : Measure (Fin n → ℝ)} {K : ℝ} (hμ : UpLaw n μ K) (k : ℕ)
    (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) :
    BofQ μ k f0 T M = 2 * BofQ ((2 : ℝ≥0∞)⁻¹ • μ + (2 : ℝ≥0∞)⁻¹ • uniformSphere n) k f0 T M -
      BofQ (uniformSphere n) k f0 T M := by
  have hσ := BstLean.Part29.uniformSphere_isProbability n hn
  have hS := sph_of_up59x hμ
  have hσS : SphLaw n (uniformSphere n) := ⟨hσ, BstLean.Part29.uniformSphere_ae_sphere n⟩
  have h1 := cont_integrable59x hS (fval_cont59x (d := d) k f0 T M)
  have h2 := cont_integrable59x hσS (fval_cont59x (d := d) k f0 T M)
  unfold BofQ
  rw [integral_add_measure (h1.smul_measure (by simp)) (h2.smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- The mixing parameter `Λ = log(2(|K|+1))`, so `e^Λ = 2(|K|+1)`. -/
noncomputable def Lam63 (K : ℝ) : ℝ := Real.log (2 * (|K| + 1))

/-- **The Prop E constant** `C_E = 10·|2·corrE + 2·main|` at `Λ = log(2(|K|+1))`, every `d ≥ 1`
(feature constant `d + 1`, `Part59.ErrorAux59x.normalized_bound59x`). -/
noncomputable def CE63 (d k : ℕ) (K : ℝ) : ℝ :=
  10 * |2 * BstLean.Part53.error53_correction_constant d k (Lam63 K) +
    2 * ErrorAux59x.mainConstant59x d k (Lam63 K)|

/-- **Prop E with its explicit constant**, every `d ≥ 1` (the proof of `Part59.propE59_d1`, run at
general `d`). -/
theorem propE63 (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (K : ℝ) :
    PropE59 d k K (CE63 d k K) 1 := by
  set Λ := Real.log (2 * (|K| + 1)) with hΛ
  have hΛ0 : 0 ≤ Λ := Real.log_nonneg (by nlinarith [abs_nonneg K])
  let C := 2 * BstLean.Part53.error53_correction_constant d k Λ +
    2 * ErrorAux59x.mainConstant59x d k Λ
  let n0 := 1
  have hE : BstLean.Part53.PropE53 d k Λ C n0 := by
    intro n hn μ hμ f0 T hT hTk
    exact ⟨BstLean.Part53.error53_integrable_dens hμ k f0 T,
      ErrorAux59x.normalized_bound59x hn hd hμ
        (BstLean.Part53.lemmaU53 d) BstLean.Part53.lemmaS53
        BstLean.Part53.lemmaTr53 k f0 T hT⟩
  show PropE59 d k K (10 * |C|) (max n0 1)
  intro n hn μ hμ f0 T hT hTk
  have hn0 : n0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨μ', hμ'⟩ : ∃ μ' : Measure (Fin n → ℝ), μ' = (2 : ℝ≥0∞)⁻¹ • μ + (2 : ℝ≥0∞)⁻¹ • uniformSphere n :=
    ⟨_, rfl⟩
  have hB : ∀ M : CoefIdxD n d → ℝ, BofQ μ k f0 T M = 2 * BofQ μ' k f0 T M -
      BofQ (uniformSphere n) k f0 T M := by
    intro M; rw [hμ']; exact B_mix59x hn1 hμ k f0 T M
  obtain ⟨i1, b1⟩ := hE n hn0 μ' (hμ' ▸ mix_dens59x hn1 hμ) f0 T hT hTk
  obtain ⟨i2, b2⟩ := hE n hn0 (uniformSphere n) (unif_dens59x hn1 Λ hΛ0) f0 T hT hTk
  set e1 := fun Z : CoefIdxD n d → ℝ => (BofQ μ' k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) ^ 2
  set e2 := fun Z : CoefIdxD n d → ℝ =>
    (BofQ (uniformSphere n) k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) ^ 2
  have hpt : ∀ Z, (BofQ μ k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) ^ 2 ≤ 8 * e1 Z + 2 * e2 Z := by
    intro Z
    rw [hB]
    simp only [e1, e2]
    nlinarith [sq_nonneg (2 * (BofQ μ' k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) +
      (BofQ (uniformSphere n) k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)))]
  have hint : Integrable (fun Z => 8 * e1 Z + 2 * e2 Z) (stdGauss (CoefIdxD n d)) :=
    (i1.const_mul 8).add (i2.const_mul 2)
  have hiE : Integrable (fun Z => (BofQ μ k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) ^ 2)
      (stdGauss (CoefIdxD n d)) :=
    BstLean.Part53.error53_integrable (sph_of_up59x hμ) k f0 T (sg n d)
  refine ⟨hiE, ?_⟩
  have hN : 0 ≤ Ncirc n d k f0 T := by
    unfold Ncirc
    exact Finset.sum_nonneg fun c _ => div_nonneg (Finset.sum_nonneg fun w _ => sq_nonneg _)
      (pow_nonneg (by unfold DD; positivity) _)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hCa : C / n * Ncirc n d k f0 T ≤ |C| / n * Ncirc n d k f0 T :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_abs_self _) hnR.le) hN
  calc ∫ Z, (BofQ μ k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) ^ 2 ∂stdGauss (CoefIdxD n d)
      ≤ ∫ Z, (8 * e1 Z + 2 * e2 Z) ∂stdGauss (CoefIdxD n d) := integral_mono hiE hint hpt
    _ = 8 * ∫ Z, e1 Z ∂stdGauss (CoefIdxD n d) + 2 * ∫ Z, e2 Z ∂stdGauss (CoefIdxD n d) := by
        rw [integral_add (i1.const_mul 8) (i2.const_mul 2), integral_const_mul, integral_const_mul]
    _ ≤ 8 * (|C| / n * Ncirc n d k f0 T) + 2 * (|C| / n * Ncirc n d k f0 T) := by
        have := b1.trans hCa; have := b2.trans hCa; linarith
    _ = 10 * |C| / n * Ncirc n d k f0 T := by ring

end BstLean.Part63
