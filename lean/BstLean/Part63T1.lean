import BstLean.Part59T1

/-!
# Part 63: Prop T1* with its explicit witnesses

A copy of `Part59T1.lean` (same private helpers, same proof; the public definitions `trc59`, `hco59`,
`qv59` and `qv59_eval` are reused from Part 59). `propT1s63` proves
`PropT1_59 d k K (2.5(k+1)²·|C_E|) (max n_E 40)` from `PropE59 d k K C_E n_E`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part63

open BstLean.Part59

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT Tens TSymm fval In41 Pn heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part40 (SphLaw)
open BstLean.Part53 (sg c0 aH g0 heatA fvA TF Tcirc Ncirc LemmaR53 GaussPolar53)

variable {n d : ℕ}

private lemma contr_smul {j : ℕ} (A : (Fin j → Fin n) → ℝ) (l : ℝ) (y : Fin n → ℝ) :
    contr A (fun _ => l • y) = l ^ j * contr A (fun _ => y) := by
  unfold contr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  ring

private lemma contr_sum {j : ℕ} {α : Type*} (s : Finset α) (a : α → ℝ) (B : α → (Fin j → Fin n) → ℝ)
    (y : Fin n → ℝ) :
    contr (fun w => ∑ i ∈ s, a i * B i w) (fun _ => y) = ∑ i ∈ s, a i * contr (B i) (fun _ => y) := by
  unfold contr
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro w _
  ring

private lemma contr_heatA (k : ℕ) (v : ℝ) (A : Tens n) (c : ℕ) (y : Fin n → ℝ) :
    contr (heatA k v A c) (fun _ => y) =
      ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k), hco59 v c i * contr (trc59 A c i) (fun _ => y) := by
  have : heatA k v A c = fun w => ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
      hco59 v c i * trc59 A c i w := rfl
  rw [this, contr_sum]

private lemma mapMD_smul (v : CoefIdxD n d → ℝ) (l : ℝ) (x : Fin n → ℝ) :
    mapMD (l • v) x = l • mapMD v x := by
  funext a
  unfold mapMD BstLean.Part36.coefD
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro β _
  split_ifs <;> simp [mul_assoc]

private lemma mapMD_cont (Z : CoefIdxD n d → ℝ) : Continuous (fun x => mapMD Z x) := by
  classical
  apply continuous_pi
  intro a
  unfold mapMD
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro β _
  apply Continuous.const_mul
  exact continuous_multiset_prod β.val (fun i _ => continuous_apply i)

private lemma contr_cont {j : ℕ} (A : (Fin j → Fin n) → ℝ) {α : Type*} [TopologicalSpace α]
    {g : α → Fin n → ℝ} (hg : Continuous g) : Continuous (fun x => contr A (fun _ => g x)) := by
  unfold contr
  apply continuous_finsetSum; intro w _
  apply Continuous.mul continuous_const
  apply continuous_finsetProd; intro t _
  exact (continuous_apply _).comp hg

private lemma sphere_cont_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) {f : (Fin n → ℝ) → ℝ}
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

private lemma B_smul {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (k : ℕ) (f0 : ℝ) (T : Tens n)
    (v : CoefIdxD n d → ℝ) (l : ℝ) :
    BofQ μ k f0 T (l • v) = f0 + ∑ j ∈ Finset.Icc 1 k, (∫ x, contr (T j) (fun _ => mapMD v x) ∂μ) * l ^ j := by
  let := hμ.prob
  unfold BofQ fval
  simp_rw [mapMD_smul, contr_smul]
  have hint : ∀ j, Integrable (fun x => contr (T j) (fun _ => mapMD v x)) μ :=
    fun j => sphere_cont_integrable hμ (contr_cont _ (mapMD_cont v))
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun j _ => (hint j).const_mul _),
    integral_const, integral_finsetSum _ fun j _ => (hint j).const_mul _]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  congr 1
  apply Finset.sum_congr rfl; intro j _
  rw [integral_const_mul, mul_comm]

private lemma g0_smul (k : ℕ) (f0 : ℝ) (T : Tens n) (v : CoefIdxD n d → ℝ) (l : ℝ) :
    g0 n d k f0 T (l • v) = ∑ c ∈ Finset.range (k + 1), ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
      hco59 (aH n d) c i * contr (trc59 (TF k f0 T) c i) (fun _ => colM v default) * l ^ c := by
  unfold g0 fvA
  have hcol : colM (l • v) default = l • colM v default := rfl
  rw [hcol]
  apply Finset.sum_congr rfl; intro c _
  rw [contr_smul, contr_heatA, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  ring

private lemma qv59_poly (μ : Measure (Fin n → ℝ)) (k : ℕ) (f0 : ℝ) (T : Tens n) (v : CoefIdxD n d → ℝ) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ k ∧ ∀ l, p.eval l = qv59 μ k f0 T v l := by
  classical
  refine ⟨Polynomial.C f0 + ∑ j ∈ Finset.Icc 1 k,
      Polynomial.C (∫ x, contr (T j) (fun _ => mapMD v x) ∂μ) * Polynomial.X ^ j -
    ∑ c ∈ Finset.range (k + 1), ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
      Polynomial.C (hco59 (aH n d) c i * contr (trc59 (TF k f0 T) c i) (fun _ => colM v default)) *
        Polynomial.X ^ c, ?_, ?_⟩
  · apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · simp
      · apply Polynomial.natDegree_sum_le_of_forall_le
        intro j hj
        exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Finset.mem_Icc.mp hj).2
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro c hc
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i _
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hc))
  · intro l
    simp [qv59, Polynomial.eval_finsetSum]

private lemma mapMD_joint : Continuous (fun p : (CoefIdxD n d → ℝ) × (Fin n → ℝ) => mapMD p.1 p.2) := by
  classical
  apply continuous_pi
  intro a
  unfold mapMD
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro β _
  apply Continuous.mul
  · unfold BstLean.Part36.coefD
    split_ifs
    · exact (continuous_apply _).comp continuous_fst
    · exact continuous_const
  · exact continuous_multiset_prod β.val (fun i _ => (continuous_apply i).comp continuous_snd)

private lemma qv59_meas {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ] (k : ℕ) (f0 : ℝ) (T : Tens n) (s : ℝ) :
    Measurable (fun p : (CoefIdxD n d → ℝ) × ℝ => qv59 μ k f0 T p.1 (p.2 / s)) := by
  classical
  have hb : ∀ j, Measurable (fun v : CoefIdxD n d → ℝ => ∫ x, contr (T j) (fun _ => mapMD v x) ∂μ) := by
    intro j
    have hc : Continuous (fun p : (CoefIdxD n d → ℝ) × (Fin n → ℝ) => contr (T j) (fun _ => mapMD p.1 p.2)) :=
      contr_cont _ mapMD_joint
    exact (hc.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have hk : ∀ c i, Measurable (fun v : CoefIdxD n d → ℝ => contr (trc59 (TF k f0 T) c i) (fun _ => colM v default)) := by
    intro c i
    apply Continuous.measurable
    apply contr_cont
    exact continuous_pi fun a => continuous_apply _
  unfold qv59
  apply Measurable.sub
  · apply Measurable.add measurable_const
    apply Finset.measurable_sum
    intro j _
    exact ((hb j).comp measurable_fst).mul ((measurable_snd.div_const s).pow_const j)
  · apply Finset.measurable_sum
    intro c _
    apply Finset.measurable_sum
    intro i _
    exact (measurable_const.mul ((hk c i).comp measurable_fst)).mul ((measurable_snd.div_const s).pow_const _)

private lemma upLaw_sph' {μ : Measure (Fin n → ℝ)} {K : ℝ} (h : UpLaw n μ K) : SphLaw n μ := by
  obtain ⟨hp, ρ, -, -, hμ, -⟩ := h
  refine ⟨hp, ?_⟩
  rw [hμ]
  exact (withDensity_absolutelyContinuous _ _).ae_le (BstLean.Part29.uniformSphere_ae_sphere n)

private lemma heatA_top' (k : ℕ) (v : ℝ) (A : Tens n) : heatA k v A k = A k := by
  funext w
  unfold heatA
  have : (Finset.range (k + 1)).filter (fun i => k + 2 * i ≤ k) = {0} := by
    ext i; simp
  rw [this, Finset.sum_singleton]
  have hf : ((k.factorial : ℝ) / (k.factorial : ℝ)) = 1 := div_self (by positivity)
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_zero, add_zero, hf, one_mul]
  unfold trL
  simp only [Finset.univ_unique, Finset.sum_singleton]
  show A k (BstLean.Part41.glue k 0 default fun t => w ⟨t.1, by have := t.2; omega⟩) = A k w
  congr 1

private lemma Ncirc_pos' (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (f0 : ℝ) (T : Tens n) (hTk : 0 < frob (T k)) :
    0 < Ncirc n d k f0 T := by
  have hD : 0 < DD n d := BstLean.Part36.DD_pos hn
  have htop : frob (Tcirc n d k f0 T k) = frob (T k) := by
    unfold Tcirc
    rw [heatA_top']
    congr 1
    funext w
    simp [TF, show k ≠ 0 by omega]
  unfold Ncirc
  apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun c => frob (Tcirc n d k f0 T c) / DD n d ^ c)
    (fun c _ => div_nonneg (Finset.sum_nonneg fun w _ => sq_nonneg _) (pow_pos hD c).le)
    (Finset.mem_Icc.mpr ⟨hk, le_rfl⟩))
  rw [htop]
  exact div_pos hTk (pow_pos hD k)

private lemma gauss_zero_null : stdGauss (CoefIdxD n d) {0} = 0 ∨ IsEmpty (CoefIdxD n d) := by
  rcases isEmpty_or_nonempty (CoefIdxD n d) with h | h
  · exact Or.inr h
  · obtain ⟨i0⟩ := h
    left
    apply measure_mono_null (t := (fun Z : CoefIdxD n d → ℝ => Z i0) ⁻¹' {0})
    · intro Z hZ; simp only [Set.mem_singleton_iff] at hZ; simp [hZ]
    · unfold stdGauss
      rw [(measurePreserving_eval (fun _ : CoefIdxD n d => ProbabilityTheory.gaussianReal 0 1) i0).measure_preimage
        (measurableSet_singleton _).nullMeasurableSet]
      have := ProbabilityTheory.nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
      exact measure_singleton 0

private lemma unit_sumsq {Z : CoefIdxD n d → ℝ} (hZ : Z ≠ 0) : ∑ α, unitOfD Z α ^ 2 = 1 := by
  have hS : 0 < ∑ α, Z α ^ 2 := by
    obtain ⟨α, hα⟩ : ∃ α, Z α ≠ 0 := by
      by_contra h; push Not at h; exact hZ (funext h)
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun β _ => sq_nonneg (Z β)) (Finset.mem_univ α))
  unfold unitOfD
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, div_pow, one_pow, Real.sq_sqrt hS.le, one_div, inv_mul_cancel₀ hS.ne']

private lemma measurable_unitOfD : Measurable (unitOfD (n := n) (d := d)) := by
  unfold unitOfD
  exact (measurable_const.div (Real.continuous_sqrt.measurable.comp (by fun_prop))).smul measurable_id

private lemma ofReal_integral_le' {α : Type*} [MeasurableSpace α] {ν : Measure α} {g : α → ℝ}
    (hg : ∀ x, 0 ≤ g x) : ENNReal.ofReal (∫ x, g x ∂ν) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂ν := by
  by_cases hi : Integrable g ν
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hg)]
  · rw [integral_undef hi, ENNReal.ofReal_zero]; exact bot_le

private lemma smul_unit (Z : CoefIdxD n d → ℝ) (hZ : Z ≠ 0) :
    (Real.sqrt (∑ α, Z α ^ 2) / Real.sqrt (DD n d)) • unitOfD Z = sg n d • Z := by
  have hS : 0 < ∑ α, Z α ^ 2 := by
    obtain ⟨α, hα⟩ : ∃ α, Z α ≠ 0 := by
      by_contra h; push Not at h; exact hZ (funext h)
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun β _ => sq_nonneg (Z β)) (Finset.mem_univ α))
  have hs : Real.sqrt (∑ α, Z α ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hS).ne'
  unfold unitOfD sg
  rw [smul_smul]
  congr 1
  field_simp

/-- **Prop T1* with its explicit witnesses** `C₁ = 2.5(k+1)²·|C_E|`, `n₁ = max(n_E, 40)`
(copy of `Part59.propT1s_of`). -/
theorem propT1s63 (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (K CE : ℝ) (nE : ℕ)
    (hE : PropE59 d k K CE nE) (hR : LemmaR53 k) (hP : GaussPolar53) :
    PropT1_59 d k K (5 / 2 * ((k : ℝ) + 1) ^ 2 * |CE|) (max nE 40) := by
  classical
  set R : ℝ := 5 / 2 * ((k : ℝ) + 1) ^ 2 with hRdef
  have hR0 : 0 ≤ R := by positivity
  intro n hn μ hμ f0 T hT hTk c hc
  have hnE : nE ≤ n := le_trans (le_max_left _ _) hn
  have hn40 : 40 ≤ n := le_trans (le_max_right _ _) hn
  have hμS := upLaw_sph' hμ
  have := hμS.prob
  have hN := Ncirc_pos' (d := d) (by omega) k hk f0 T hTk
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcard : 1000 ≤ Fintype.card (CoefIdxD n d) := by
    rw [BstLean.Part36.card_coefIdxD]
    have h1 : n + 1 ≤ (n + d).choose d := by
      rw [← Nat.choose_symm_add]
      calc n + 1 = (n + 1).choose n := by rw [Nat.choose_succ_self_right]
        _ ≤ (n + d).choose n := Nat.choose_le_choose n (by omega)
    nlinarith
  have hDpos : 0 < DD n d := BstLean.Part36.DD_pos (by omega)
  -- the polar integrand
  obtain ⟨F, hF⟩ : ∃ F : (CoefIdxD n d → ℝ) → ℝ → ℝ≥0∞,
      F = fun v r => ENNReal.ofReal (R * (qv59 μ k f0 T v (r / Real.sqrt (DD n d))) ^ 2) := ⟨_, rfl⟩
  have hFm : Measurable (Function.uncurry F) := by
    rw [hF]
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul ((qv59_meas (μ := μ) k f0 T _).pow_const 2))
  have hrad : Measurable (fun Z : CoefIdxD n d → ℝ => Real.sqrt (∑ α, Z α ^ 2)) :=
    Real.continuous_sqrt.measurable.comp (by fun_prop)
  obtain ⟨f, hfdef⟩ : ∃ f : (CoefIdxD n d → ℝ) → ℝ≥0∞,
      f = fun Z => ∫⁻ Z', F (unitOfD Z) (Real.sqrt (∑ α, Z' α ^ 2)) ∂stdGauss (CoefIdxD n d) := ⟨_, rfl⟩
  have hfm : Measurable f := by
    have h2 : Measurable (fun p : (CoefIdxD n d → ℝ) × (CoefIdxD n d → ℝ) =>
        (unitOfD p.1, Real.sqrt (∑ α, p.2 α ^ 2))) :=
      (measurable_unitOfD.comp measurable_fst).prodMk (hrad.comp measurable_snd)
    have h3 : Measurable (fun p : (CoefIdxD n d → ℝ) × (CoefIdxD n d → ℝ) =>
        F (unitOfD p.1) (Real.sqrt (∑ α, p.2 α ^ 2))) := hFm.comp h2
    rw [hfdef]
    exact h3.lintegral_prod_right'
  -- the Remez step
  have hrem : ∀ Z : CoefIdxD n d → ℝ, Z ≠ 0 →
      ENNReal.ofReal ((BofQ μ k f0 T (unitOfD Z) - g0 n d k f0 T (unitOfD Z)) ^ 2) ≤ f Z := by
    intro Z _
    obtain ⟨p, hpdeg, hpeval⟩ := qv59_poly μ k f0 T (unitOfD Z)
    have h1 : BofQ μ k f0 T (unitOfD Z) - g0 n d k f0 T (unitOfD Z) = p.eval 1 := by
      rw [hpeval, qv59_eval hμS k f0 T _ 1, one_smul]
    have hR' := hR (CoefIdxD n d) hcard p hpdeg
    rw [h1]
    calc ENNReal.ofReal (p.eval 1 ^ 2)
        ≤ ENNReal.ofReal (R * ∫ Z', (p.eval (Real.sqrt (∑ i, Z' i ^ 2) /
            Real.sqrt (Fintype.card (CoefIdxD n d)))) ^ 2 ∂stdGauss (CoefIdxD n d)) :=
          ENNReal.ofReal_le_ofReal hR'
      _ = ENNReal.ofReal (∫ Z', R * (p.eval (Real.sqrt (∑ i, Z' i ^ 2) /
            Real.sqrt (Fintype.card (CoefIdxD n d)))) ^ 2 ∂stdGauss (CoefIdxD n d)) := by
          rw [integral_const_mul]
      _ ≤ ∫⁻ Z', ENNReal.ofReal (R * (p.eval (Real.sqrt (∑ i, Z' i ^ 2) /
            Real.sqrt (Fintype.card (CoefIdxD n d)))) ^ 2) ∂stdGauss (CoefIdxD n d) :=
          ofReal_integral_le' (fun Z' => mul_nonneg hR0 (sq_nonneg _))
      _ = f Z := by
          rw [hfdef, hF]
          apply lintegral_congr
          intro Z'
          simp only
          rw [hpeval]
          rfl
  -- Markov
  have hsub : {Z : CoefIdxD n d → ℝ | Z ≠ 0 ∧ c * Ncirc n d k f0 T ≤
      (BofQ μ k f0 T (unitOfD Z) - g0 n d k f0 T (unitOfD Z)) ^ 2} ⊆
      {Z | ENNReal.ofReal (c * Ncirc n d k f0 T) ≤ f Z} := by
    intro Z ⟨hZ, hX⟩
    exact (ENNReal.ofReal_le_ofReal hX).trans (hrem Z hZ)
  have hcN : 0 < c * Ncirc n d k f0 T := mul_pos hc hN
  refine le_trans (measure_mono hsub) (le_trans (meas_ge_le_lintegral_div hfm.aemeasurable
    (by simpa using hcN) ENNReal.ofReal_ne_top) ?_)
  -- polar independence
  have hpol : ∫⁻ Z, f Z ∂stdGauss (CoefIdxD n d) =
      ∫⁻ Z, F (unitOfD Z) (Real.sqrt (∑ α, Z α ^ 2)) ∂stdGauss (CoefIdxD n d) := by
    rw [hfdef]; exact (hP n d F hFm).symm
  -- a.e. `Z ≠ 0`
  have hae : ∀ᵐ Z ∂stdGauss (CoefIdxD n d), Z ≠ 0 := by
    rcases gauss_zero_null (n := n) (d := d) with h0 | hempty
    · exact measure_eq_zero_iff_ae_notMem.mp h0 |>.mono fun Z hZ => hZ
    · exfalso
      have := Fintype.card_eq_zero (α := CoefIdxD n d)
      omega
  set e1 : (CoefIdxD n d → ℝ) → ℝ := fun Z => (BofQ μ k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) ^ 2
  obtain ⟨hi1, hb1⟩ := hE n hnE μ hμ f0 T hT hTk
  have hbound : ∫⁻ Z, F (unitOfD Z) (Real.sqrt (∑ α, Z α ^ 2)) ∂stdGauss (CoefIdxD n d) ≤
      ∫⁻ Z, ENNReal.ofReal (R * e1 Z) ∂stdGauss (CoefIdxD n d) := by
    apply lintegral_mono_ae
    filter_upwards [hae] with Z hZ
    rw [hF]
    simp only
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hR0
    rw [qv59_eval hμS k f0 T _, smul_unit Z hZ]
  have hint : Integrable (fun Z => R * e1 Z) (stdGauss (CoefIdxD n d)) := hi1.const_mul R
  have hnn : ∀ Z, 0 ≤ R * e1 Z := fun Z => mul_nonneg hR0 (by simp only [e1]; positivity)
  rw [hpol]
  refine le_trans (ENNReal.div_le_div_right hbound _) ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn),
    ← ENNReal.ofReal_div_of_pos hcN]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_const_mul]
  rw [div_le_div_iff₀ hcN (mul_pos hnR hc)]
  have hb1' : ∫ Z, e1 Z ∂stdGauss (CoefIdxD n d) ≤ |CE| / n * Ncirc n d k f0 T :=
    hb1.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_abs_self _) hnR.le) hN.le)
  calc R * (∫ Z, e1 Z ∂stdGauss (CoefIdxD n d)) * ((n : ℝ) * c)
      ≤ R * (|CE| / n * Ncirc n d k f0 T) * ((n : ℝ) * c) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb1' hR0) (by positivity)
    _ = R * |CE| * (c * Ncirc n d k f0 T) := by field_simp

end BstLean.Part63
