import BstLean.Part56T1

/-!
# Part 64: Prop T1′ with explicit constants (copy of `Part56T1` with the witnesses stated)

* `Cerr64 k CD = 4 · (5/2)(k+1)² · √(2|CD|)`, `n1T1_64 CD = max 40 (⌈8|CD|⌉₊ + 2)`;
  `propT1_64_of : PropT1_56 d k C η (Cerr64 k CD) (n1T1_64 CD)`.

The private helpers are copied from `Part56T1`. Do not use `native_decide` or `axiom`.
-/

namespace BstLean.Part64

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM colM contr trL frob Tens TSymm fval varU)
open BstLean.Part43 (BofQ varFQ etaQ)
open BstLean.Part50 (qA PSDq)
open BstLean.Part53 (TF sg linZ LemmaR53 GaussPolar53)
open BstLean.Part56

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


private lemma contr_smul_vec {m : ℕ} (A : (Fin m → Fin n) → ℝ) (l : ℝ) (y : Fin m → Fin n → ℝ) :
    contr A (fun r => l • y r) = l ^ m * contr A y := by
  unfold contr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  ring

private lemma ancRK_smul (M : CoefIdxD n d → ℝ) (l : ℝ) (v : Fin n → ℝ) (j : ℕ) :
    ancRK (l • M) v j = l • ancRK M v j := by
  funext a
  unfold ancRK linZ BstLean.Part41.colM
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

private lemma gW_smul (k : ℕ) (A : Tens n) (c : KeyRK k d → ℝ) (W : CoefIdxD n d → ℝ)
    (v : Fin n → ℝ) (l : ℝ) :
    gW k A c (fun j => ancRK (l • W) v j) = gpart56 k A c W v l := by
  unfold gW gpart56
  refine Finset.sum_congr rfl fun κ _ => ?_
  split_ifs
  · simp only [ancRK_smul]
    rw [contr_smul_vec]; ring
  · rfl


private lemma qv56_eval {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (k : ℕ) (f0 : ℝ) (T : Tens n)
    (c : KeyRK k d → ℝ) (v : Fin n → ℝ) (W : CoefIdxD n d → ℝ) (l : ℝ) :
    qv56 μ k f0 T c v W l = BofQ μ k f0 T (l • W) - gW k (TF k f0 T) c (fun j => ancRK (l • W) v j) := by
  rw [B_smul hμ, gW_smul]
  rfl

private lemma qv56_poly (μ : Measure (Fin n → ℝ)) (k : ℕ) (f0 : ℝ) (T : Tens n) (c : KeyRK k d → ℝ)
    (v : Fin n → ℝ) (W : CoefIdxD n d → ℝ) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ k ∧ ∀ l, p.eval l = qv56 μ k f0 T c v W l := by
  classical
  refine ⟨Polynomial.C f0 + ∑ j ∈ Finset.Icc 1 k,
      Polynomial.C (∫ x, contr (T j) (fun _ => mapMD W x) ∂μ) * Polynomial.X ^ j -
    ∑ κ : KeyRK k d, if 2 * (κ.1.2 : ℕ) ≤ (κ.1.1 : ℕ) then
      Polynomial.C (c κ * contr (trL (κ.1.2 : ℕ) (TF k f0 T κ.1.1)) (fun r => ancRK W v (κ.2 r))) *
        Polynomial.X ^ ((κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ)) else 0, ?_, ?_⟩
  · apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · simp
      · apply Polynomial.natDegree_sum_le_of_forall_le
        intro j hj
        exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Finset.mem_Icc.mp hj).2
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro κ _
      split_ifs
      · refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
        have := κ.1.1.2
        omega
      · simp
  · intro l
    simp only [qv56, gpart56, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    congr 1
    refine Finset.sum_congr rfl fun κ _ => ?_
    split_ifs <;> simp

private lemma anc_cont (v : Fin n → ℝ) (j : ℕ) {α : Type*} [TopologicalSpace α]
    {g : α → CoefIdxD n d → ℝ} (hg : Continuous g) : Continuous fun a => ancRK (g a) v j := by
  apply continuous_pi; intro i
  unfold ancRK linZ BstLean.Part41.colM
  exact continuous_finsetSum _ fun p _ => ((continuous_apply _).comp hg).mul continuous_const

private lemma qv56_meas {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ] (k : ℕ) (f0 : ℝ) (T : Tens n)
    (c : KeyRK k d → ℝ) (v : Fin n → ℝ) (s : ℝ) :
    Measurable (fun p : (CoefIdxD n d → ℝ) × ℝ => qv56 μ k f0 T c v p.1 (p.2 / s)) := by
  classical
  have hb : ∀ j, Measurable (fun W : CoefIdxD n d → ℝ => ∫ x, contr (T j) (fun _ => mapMD W x) ∂μ) := by
    intro j
    have hc : Continuous (fun p : (CoefIdxD n d → ℝ) × (Fin n → ℝ) => contr (T j) (fun _ => mapMD p.1 p.2)) :=
      contr_cont _ mapMD_joint
    exact (hc.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have hg : Continuous (fun p : (CoefIdxD n d → ℝ) × ℝ => gpart56 k (TF k f0 T) c p.1 v (p.2 / s)) := by
    unfold gpart56
    refine continuous_finsetSum _ fun κ _ => ?_
    split_ifs
    · refine Continuous.mul (continuous_const.mul ?_) ((continuous_snd.div_const s).pow _)
      unfold contr
      refine continuous_finsetSum _ fun w _ => continuous_const.mul ?_
      refine continuous_finsetProd _ fun r _ => ?_
      exact (continuous_apply _).comp (anc_cont v _ continuous_fst)
    · exact continuous_const
  unfold qv56
  apply Measurable.sub
  · apply Measurable.add measurable_const
    apply Finset.measurable_sum
    intro j _
    exact ((hb j).comp measurable_fst).mul ((measurable_snd.div_const s).pow_const j)
  · exact hg.measurable

private lemma qA_rk1' (t : ℝ) (v x : Fin n → ℝ) : qA (rk1 t v) x = t * (∑ i, v i * x i) ^ 2 := by
  unfold qA rk1
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma integrable_of_le_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hg : Integrable g μ) (hf : AEStronglyMeasurable f μ) (h0 : ∀ a, 0 ≤ f a)
    (h : ∀ a, f a ≤ g a) : Integrable f μ :=
  hg.mono' hf (Filter.Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 a)]; exact h a)


/-- The explicit T1 constant `C_err = 4 · (5/2)(k+1)² · √(2|CD|)`. -/
noncomputable def Cerr64 (k : ℕ) (CD : ℝ) : ℝ := 4 * (5 / 2 * ((k : ℝ) + 1) ^ 2) * Real.sqrt (2 * |CD|)

/-- The explicit T1 threshold `max 40 (⌈8|CD|⌉₊ + 2)`. -/
noncomputable def n1T1_64 (CD : ℝ) : ℕ := max 40 (⌈8 * |CD|⌉₊ + 2)

/-- **Prop T1′** with explicit constants. -/
theorem propT1_64_of (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (C η CD : ℝ) (hR : LemmaR53 k)
    (hP : GaussPolar53) (hW : PropWeights56 d k) (hE : PropRKGErr56 d k) (hF : PropRKGFloor56 d k)
    (hD : PropD56 d CD) (hS : PropSurr56 d k C η) :
    PropT1_56 d k C η (Cerr64 k CD) (n1T1_64 CD) := by
  classical
  set R : ℝ := 5 / 2 * ((k : ℝ) + 1) ^ 2 with hRdef
  have hR0 : 0 ≤ R := by positivity
  set A0 : ℝ := Real.sqrt (2 * |CD|) with hA0
  show PropT1_56 d k C η (Cerr64 k CD) (n1T1_64 CD)
  rw [show Cerr64 k CD = 4 * R * A0 by rw [hRdef, hA0]; rfl]
  unfold n1T1_64
  intro n hn v hv t ht0 ht f0 T hT hTk c hc
  have hn40 : 40 ≤ n := le_trans (le_max_left _ _) hn
  have hnCD : ⌈8 * |CD|⌉₊ + 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : 1 ≤ n := by omega
  set D := lawRK n t v with hDdef
  set Q := surrRK n (KRK C n η) t v with hQdef
  have hDS : SphLaw n D := (BstLean.Part50.binghamA_antipodal hn1 _).sph
  have hQS : SphLaw n Q := (BstLean.Part50.binghamKA_antipodal hn1 _ _
    (fun x => by rw [qA_rk1']; positivity)).sph
  have := hDS.prob
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcard : 1000 ≤ Fintype.card (CoefIdxD n d) := by
    rw [BstLean.Part36.card_coefIdxD]
    have h1 : n + 1 ≤ (n + d).choose d := by
      rw [← Nat.choose_symm_add]
      calc n + 1 = (n + 1).choose n := by rw [Nat.choose_succ_self_right]
        _ ≤ (n + d).choose n := Nat.choose_le_choose n (by omega)
    nlinarith
  -- the proxy bound
  set EV := EV56 d D k f0 T with hEV
  set δ := Real.sqrt (deltaSq D d v) with hδ
  have hEV0 : 0 ≤ EV := by
    rw [hEV]; unfold EV56
    exact integral_nonneg fun Z => by unfold varFQ varU; exact integral_nonneg fun _ => sq_nonneg _
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hδA : δ ≤ A0 / Real.sqrt n := by
    have h1 := hD n (by omega) v hv t
    have hn2 : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by
      have : (40 : ℝ) ≤ n := by exact_mod_cast hn40
      linarith
    have h2 : deltaSq D d v ≤ 2 * |CD| / n := by
      refine h1.trans ?_
      rw [div_le_div_iff₀ (by linarith) hnR]
      nlinarith [le_abs_self CD, abs_nonneg CD]
    rw [hδ, hA0, ← Real.sqrt_div' _ hnR.le]
    exact Real.sqrt_le_sqrt h2
  have hδhalf : δ ≤ 1 / 2 := by
    refine hδA.trans ?_
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hnR), hA0]
    rw [show (1 / 2 : ℝ) * Real.sqrt n = Real.sqrt (n / 4) by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]; ring]
    apply Real.sqrt_le_sqrt
    have : (8 * |CD| : ℝ) ≤ ⌈8 * |CD|⌉₊ := Nat.le_ceil _
    have : ((⌈8 * |CD|⌉₊ + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hnCD
    push_cast at this
    linarith
  obtain ⟨hi1, hb1⟩ := hE n D hDS v hv f0 T hT
  have hfl := hF n D hDS v hv f0 T hT
  obtain ⟨hi2, hb2⟩ := hS n (by omega) v hv t ht0 ht f0 T hT
  set e1 : (CoefIdxD n d → ℝ) → ℝ := fun Z =>
    (BofQ D k f0 T (sg n d • Z) - gLineH D k f0 T v (sg n d • Z)) ^ 2 with he1
  set e2 : (CoefIdxD n d → ℝ) → ℝ := fun Z =>
    (gLineH Q k f0 T v (sg n d • Z) - gLineH D k f0 T v (sg n d • Z)) ^ 2 with he2
  have hb1' : ∫ Z, e1 Z ∂stdGauss (CoefIdxD n d) ≤ 2 * δ * EV := by
    set S := ∫ Z, Sfl D d k f0 T v (sg n d • Z) ∂stdGauss (CoefIdxD n d)
    have h1 : 0 < 1 - δ := by linarith
    have hS' : S ≤ 2 * EV := by
      have : (1 / 2) * S ≤ (1 - δ) * S ∨ S < 0 := by
        by_cases hS0 : 0 ≤ S
        · left; exact mul_le_mul_of_nonneg_right (by linarith) hS0
        · right; linarith
      rcases this with h | h
      · linarith
      · linarith
    calc ∫ Z, e1 Z ∂stdGauss (CoefIdxD n d) ≤ δ * S := hb1
      _ ≤ δ * (2 * EV) := mul_le_mul_of_nonneg_left hS' hδ0
      _ = 2 * δ * EV := by ring
  have hbound_int : ∫ Z, R * (2 * e1 Z + 2 * e2 Z) ∂stdGauss (CoefIdxD n d) ≤
      (4 * R * A0 / Real.sqrt n + 5 * ((k : ℝ) + 1) ^ 2 * etaQ η ^ 2) * EV := by
    rw [integral_const_mul, integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul,
      integral_const_mul]
    have h4 : 4 * R * δ * EV ≤ 4 * R * A0 / Real.sqrt n * EV := by
      have := mul_le_mul_of_nonneg_left hδA (by positivity : (0 : ℝ) ≤ 4 * R)
      have := mul_le_mul_of_nonneg_right this hEV0
      calc 4 * R * δ * EV = 4 * R * δ * EV := rfl
        _ ≤ 4 * R * (A0 / Real.sqrt n) * EV := this
        _ = _ := by ring
    have h5 : R * (2 * ∫ Z, e2 Z ∂stdGauss (CoefIdxD n d)) ≤ 5 * ((k : ℝ) + 1) ^ 2 * etaQ η ^ 2 * EV := by
      have := mul_le_mul_of_nonneg_left hb2 (by positivity : (0 : ℝ) ≤ 2 * R)
      calc R * (2 * ∫ Z, e2 Z ∂stdGauss (CoefIdxD n d)) = 2 * R * ∫ Z, e2 Z ∂stdGauss (CoefIdxD n d) := by ring
        _ ≤ 2 * R * (etaQ η ^ 2 * EV) := this
        _ = _ := by rw [hRdef]; ring
    have h6 : R * (2 * ∫ Z, e1 Z ∂stdGauss (CoefIdxD n d)) ≤ 4 * R * δ * EV := by
      have := mul_le_mul_of_nonneg_left hb1' (by positivity : (0 : ℝ) ≤ 2 * R)
      calc R * (2 * ∫ Z, e1 Z ∂stdGauss (CoefIdxD n d)) = 2 * R * ∫ Z, e1 Z ∂stdGauss (CoefIdxD n d) := by ring
        _ ≤ 2 * R * (2 * δ * EV) := this
        _ = _ := by ring
    nlinarith
  -- the polar integrand
  set cw := wRK Q d v with hcw
  obtain ⟨F, hF⟩ : ∃ F : (CoefIdxD n d → ℝ) → ℝ → ℝ≥0∞,
      F = fun W r => ENNReal.ofReal (R * (qv56 D k f0 T cw v W (r / Real.sqrt (DD n d))) ^ 2) := ⟨_, rfl⟩
  have hFm : Measurable (Function.uncurry F) := by
    rw [hF]
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul ((qv56_meas (μ := D) k f0 T cw v _).pow_const 2))
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
      ENNReal.ofReal ((BofQ D k f0 T (unitOfD Z) - gLineW Q k f0 T v (unitOfD Z)) ^ 2) ≤ f Z := by
    intro Z hZ
    obtain ⟨p, hpdeg, hpeval⟩ := qv56_poly D k f0 T cw v (unitOfD Z)
    have h1 : BofQ D k f0 T (unitOfD Z) - gLineW Q k f0 T v (unitOfD Z) = p.eval 1 := by
      rw [hpeval, qv56_eval hDS k f0 T cw v _ 1, one_smul]
      rfl
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
  -- polar independence
  have hpol : ∫⁻ Z, f Z ∂stdGauss (CoefIdxD n d) =
      ∫⁻ Z, F (unitOfD Z) (Real.sqrt (∑ α, Z α ^ 2)) ∂stdGauss (CoefIdxD n d) := by
    rw [hfdef]; exact (hP n d F hFm).symm
  have hae : ∀ᵐ Z ∂stdGauss (CoefIdxD n d), Z ≠ 0 := by
    rcases gauss_zero_null (n := n) (d := d) with h0 | hempty
    · exact measure_eq_zero_iff_ae_notMem.mp h0 |>.mono fun Z hZ => hZ
    · exfalso
      have := Fintype.card_eq_zero (α := CoefIdxD n d)
      omega
  have hbound : ∫⁻ Z, F (unitOfD Z) (Real.sqrt (∑ α, Z α ^ 2)) ∂stdGauss (CoefIdxD n d) ≤
      ∫⁻ Z, ENNReal.ofReal (R * (2 * e1 Z + 2 * e2 Z)) ∂stdGauss (CoefIdxD n d) := by
    apply lintegral_mono_ae
    filter_upwards [hae] with Z hZ
    rw [hF]
    simp only
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hR0
    rw [qv56_eval hDS k f0 T cw v _ _, smul_unit Z hZ]
    have hWQ := hW n Q hQS v hv f0 T hT (sg n d • Z)
    unfold gLineW at hWQ
    rw [hcw, hWQ]
    simp only [he1, he2]
    nlinarith [sq_nonneg (BofQ D k f0 T (sg n d • Z) + gLineH Q k f0 T v (sg n d • Z) -
      2 * gLineH D k f0 T v (sg n d • Z))]
  have hint : Integrable (fun Z => R * (2 * e1 Z + 2 * e2 Z)) (stdGauss (CoefIdxD n d)) :=
    ((hi1.const_mul 2).add (hi2.const_mul 2)).const_mul R
  have hnn : ∀ Z, 0 ≤ R * (2 * e1 Z + 2 * e2 Z) := fun Z =>
    mul_nonneg hR0 (by simp only [he1, he2]; positivity)
  have htot : ∫⁻ Z, f Z ∂stdGauss (CoefIdxD n d) ≤
      ENNReal.ofReal ((4 * R * A0 / Real.sqrt n + 5 * ((k : ℝ) + 1) ^ 2 * etaQ η ^ 2) * EV) := by
    rw [hpol]
    refine hbound.trans ?_
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
    exact ENNReal.ofReal_le_ofReal hbound_int
  set Bd : ℝ := 4 * R * A0 / Real.sqrt n + 5 * ((k : ℝ) + 1) ^ 2 * etaQ η ^ 2 with hBd
  rcases hEV0.lt_or_eq with hEVp | hEVz
  · -- Markov at level `c · EV > 0`
    have hsub : {Z : CoefIdxD n d → ℝ | Z ≠ 0 ∧ c * EV <
        (BofQ D k f0 T (unitOfD Z) - gLineW Q k f0 T v (unitOfD Z)) ^ 2} ⊆
        {Z | ENNReal.ofReal (c * EV) ≤ f Z} := by
      intro Z ⟨hZ, hX⟩
      exact (ENNReal.ofReal_le_ofReal hX.le).trans (hrem Z hZ)
    have hcN : 0 < c * EV := mul_pos hc hEVp
    refine le_trans (measure_mono hsub) (le_trans (meas_ge_le_lintegral_div hfm.aemeasurable
      (by simpa using hcN) ENNReal.ofReal_ne_top) ?_)
    refine le_trans (ENNReal.div_le_div_right htot _) ?_
    rw [← ENNReal.ofReal_div_of_pos hcN]
    apply ENNReal.ofReal_le_ofReal
    rw [show Bd * EV / (c * EV) = Bd / c by field_simp]
  · -- `EV = 0`: the event is null
    have hf0 : ∫⁻ Z, f Z ∂stdGauss (CoefIdxD n d) = 0 := by
      refine le_antisymm (htot.trans ?_) bot_le
      rw [← hEVz, mul_zero, ENNReal.ofReal_zero]
    have hfae : f =ᵐ[stdGauss (CoefIdxD n d)] 0 := (lintegral_eq_zero_iff hfm).mp hf0
    have hnull : stdGauss (CoefIdxD n d) {Z : CoefIdxD n d → ℝ | Z ≠ 0 ∧ c * EV <
        (BofQ D k f0 T (unitOfD Z) - gLineW Q k f0 T v (unitOfD Z)) ^ 2} = 0 := by
      apply measure_mono_null (t := {Z | f Z ≠ 0})
      · intro Z ⟨hZ, hX⟩
        have h1 := hrem Z hZ
        have h2 : 0 < (BofQ D k f0 T (unitOfD Z) - gLineW Q k f0 T v (unitOfD Z)) ^ 2 := by
          rw [← hEVz, mul_zero] at hX; exact hX
        intro hfz
        rw [hfz] at h1
        exact absurd (ENNReal.ofReal_eq_zero.mp (le_antisymm h1 bot_le)) (not_le.mpr h2)
      · exact hfae
    rw [hnull]
    exact bot_le

end BstLean.Part64
