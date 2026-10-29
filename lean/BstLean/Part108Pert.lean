import BstLean.Part108Defs

/-!
# Part 108: the perturbation bound (`PertBound108`)

For fixed `W`, `τ`, blocks `ω`, and the test function `ψ = psi ρ_A A₁ F`:
`(|g − B| + sd_μ/2)² ≤ 4·(1/k) Σ_i ψ(x_i)² + (9/2)·∫ ψ(W(u)/|W(u)|)² du`; then the mean over the
Gaussian version of `F` (`HtailMom108`) and of `A₁` (`EvalMom108`), by Tonelli.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part108

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105
open scoped ENNReal

/-- The abstract inequality: `(|mean_k a − E f| + sd(f)/2)² ≤ 4·mean_k a² + (9/2)·E f²`. -/
lemma pert_abs {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    {f : α → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) {k : ℕ} (hk : 1 ≤ k)
    (a : Fin k → ℝ) :
    Integrable (fun x => f x ^ 2) P ∧
    (|(∑ i, a i) / (k : ℝ) - ∫ x, f x ∂P| +
        1 / 2 * Real.sqrt (∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P)) ^ 2 ≤
      4 * ((∑ i, a i ^ 2) / (k : ℝ)) + 9 / 2 * ∫ x, f x ^ 2 ∂P := by
  have hfi : Integrable f P :=
    Integrable.mono' (integrable_const M) hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa using hM x)
  have hf2 : Integrable (fun x => f x ^ 2) P := by
    refine Integrable.mono' (integrable_const (M ^ 2)) (hf.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
  refine ⟨hf2, ?_⟩
  set B := ∫ x, f x ∂P with hB
  have hV : ∫ x, (f x - B) ^ 2 ∂P = ∫ x, f x ^ 2 ∂P - B ^ 2 := by
    have e : ∀ x, (f x - B) ^ 2 = f x ^ 2 - 2 * B * f x + B ^ 2 := fun x => by ring
    simp_rw [e]
    have i1 : Integrable (fun x => 2 * B * f x) P := hfi.const_mul _
    have i2 : Integrable (fun x => f x ^ 2 - 2 * B * f x) P := hf2.sub i1
    rw [integral_add (f := fun x => f x ^ 2 - 2 * B * f x) (g := fun _ => B ^ 2) i2
        (integrable_const _),
      integral_sub (f := fun x => f x ^ 2) (g := fun x => 2 * B * f x) hf2 i1,
      integral_const_mul, integral_const, ← hB]
    simp
    ring
  have hV0 : 0 ≤ ∫ x, (f x - B) ^ 2 ∂P := integral_nonneg fun x => sq_nonneg _
  set V := ∫ x, (f x - B) ^ 2 ∂P with hVdef
  have hs2 : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV0
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hcs : (∑ i, a i) ^ 2 ≤ (k : ℝ) * ∑ i, a i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin k))) (f := a)
    simpa using this
  have hg2 : ((∑ i, a i) / (k : ℝ)) ^ 2 ≤ (∑ i, a i ^ 2) / (k : ℝ) := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hk0]
    have := mul_le_mul_of_nonneg_right hcs hk0.le
    nlinarith [this]
  set g := (∑ i, a i) / (k : ℝ) with hg
  have h1 := sq_abs (g - B)
  nlinarith [sq_nonneg (|g - B| - Real.sqrt V / 2), sq_nonneg (g + B), h1, hs2, hg2, hV, hV0]

/-- A continuous function is bounded on the closed unit ball. -/
lemma cont_bdd_ball {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (hφ : Continuous φ) :
    ∃ M : ℝ, ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 ≤ 1 → |φ x| ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := fun _ : Fin n => (-1 : ℝ))
    (b := fun _ : Fin n => (1 : ℝ))).exists_bound_of_continuousOn hφ.continuousOn
  refine ⟨C, fun x hx => ?_⟩
  have hi : ∀ i, |x i| ≤ 1 := fun i =>
    (sq_le_one_iff_abs_le_one (x i)).mp
      ((Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j))
        (Finset.mem_univ i)).trans hx)
  have := hC x ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩
  simpa using this

variable {n dA dF : ℕ}

lemma continuous_Htail (hd : 1 ≤ dF) (F : CoefIdx n 1 dF → ℝ) : Continuous (Htail hd F) := by
  unfold Htail
  exact (((continuous_apply 0).comp (BstLean.Part106.continuous_bwEval F)).sub
    continuous_const).sub
      (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))

lemma continuous_psi (hd : 1 ≤ dF) (ρ : ℝ) (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ) :
    Continuous (psi hd ρ A F) := by
  unfold psi
  have h : Continuous (fun x : Fin n → ℝ => ρ⁻¹ • bwEval A x) :=
    (BstLean.Part106.continuous_bwEval A).const_smul ρ⁻¹
  exact continuous_const.mul ((continuous_Htail hd F).comp h)

lemma measurable_Htail2 (hd : 1 ≤ dF) :
    Measurable (fun p : (CoefIdx n 1 dF → ℝ) × (Fin n → ℝ) => Htail hd p.1 p.2) := by
  unfold Htail
  exact (((measurable_pi_apply 0).comp measurable_bwEval2).sub
    ((measurable_pi_apply _).comp measurable_fst)).sub
      (Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply _).comp measurable_fst).mul
          ((measurable_pi_apply i).comp measurable_snd))

lemma measurable_bwNormSq {k q d : ℕ} : Measurable (bwNormSq (k := k) (q := q) (d := d)) := by
  unfold bwNormSq bwInner
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).mul (measurable_pi_apply i)).mul measurable_const

lemma measurable_psi_rho (hd : 1 ≤ dF) :
    Measurable (fun p : ((CoefIdx n n dA → ℝ) × (CoefIdx n 1 dF → ℝ)) × (Fin n → ℝ) =>
      psi hd (Real.sqrt (bwNormSq p.1.1)) p.1.1 p.1.2 p.2) := by
  unfold psi
  have hρ : Measurable (fun p : ((CoefIdx n n dA → ℝ) × (CoefIdx n 1 dF → ℝ)) × (Fin n → ℝ) =>
      Real.sqrt (bwNormSq p.1.1)) :=
    (measurable_bwNormSq.comp (measurable_fst.comp measurable_fst)).sqrt
  have hy : Measurable (fun p : ((CoefIdx n n dA → ℝ) × (CoefIdx n 1 dF → ℝ)) × (Fin n → ℝ) =>
      (Real.sqrt (bwNormSq p.1.1))⁻¹ • bwEval p.1.1 p.2) :=
    hρ.inv.smul (measurable_bwEval_comp (measurable_fst.comp measurable_fst) measurable_snd)
  exact hρ.mul ((measurable_Htail2 hd).comp ((measurable_snd.comp measurable_fst).prodMk hy))

/-- The integrand at one evaluation point. -/
@[irreducible] noncomputable def Jf (hd : 1 ≤ dF) (c2 : ℝ) (q : (CoefIdx n n dA → ℝ) × (CoefIdx n 1 dF → ℝ))
    (x : Fin n → ℝ) : ℝ≥0∞ :=
  if 1 ≤ c2 * bwNormSq q.1 then
    ENNReal.ofReal (psi hd (Real.sqrt (bwNormSq q.1)) q.1 q.2 x ^ 2) else 0

lemma measurable_Jf (hd : 1 ≤ dF) (c2 : ℝ) :
    Measurable (fun p : ((CoefIdx n n dA → ℝ) × (CoefIdx n 1 dF → ℝ)) × (Fin n → ℝ) =>
      Jf hd c2 p.1 p.2) := by
  unfold Jf
  exact Measurable.ite
    (measurableSet_le measurable_const
      (measurable_const.mul (measurable_bwNormSq.comp (measurable_fst.comp measurable_fst))))
    ((measurable_psi_rho hd).pow_const 2).ennreal_ofReal measurable_const

lemma measurable_Jf_s {N dW : ℕ} (hd : 1 ≤ dF) (c2 : ℝ) (W : CoefIdx N n dW → ℝ) :
    Measurable (fun p : ((CoefIdx n n dA → ℝ) × (CoefIdx n 1 dF → ℝ)) × (Fin N → ℝ) =>
      Jf hd c2 p.1 (sphProj (bwEval W p.2))) := by
  have hsm : Measurable (fun u : Fin N → ℝ => sphProj (bwEval W u)) :=
    measurable_sphProj.comp (measurable_bwEval_comp measurable_const measurable_id)
  have h0 : Measurable (fun p : ((CoefIdx n n dA → ℝ) × (CoefIdx n 1 dF → ℝ)) × (Fin N → ℝ) =>
      (p.1, sphProj (bwEval W p.2))) := measurable_fst.prodMk (hsm.comp measurable_snd)
  exact (measurable_Jf hd c2).comp h0

lemma gmom_nonneg (n j : ℕ) : 0 ≤ gmom n j := by
  unfold gmom
  exact integral_nonneg fun z => pow_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) _

lemma kap_bounds (dA : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ BstLean.Part107.kap dA t ∧ BstLean.Part107.kap dA t ≤ (dA : ℝ) + 1 := by
  unfold BstLean.Part107.kap
  refine ⟨Finset.sum_nonneg fun j _ => pow_nonneg h0 _, ?_⟩
  calc ∑ j ∈ Finset.range (dA + 1), t ^ j ≤ ∑ _j ∈ Finset.range (dA + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => pow_le_one₀ h0 h1
    _ = (dA : ℝ) + 1 := by simp

/-- The mean over `(A₁, F)` of the integrand at one point of the closed unit ball. -/
lemma key_point (hH : HtailMom108) (hE : EvalMom108) (hd : 1 ≤ dF) {c2 : ℝ} (hc2 : 0 ≤ c2)
    (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 ≤ 1) :
    ∫⁻ q, Jf (dA := dA) hd c2 q x ∂((bwGauss n n dA 1).prod (bwGauss n 1 dF 1)) ≤
      ENNReal.ofReal (∑ j ∈ Finset.Icc 2 dF, c2 ^ (j - 1) * ((dA : ℝ) + 1) ^ j * gmom n j) := by
  have hJx : Measurable (fun q : (CoefIdx n n dA → ℝ) × (CoefIdx n 1 dF → ℝ) => Jf hd c2 q x) :=
    (measurable_Jf hd c2).comp (measurable_id.prodMk measurable_const)
  rw [lintegral_prod _ hJx.aemeasurable]
  have hZ : ∀ A : CoefIdx n n dA → ℝ, 0 ≤ ∑ a, bwEval A x a ^ 2 := fun A =>
    Finset.sum_nonneg fun a _ => sq_nonneg _
  have inner : ∀ A : CoefIdx n n dA → ℝ,
      ∫⁻ F, Jf hd c2 (A, F) x ∂bwGauss n 1 dF 1 ≤
        ENNReal.ofReal (∑ j ∈ Finset.Icc 2 dF, c2 ^ (j - 1) * (∑ a, bwEval A x a ^ 2) ^ j) := by
    intro A
    by_cases h : 1 ≤ c2 * bwNormSq A
    · simp only [Jf, if_pos h]
      set R := bwNormSq A with hR
      have hRpos : 0 < R := by
        by_contra hneg
        have : c2 * R ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc2 (not_lt.mp hneg)
        linarith
      set ρ := Real.sqrt R with hρ
      have hρ2 : ρ ^ 2 = R := Real.sq_sqrt hRpos.le
      set y : Fin n → ℝ := ρ⁻¹ • bwEval A x with hy
      have e : ∀ F : CoefIdx n 1 dF → ℝ, ENNReal.ofReal (psi hd ρ A F x ^ 2) =
          ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal (Htail hd F y ^ 2) := by
        intro F
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        unfold psi
        ring
      simp_rw [e]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hH n dF hd y,
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
      have hdot : dot y y = R⁻¹ * ∑ a, bwEval A x a ^ 2 := by
        rw [← hρ2, ← inv_pow, Finset.mul_sum]
        unfold dot
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [hy, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hρ2, hdot]
      set Z := ∑ a, bwEval A x a ^ 2 with hZdef
      have hinv : R⁻¹ ≤ c2 := (inv_le_iff_one_le_mul₀ hRpos).mpr h
      have hRR : R * R⁻¹ = 1 := mul_inv_cancel₀ hRpos.ne'
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      calc R * (R⁻¹ * Z) ^ (m + 1) = R⁻¹ ^ m * Z ^ (m + 1) * (R * R⁻¹) := by ring
        _ = R⁻¹ ^ m * Z ^ (m + 1) := by rw [hRR, mul_one]
        _ ≤ c2 ^ m * Z ^ (m + 1) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_nonneg.2 hRpos.le) hinv _)
              (pow_nonneg (hZ A) _)
    · simp only [Jf, if_neg h]
      simp
  refine le_trans (lintegral_mono inner) ?_
  have e : ∀ A : CoefIdx n n dA → ℝ,
      ENNReal.ofReal (∑ j ∈ Finset.Icc 2 dF, c2 ^ (j - 1) * (∑ a, bwEval A x a ^ 2) ^ j) =
        ∑ j ∈ Finset.Icc 2 dF,
          ENNReal.ofReal (c2 ^ (j - 1)) * ENNReal.ofReal ((∑ a, bwEval A x a ^ 2) ^ j) := by
    intro A
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ =>
      mul_nonneg (pow_nonneg hc2 _) (pow_nonneg (hZ A) _)]
    exact Finset.sum_congr rfl fun j _ => ENNReal.ofReal_mul (pow_nonneg hc2 _)
  simp_rw [e]
  rw [lintegral_finsetSum _ fun j _ =>
    (((Finset.measurable_sum _ fun a _ =>
      (measurable_bwEval x a).pow_const 2).pow_const j).ennreal_ofReal).const_mul _]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hE n dA x]
  have ht0 : 0 ≤ dot x x := by
    rw [dot_self_eq]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have ht1 : dot x x ≤ 1 := by rw [dot_self_eq]; exact hx
  obtain ⟨hk0, hk1⟩ := kap_bounds dA ht0 ht1
  rw [ENNReal.ofReal_sum_of_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (pow_nonneg hc2 _) (by positivity)) (gmom_nonneg n j)]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← ENNReal.ofReal_mul (pow_nonneg hc2 _)]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hk0 hk1 j) (gmom_nonneg n j))
    (pow_nonneg hc2 _)

/-- **The perturbation bound.** -/
theorem pertBound108 (hH : HtailMom108) (hE : EvalMom108) (_hG : GMom108) : PertBound108 := by
  intro N n dW dA dF k hd hN hk W τ ω c2 hc2
  have := BstLean.Part29.uniformSphere_isProbability N hN
  set S : ℝ := ∑ j ∈ Finset.Icc 2 dF, c2 ^ (j - 1) * ((dA : ℝ) + 1) ^ j * gmom n j with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (pow_nonneg hc2 _) (by positivity)) (gmom_nonneg n j)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set s : (Fin N → ℝ) → Fin n → ℝ := fun u => sphProj (bwEval W u) with hs
  have hsm : Measurable s := measurable_sphProj.comp (measurable_bwEval_comp measurable_const
    measurable_id)
  set xs : Fin k → Fin n → ℝ := fun i => BstLean.Part106.standIn W τ (ω i) with hxs
  have hxs1 : ∀ i, ∑ a, xs i a ^ 2 ≤ 1 := fun i => BstLean.Part106.sphProj_sq_le _
  have hs1 : ∀ u, ∑ a, s u a ^ 2 ≤ 1 := fun u => BstLean.Part106.sphProj_sq_le _
  have hJm := measurable_Jf (n := n) (dA := dA) hd c2
  have hJx : ∀ x : Fin n → ℝ,
      Measurable (fun q : (CoefIdx n n dA → ℝ) × (CoefIdx n 1 dF → ℝ) => Jf hd c2 q x) :=
    fun x => hJm.comp (measurable_id.prodMk measurable_const)
  -- the pointwise bound
  have hpt : ∀ q : (CoefIdx n n dA → ℝ) × (CoefIdx n 1 dF → ℝ),
      (if 1 ≤ c2 * bwNormSq q.1 then
          ENNReal.ofReal
            ((|Err W τ (psi hd (Real.sqrt (bwNormSq q.1)) q.1 q.2) ω| +
              1 / 2 * Real.sqrt (Vu W (psi hd (Real.sqrt (bwNormSq q.1)) q.1 q.2))) ^ 2)
        else 0) ≤
        ENNReal.ofReal (4 / (k : ℝ)) * ∑ i, Jf hd c2 q (xs i) +
          ENNReal.ofReal (9 / 2) * ∫⁻ u, Jf hd c2 q (s u) ∂uniformSphere N := by
    intro q
    by_cases h : 1 ≤ c2 * bwNormSq q.1
    · simp only [Jf, if_pos h]
      set ψ := psi hd (Real.sqrt (bwNormSq q.1)) q.1 q.2 with hψ
      obtain ⟨M, hM⟩ := cont_bdd_ball ψ (continuous_psi hd _ _ _)
      have hψm : Measurable ψ := (continuous_psi hd _ _ _).measurable
      obtain ⟨hf2, hineq⟩ := pert_abs (uniformSphere N) (f := fun u => ψ (s u)) (hψm.comp hsm)
        (fun u => hM _ (hs1 u)) hk (fun i => ψ (xs i))
      have e1 : ENNReal.ofReal (4 * ((∑ i, ψ (xs i) ^ 2) / (k : ℝ))) =
          ENNReal.ofReal (4 / (k : ℝ)) * ∑ i, ENNReal.ofReal (ψ (xs i) ^ 2) := by
        rw [show 4 * ((∑ i, ψ (xs i) ^ 2) / (k : ℝ)) = 4 / (k : ℝ) * ∑ i, ψ (xs i) ^ 2 by ring,
          ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
      have e2 : ENNReal.ofReal (9 / 2 * ∫ u, ψ (s u) ^ 2 ∂uniformSphere N) =
          ENNReal.ofReal (9 / 2) * ∫⁻ u, ENNReal.ofReal (ψ (s u) ^ 2) ∂uniformSphere N := by
        rw [ENNReal.ofReal_mul (by norm_num),
          ofReal_integral_eq_lintegral_ofReal hf2
            (Filter.Eventually.of_forall fun u => sq_nonneg _)]
      rw [← e1, ← e2, ← ENNReal.ofReal_add
        (mul_nonneg (by norm_num) (div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) hk0.le))
        (mul_nonneg (by norm_num) (integral_nonneg fun u => sq_nonneg _))]
      apply ENNReal.ofReal_le_ofReal
      exact hineq
    · rw [if_neg h]
      exact bot_le
  refine le_trans (lintegral_mono hpt) ?_
  have hsw := measurable_Jf_s (dA := dA) hd c2 W
  rw [lintegral_add_left ((Finset.measurable_sum _ fun i _ => hJx (xs i)).const_mul _),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finsetSum _ fun i _ => hJx (xs i),
    lintegral_lintegral_swap (f := fun q u => Jf hd c2 q (s u)) hsw.aemeasurable]
  have h1 : ∑ i, ∫⁻ q, Jf hd c2 q (xs i) ∂((bwGauss n n dA 1).prod (bwGauss n 1 dF 1)) ≤
      ∑ _i : Fin k, ENNReal.ofReal S :=
    Finset.sum_le_sum fun i _ => key_point hH hE hd hc2 (xs i) (hxs1 i)
  have h2 : ∫⁻ u, ∫⁻ q, Jf hd c2 q (s u) ∂((bwGauss n n dA 1).prod (bwGauss n 1 dF 1))
      ∂uniformSphere N ≤ ∫⁻ _u, ENNReal.ofReal S ∂uniformSphere N :=
    lintegral_mono fun u => key_point hH hE hd hc2 (s u) (hs1 u)
  refine le_trans (add_le_add (mul_le_mul_right h1 _) (mul_le_mul_right h2 _)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, lintegral_const,
    measure_univ, mul_one, ← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_mul hk0.le,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  apply le_of_eq
  field_simp
  ring

end BstLean.Part108

#print axioms BstLean.Part108.pertBound108
