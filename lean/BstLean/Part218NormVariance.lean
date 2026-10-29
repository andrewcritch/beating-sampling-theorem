import BstLean.Part218NormKernel

/-! Exact degeneracy of the ordered input norm kernel removes the cubic row-count term. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part105 BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part137

lemma normKernel_measurable {N : ℕ} (hN : 1 ≤ N) : Measurable (normKernel N) := by
  have := uniformSphere_isProbability N hN
  have hc : Continuous (fun p : ((Fin N → ℝ) × (Fin N → ℝ)) × (Fin N → ℝ) =>
      relu (dotp p.1.1 p.2) ^ 2 * relu (dotp p.1.2 p.2) ^ 2) := by
    unfold relu dotp
    fun_prop
  exact hc.measurable.stronglyMeasurable.integral_prod_right'.measurable.sub (by
    unfold normSq; fun_prop)

lemma normKernel_symm (N : ℕ) (x y : Fin N → ℝ) :
    normKernel N (x, y) = normKernel N (y, x) := by
  unfold normKernel
  simp only [mul_comm]

lemma normKernel_abs_le {N : ℕ} (hN : 1 ≤ N) (x y : Fin N → ℝ) :
    |normKernel N (x, y)| ≤ (1 + 1 / (4 * (N : ℝ) ^ 2)) * normSq x * normSq y := by
  have := uniformSphere_isProbability N hN
  have hc : Continuous (fun u : Fin N → ℝ => relu (dotp x u) ^ 2 * relu (dotp y u) ^ 2) := by
    unfold relu dotp; fun_prop
  have hb : ∀ z u : Fin N → ℝ, normSq u = 1 → relu (dotp z u) ^ 2 ≤ normSq z := by
    intro z u hu
    have hd : dotp z u ^ 2 ≤ normSq z * normSq u := by
      have h := pow_le_pow_left₀ (abs_nonneg _) (abs_dotp_le_nrm z u) 2
      simpa only [sq_abs, mul_pow, nrm_sq] using h
    rw [hu, mul_one] at hd
    exact (relu_sq_le _).trans hd
  have hu : (∫ u, relu (dotp x u) ^ 2 * relu (dotp y u) ^ 2 ∂uniformSphere N) ≤
      normSq x * normSq y := by
    calc
      _ ≤ ∫ _u, normSq x * normSq y ∂uniformSphere N := by
        apply integral_mono_ae (sphere_cont_integrable hN hc) (integrable_const _)
        filter_upwards [uniformSphere_ae_sphere N] with u hu
        exact mul_le_mul (hb x u hu) (hb y u hu) (sq_nonneg _) (normSq_nonneg _)
      _ = _ := by simp
  have hl : 0 ≤ ∫ u, relu (dotp x u) ^ 2 * relu (dotp y u) ^ 2 ∂uniformSphere N :=
    integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  unfold normKernel
  dsimp only [Prod.fst, Prod.snd]
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg hl, abs_of_nonneg (div_nonneg
    (mul_nonneg (normSq_nonneg x) (normSq_nonneg y)) (by positivity))]
  calc
    _ ≤ normSq x * normSq y + normSq x * normSq y / (4 * (N : ℝ) ^ 2) := add_le_add hu le_rfl
    _ = _ := by ring

lemma normKernel_memLp {N : ℕ} (hN : 1 ≤ N) :
    MemLp (normKernel N) 2 ((stdGauss (Fin N)).prod (stdGauss (Fin N))) := by
  apply (memLp_two_iff_integrable_sq (normKernel_measurable hN).aestronglyMeasurable).mpr
  have hi := ((gauss_normSq_sq N).1.mul_prod (gauss_normSq_sq N).1).const_mul
    ((1 + 1 / (4 * (N : ℝ) ^ 2)) ^ 2)
  apply hi.mono' ((normKernel_measurable hN).pow_const 2).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := pow_le_pow_left₀ (abs_nonneg _) (normKernel_abs_le hN p.1 p.2) 2
  simpa only [sq_abs, mul_pow, mul_assoc] using h

theorem normKernel_mean_zero {N : ℕ} (hN : 1 ≤ N) :
    (∫ p, normKernel N p ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) = 0 := by
  rw [integral_prod _ ((normKernel_memLp hN).integrable one_le_two)]
  simp_rw [(normKernel_conditional_zero hN _).2]
  simp

theorem normKernel_shared_zero {N : ℕ} (hN : 1 ≤ N) :
    (∫ p : (Fin N → ℝ) × ((Fin N → ℝ) × (Fin N → ℝ)),
      normKernel N (p.1, p.2.1) * normKernel N (p.1, p.2.2)
      ∂(stdGauss (Fin N)).prod ((stdGauss (Fin N)).prod (stdGauss (Fin N)))) = 0 := by
  let K : ℝ := 1 + 1 / (4 * (N : ℝ) ^ 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hm : Measurable (fun p : (Fin N → ℝ) × ((Fin N → ℝ) × (Fin N → ℝ)) =>
      normKernel N (p.1, p.2.1) * normKernel N (p.1, p.2.2)) := by
    exact ((normKernel_measurable hN).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      ((normKernel_measurable hN).comp
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hi : Integrable (fun p : (Fin N → ℝ) × ((Fin N → ℝ) × (Fin N → ℝ)) =>
      normKernel N (p.1, p.2.1) * normKernel N (p.1, p.2.2))
      ((stdGauss (Fin N)).prod ((stdGauss (Fin N)).prod (stdGauss (Fin N)))) := by
    have hb := ((gauss_normSq_sq N).1.mul_prod
      ((gauss_normSq N).1.mul_prod (gauss_normSq N).1)).const_mul (K ^ 2)
    apply hb.mono' hm.aestronglyMeasurable
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ (K * normSq p.1 * normSq p.2.1) * (K * normSq p.1 * normSq p.2.2) :=
        mul_le_mul (normKernel_abs_le hN _ _) (normKernel_abs_le hN _ _)
          (abs_nonneg _) (mul_nonneg (mul_nonneg hK (normSq_nonneg _)) (normSq_nonneg _))
      _ = _ := by ring
  rw [integral_prod _ hi]
  have he : ∀ x : Fin N → ℝ,
      (∫ p : (Fin N → ℝ) × (Fin N → ℝ), normKernel N (x, p.1) * normKernel N (x, p.2)
        ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) = 0 := by
    intro x
    rw [integral_prod_mul (fun y : Fin N → ℝ => normKernel N (x, y))
      (fun z : Fin N → ℝ => normKernel N (x, z)), (normKernel_conditional_zero hN x).2, zero_mul]
  simp_rw [he]
  simp

/-- The actual ordered kernel has only the quadratic row-count contribution. -/
theorem normKernel_ordered_variance {N m : ℕ} (hN : 1 ≤ N) :
    Var[fun x : Fin m → Fin N → ℝ => ∑ p : Fin m × Fin m, orderedRow (normKernel N) p x;
      Measure.pi fun _ : Fin m => stdGauss (Fin N)] =
      2 * (m : ℝ) * ((m : ℝ) - 1) *
        (∫ p, normKernel N p ^ 2 ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) := by
  have h₂ : (∫ p, normKernel N p ^ 2 ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) -
      (∫ p, normKernel N p ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) ^ 2 =
      ∫ p, normKernel N p ^ 2 ∂(stdGauss (Fin N)).prod (stdGauss (Fin N)) := by
    rw [normKernel_mean_zero hN]; ring
  have h₁ : (∫ p : (Fin N → ℝ) × ((Fin N → ℝ) × (Fin N → ℝ)),
      normKernel N (p.1, p.2.1) * normKernel N (p.1, p.2.2)
      ∂(stdGauss (Fin N)).prod ((stdGauss (Fin N)).prod (stdGauss (Fin N)))) -
      (∫ p, normKernel N p ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) ^ 2 = 0 := by
    rw [normKernel_shared_zero hN, normKernel_mean_zero hN]; ring
  have h := iid_ordered_pair_variance (m := m) (stdGauss (Fin N))
    (normKernel_measurable hN) (normKernel_memLp hN) (normKernel_symm N) h₂ h₁
  simpa only [mul_zero, zero_add] using h

end BstLean.Part218
#print axioms BstLean.Part218.normKernel_shared_zero
#print axioms BstLean.Part218.normKernel_ordered_variance
