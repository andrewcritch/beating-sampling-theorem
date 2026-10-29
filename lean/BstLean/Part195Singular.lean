import BstLean.Part165Poin
import BstLean.Part195Rotation
import BstLean.Part153Inv

/-! The even rotation inequality for normalized inputs.
The cutoff error uses an inverse-radius moment at the gradient order. -/
namespace BstLean.Part195
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq sphPt normSq_nonneg normSq_sphPt measurable_sphPt)
open BstLean.Part148 (EuLip)
open BstLean.Part153 (cut cutF_lip cut_eq_sphPt cut_normSq_le cont_ns epsSeq epsSeq_pos
  epsSeq_tendsto)
open BstLean.Part162 (gmom gmom_nonneg poincare_p)

/-- The singular inequality uses the actual coordinate derivative. -/
theorem rotation_singular_even {n q : ℕ} (hq : 1 ≤ q)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {Φ : (Fin n → ℝ) → ℝ} {K : ℝ}
    (hK0 : 0 ≤ K) (hΦ : EuLip Φ K) {Γ : (Fin n → ℝ) → ℝ}
    (hΓ0 : ∀ ξ, 0 ≤ Γ ξ)
    (hΓ : Integrable (fun ξ => Γ ξ ^ q) (stdGauss (Fin n)))
    (hgrad : ∀ᵐ ξ ∂stdGauss (Fin n),
      ∑ i, (fderiv ℝ (fun ξ => Φ (sphPt (c + τ • ξ))) ξ (Pi.single i 1)) ^ 2 ≤ Γ ξ)
    (hinv : Integrable (fun ξ : Fin n → ℝ => (normSq (c + τ • ξ))⁻¹ ^ q)
      (stdGauss (Fin n)))
    (hne : ∀ᵐ ξ ∂stdGauss (Fin n), normSq (c + τ • ξ) ≠ 0) :
    ∫ ξ, |Φ (sphPt (c + τ • ξ)) - ∫ ξ', Φ (sphPt (c + τ • ξ'))
      ∂stdGauss (Fin n)| ^ (2 * q) ∂stdGauss (Fin n) ≤
      rotationConstant q ^ (2 * q) * (∫ ξ, Γ ξ ^ q ∂stdGauss (Fin n)) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn : 1 ≤ n := by
    by_contra hcon
    have h0 : n = 0 := by omega
    subst h0
    have hF : ∀ᵐ ξ ∂stdGauss (Fin 0), False := by
      filter_upwards [hne] with ξ h
      exact h (by simp [normSq])
    rw [eventually_false_iff_eq_bot, ae_eq_bot] at hF
    exact IsProbabilityMeasure.ne_zero _ hF
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = |Φ 0| + K := ⟨_, rfl⟩
  have hΦb : ∀ x : Fin n → ℝ, normSq x ≤ 1 → |Φ x| ≤ C := by
    intro x hx
    have h := hΦ x 0
    simp only [Pi.zero_apply, sub_zero] at h
    have h1 : √(∑ i, x i ^ 2) ≤ 1 := Real.sqrt_le_one.mpr hx
    have h2 : K * √(∑ i, x i ^ 2) ≤ K * 1 := mul_le_mul_of_nonneg_left h1 hK0
    have h3 := abs_sub_abs_le_abs_sub (Φ x) (Φ 0)
    rw [hC]; linarith
  have hfb : ∀ ξ : Fin n → ℝ, |Φ (sphPt (c + τ • ξ))| ≤ C := fun ξ =>
    hΦb _ (normSq_sphPt hn _).le
  have hFb : ∀ ε : ℝ, 0 < ε → ∀ ξ : Fin n → ℝ, |Φ (cut ε (c + τ • ξ))| ≤ C := fun ε hε ξ =>
    hΦb _ (cut_normSq_le hε _)
  have hFm : ∀ ε : ℝ, 0 < ε → Measurable (fun ξ : Fin n → ℝ => Φ (cut ε (c + τ • ξ))) :=
    fun ε hε => ((cutF_lip c hτ hε hK0 hΦ).continuous (by positivity)).measurable
  have hfm : Measurable (fun ξ : Fin n → ℝ => Φ (sphPt (c + τ • ξ))) :=
    (hΦ.continuous hK0).measurable.comp
      (measurable_sphPt.comp (measurable_const.add (measurable_id.const_smul τ)))
  have hpw : ∀ a b : ℝ, |a| ≤ C → |b| ≤ C → ‖|a - b| ^ (2 * q)‖ ≤ (2 * C) ^ (2 * q) := by
    intro a b ha hb
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ (2 * q)
    have h1 := abs_le.mp ha
    have h2 := abs_le.mp hb
    rw [abs_le]; constructor <;> linarith
  have hmb : ∀ g : (Fin n → ℝ) → ℝ, (∀ ξ, |g ξ| ≤ C) → |∫ ξ, g ξ ∂stdGauss (Fin n)| ≤ C := by
    intro g hg
    have h := norm_integral_le_of_norm_le_const (μ := stdGauss (Fin n)) (f := g) (C := C)
      (Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact hg ξ)
    simpa using h
  -- pointwise convergence
  have hpt : ∀ ξ : Fin n → ℝ, normSq (c + τ • ξ) ≠ 0 →
      ∀ᶠ j in atTop, Φ (cut (epsSeq j) (c + τ • ξ)) = Φ (sphPt (c + τ • ξ)) := by
    intro ξ hz
    have hs : 0 < √(normSq (c + τ • ξ)) :=
      Real.sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hz))
    filter_upwards [epsSeq_tendsto.eventually (gt_mem_nhds hs)] with j hj
    rw [cut_eq_sphPt (epsSeq_pos j) hj.le]
  have hptT : ∀ᵐ ξ ∂stdGauss (Fin n), Tendsto (fun j => Φ (cut (epsSeq j) (c + τ • ξ))) atTop
      (𝓝 (Φ (sphPt (c + τ • ξ)))) := by
    filter_upwards [hne] with ξ hz
    exact Tendsto.congr' ((hpt ξ hz).mono fun j h => h.symm) tendsto_const_nhds
  have hm : Tendsto (fun j => ∫ ξ, Φ (cut (epsSeq j) (c + τ • ξ)) ∂stdGauss (Fin n)) atTop
      (𝓝 (∫ ξ, Φ (sphPt (c + τ • ξ)) ∂stdGauss (Fin n))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun j => (hFm _ (epsSeq_pos j)).aestronglyMeasurable) (integrable_const C)
      (fun j => Eventually.of_forall fun ξ => ?_) hptT
    rw [Real.norm_eq_abs]
    exact hFb _ (epsSeq_pos j) ξ
  have hV : Tendsto (fun j => ∫ ξ, |Φ (cut (epsSeq j) (c + τ • ξ)) -
        ∫ ξ', Φ (cut (epsSeq j) (c + τ • ξ')) ∂stdGauss (Fin n)| ^ (2 * q) ∂stdGauss (Fin n)) atTop
      (𝓝 (∫ ξ, |Φ (sphPt (c + τ • ξ)) -
        ∫ ξ', Φ (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)| ^ (2 * q) ∂stdGauss (Fin n))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (2 * C) ^ (2 * q))
      (fun j => (((hFm _ (epsSeq_pos j)).sub measurable_const).abs.pow_const (2 * q)).aestronglyMeasurable)
      (integrable_const _) (fun j => Eventually.of_forall fun ξ => ?_) ?_
    · exact hpw _ _ (hFb _ (epsSeq_pos j) ξ) (hmb _ (hFb _ (epsSeq_pos j)))
    · filter_upwards [hptT] with ξ hξ
      exact ((hξ.sub hm).abs).pow (2 * q)
  let E : ℕ → (Fin n → ℝ) → ℝ := fun j ξ =>
    if normSq (c + τ • ξ) ≤ epsSeq j ^ 2 then
      (K * τ) ^ (2 * q) * (normSq (c + τ • ξ))⁻¹ ^ q else 0
  have hEi : ∀ j, Integrable (E j) (stdGauss (Fin n)) := by
    intro j
    exact (hinv.const_mul _).indicator
      (measurableSet_le (cont_ns c τ).measurable measurable_const)
  have hEt : Tendsto (fun j => ∫ ξ, E j ξ ∂stdGauss (Fin n)) atTop (𝓝 0) := by
    have ht : Tendsto (fun j => ∫ ξ, E j ξ ∂stdGauss (Fin n)) atTop
        (𝓝 (∫ _ξ : Fin n → ℝ, (0 : ℝ) ∂stdGauss (Fin n))) := by
      refine tendsto_integral_of_dominated_convergence
        (fun ξ => (K * τ) ^ (2 * q) * (normSq (c + τ • ξ))⁻¹ ^ q)
        (fun j => (hEi j).aestronglyMeasurable) (hinv.const_mul _) ?_ ?_
      · intro j
        exact ae_of_all _ fun ξ => by
          have hd : 0 ≤ (K * τ) ^ (2 * q) * (normSq (c + τ • ξ))⁻¹ ^ q :=
            mul_nonneg (by positivity)
              (pow_nonneg (inv_nonneg.mpr (normSq_nonneg _)) q)
          dsimp [E]
          split_ifs
          · rw [abs_of_nonneg hd]
          · simpa using hd
      · filter_upwards [hne] with ξ hz
        have hs : 0 < normSq (c + τ • ξ) :=
          lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hz)
        have he : ∀ᶠ j in atTop, E j ξ = 0 := by
          have ht : Tendsto (fun j => epsSeq j ^ 2) atTop (𝓝 (0 : ℝ)) := by
            simpa using epsSeq_tendsto.pow 2
          filter_upwards [ht.eventually (gt_mem_nhds hs)] with j hj
          simp [E, not_le.mpr hj]
        exact tendsto_const_nhds.congr' (he.mono fun j hj => hj.symm)
    simpa using ht
  have hcut : ∀ j,
      ∫ ξ, |Φ (cut (epsSeq j) (c + τ • ξ)) -
        ∫ ξ', Φ (cut (epsSeq j) (c + τ • ξ')) ∂stdGauss (Fin n)| ^ (2 * q)
          ∂stdGauss (Fin n) ≤
      rotationConstant q ^ (2 * q) * (
        (∫ ξ, Γ ξ ^ q ∂stdGauss (Fin n) + ∫ ξ, E j ξ ∂stdGauss (Fin n))) := by
    intro j
    have he := epsSeq_pos j
    have hL0 : 0 ≤ K * τ / epsSeq j := by positivity
    have hP := rotation_even hL0 (cutF_lip c hτ he hK0 hΦ) hq
    have hsq : (fun ξ => √(BstLean.Part151.gradSq
        (fun ξ => Φ (cut (epsSeq j) (c + τ • ξ))) ξ) ^ (2 * q)) =
        (fun ξ => BstLean.Part151.gradSq
          (fun ξ => Φ (cut (epsSeq j) (c + τ • ξ))) ξ ^ q) := by
      funext ξ
      rw [pow_mul, Real.sq_sqrt (BstLean.Part151.gradSq_nonneg _ _)]
    rw [← hsq] at hP
    refine hP.trans ?_
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (rotationConstant_nonneg q) _)
    rw [← integral_add hΓ (hEi j)]
    have hi : Integrable (fun ξ => √(BstLean.Part151.gradSq
        (fun ξ => Φ (cut (epsSeq j) (c + τ • ξ))) ξ) ^ (2 * q))
        (stdGauss (Fin n)) := by
      refine Integrable.of_bound
        (((BstLean.Part151.measurable_gradSq _).sqrt.pow_const _).aestronglyMeasurable)
        ((K * τ / epsSeq j) ^ (2 * q)) (ae_of_all _ fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply pow_le_pow_left₀ (Real.sqrt_nonneg _)
      rw [← Real.sqrt_sq hL0]
      exact Real.sqrt_le_sqrt (BstLean.Part151.gradSq_le hL0
        (cutF_lip c hτ he hK0 hΦ) ξ)
    refine integral_mono_ae hi (hΓ.add (hEi j)) ?_
    filter_upwards [hgrad, hne] with ξ hg hz
    by_cases hc : epsSeq j ^ 2 < normSq (c + τ • ξ)
    · have heq : (fun ξ => Φ (cut (epsSeq j) (c + τ • ξ))) =ᶠ[𝓝 ξ]
          (fun ξ => Φ (sphPt (c + τ • ξ))) := by
        filter_upwards [(isOpen_lt continuous_const (cont_ns c τ)).mem_nhds hc] with ξ' h'
        rw [cut_eq_sphPt he ((Real.le_sqrt' he).mpr h'.le)]
      have hb : BstLean.Part151.gradSq (fun ξ => Φ (cut (epsSeq j) (c + τ • ξ))) ξ ≤ Γ ξ := by
        unfold BstLean.Part151.gradSq
        rw [heq.fderiv_eq]
        exact hg
      simp only [E, if_neg (not_le.mpr hc), add_zero]
      rw [pow_mul, Real.sq_sqrt (BstLean.Part151.gradSq_nonneg _ _)]
      exact pow_le_pow_left₀ (BstLean.Part151.gradSq_nonneg _ _) hb q
    · have hs : 0 < normSq (c + τ • ξ) :=
        lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hz)
      have hb : (epsSeq j ^ 2)⁻¹ ≤ (normSq (c + τ • ξ))⁻¹ :=
        inv_anti₀ hs (not_lt.mp hc)
      have hh : (K * τ / epsSeq j) ^ (2 * q) ≤
          (K * τ) ^ (2 * q) * (normSq (c + τ • ξ))⁻¹ ^ q := by
        rw [div_pow, pow_mul (epsSeq j), div_eq_mul_inv, ← inv_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hb q) (by positivity)
      have hgs := BstLean.Part151.gradSq_le hL0 (cutF_lip c hτ he hK0 hΦ) ξ
      have hh' : √(BstLean.Part151.gradSq (fun ξ => Φ (cut (epsSeq j) (c + τ • ξ))) ξ)
          ^ (2 * q) ≤ (K * τ / epsSeq j) ^ (2 * q) := by
        apply pow_le_pow_left₀ (Real.sqrt_nonneg _)
        rw [← Real.sqrt_sq hL0]
        exact Real.sqrt_le_sqrt hgs
      simp only [E, if_pos (not_lt.mp hc)]
      exact hh'.trans (hh.trans (le_add_of_nonneg_left (pow_nonneg (hΓ0 ξ) q)))
  have hB := ((tendsto_const_nhds (x := ∫ ξ, Γ ξ ^ q ∂stdGauss (Fin n))).add hEt)
    |>.const_mul (rotationConstant q ^ (2 * q))
  simp only [add_zero] at hB
  exact le_of_tendsto_of_tendsto' hV hB hcut

/-- The dimension guard supplies the inverse moment and the nonzero event.
The guard comes from the existing shifted Gaussian inverse-moment theorem. -/
theorem rotation_singular_dimension {n q : ℕ} (hq : 1 ≤ q) (hn : 2 * q + 1 < n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {Φ : (Fin n → ℝ) → ℝ} {K : ℝ}
    (hK0 : 0 ≤ K) (hΦ : EuLip Φ K) {Γ : (Fin n → ℝ) → ℝ}
    (hΓ0 : ∀ ξ, 0 ≤ Γ ξ)
    (hΓ : Integrable (fun ξ => Γ ξ ^ q) (stdGauss (Fin n)))
    (hgrad : ∀ᵐ ξ ∂stdGauss (Fin n),
      ∑ i, (fderiv ℝ (fun ξ => Φ (sphPt (c + τ • ξ))) ξ (Pi.single i 1)) ^ 2 ≤ Γ ξ) :
    ∫ ξ, |Φ (sphPt (c + τ • ξ)) - ∫ ξ', Φ (sphPt (c + τ • ξ'))
      ∂stdGauss (Fin n)| ^ (2 * q) ∂stdGauss (Fin n) ≤
      rotationConstant q ^ (2 * q) * (∫ ξ, Γ ξ ^ q ∂stdGauss (Fin n)) :=
  rotation_singular_even hq c hτ hK0 hΦ hΓ0 hΓ hgrad
    (BstLean.Part153.invMoment_le hn c hτ).1
    (BstLean.Part153.ae_normSq_ne (by omega) c hτ.ne')

/-- The norm form retains the paper constant at every even order. -/
theorem rotation_singular_norm {n q : ℕ} (hq : 1 ≤ q) (hn : 2 * q + 1 < n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {Φ : (Fin n → ℝ) → ℝ} {K : ℝ}
    (hK0 : 0 ≤ K) (hΦ : EuLip Φ K) {Γ : (Fin n → ℝ) → ℝ}
    (hΓ0 : ∀ ξ, 0 ≤ Γ ξ)
    (hΓ : Integrable (fun ξ => Γ ξ ^ q) (stdGauss (Fin n)))
    (hgrad : ∀ᵐ ξ ∂stdGauss (Fin n),
      ∑ i, (fderiv ℝ (fun ξ => Φ (sphPt (c + τ • ξ))) ξ (Pi.single i 1)) ^ 2 ≤ Γ ξ) :
    BstLean.Part161.momN (stdGauss (Fin n)) (2 * q)
      (fun ξ => Φ (sphPt (c + τ • ξ)) - ∫ ξ', Φ (sphPt (c + τ • ξ'))
        ∂stdGauss (Fin n)) ≤
      rotationConstant q * BstLean.Part161.momN (stdGauss (Fin n)) (2 * q)
        (fun ξ => √(Γ ξ)) := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0)
    (mul_nonneg (rotationConstant_nonneg q) (BstLean.Part161.momN_nonneg _ _ _))
  rw [mul_pow, BstLean.Part161.momN_pow _ (by omega),
    BstLean.Part161.momN_pow _ (by omega)]
  simp only [abs_of_nonneg (Real.sqrt_nonneg _), pow_mul, Real.sq_sqrt (hΓ0 _)]
  simpa only [pow_mul] using rotation_singular_dimension hq hn c hτ hK0 hΦ hΓ0 hΓ hgrad

end BstLean.Part195
#print axioms BstLean.Part195.rotation_singular_even
#print axioms BstLean.Part195.rotation_singular_dimension
#print axioms BstLean.Part195.rotation_singular_norm
