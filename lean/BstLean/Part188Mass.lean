import BstLean.Part188Network
import BstLean.Part165Poin

/-! The energy and directional interfaces give the mass of the corrected WF good set. -/

namespace BstLean.Part188

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part152
open BstLean.Part153 (nrm nrm_nonneg nrm_sq abs_dot_le_nrm nrm_hid2_sub_le)

variable {n : ℕ}

noncomputable def centrePhi (D : Design n) (c : Ret n) (z : Fin n → ℝ) : ℝ :=
  (∑ j, hid2 c.2.1.1.1 c.2.1.1.2 z j * D.bA c.1 c.2.1.1 j) /
    (√(n : ℝ) * nrm (D.bA c.1 c.2.1.1))

lemma centrePhi_eq (D : Design n) (c : Ret n) :
    (fun ξ => centrePhi D c (sphPt (c.1.2 + D.tau0 c • ξ))) = centreCoordinate D c := rfl

lemma centrePhi_lip (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    (hb : 0 < normSq (D.bA c.1 c.2.1.1)) :
    ∃ K : ℝ, 0 ≤ K ∧ BstLean.Part148.EuLip (centrePhi D c) K := by
  set b := D.bA c.1 c.2.1.1
  set T := √(n : ℝ) * nrm b
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hT : 0 < T := mul_pos (Real.sqrt_pos.mpr hnR) (Real.sqrt_pos.mpr hb)
  set K := nrm b * (opN c.2.1.1.2 * opN c.2.1.1.1) / T
  have hO1 := opN_nonneg c.2.1.1.1
  have hO2 := opN_nonneg c.2.1.1.2
  have hbN := nrm_nonneg b
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro z z'
  have he : centrePhi D c z - centrePhi D c z' =
      (b ⬝ᵥ (hid2 c.2.1.1.1 c.2.1.1.2 z - hid2 c.2.1.1.1 c.2.1.1.2 z')) / T := by
    unfold centrePhi
    rw [div_sub_div_same]
    congr 1
    simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
  rw [he, abs_div, abs_of_pos hT]
  have hdot := (abs_dot_le_nrm b _).trans
    (mul_le_mul_of_nonneg_left (nrm_hid2_sub_le c.2.1.1.1 c.2.1.1.2 z z') (nrm_nonneg b))
  have he2 : K * √(∑ j, (z j - z' j) ^ 2) =
      (nrm b * (opN c.2.1.1.2 * opN c.2.1.1.1) * nrm (z - z')) / T := by
    change K * nrm (z - z') = _
    dsimp [K]
    ring
  rw [he2]
  exact div_le_div_of_nonneg_right (by simpa only [mul_assoc] using hdot) hT.le

/-- A supplied directional gradient moment controls the centred scalar coordinate.
The rotation constant is retained; this statement does not supply the sharp M_dir event. -/
theorem centreCoordinate_moment24 (hn : 50 ≤ n) (D : Design n) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hb : 0 < normSq (D.bA c.1 c.2.1.1)) {M : ℝ}
    (hM : DirectionMoment D c M) :
    Integrable (fun ξ => |centreCoordinate D c ξ -
      ∫ ζ, centreCoordinate D c ζ ∂stdGauss (Fin n)| ^ 24) (stdGauss (Fin n)) ∧
    ∫ ξ, |centreCoordinate D c ξ - ∫ ζ, centreCoordinate D c ζ ∂stdGauss (Fin n)| ^ 24
      ∂stdGauss (Fin n) ≤ (π / 2) ^ 24 * BstLean.Part162.gmom 24 * (M / n) ^ 12 := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hgmom := BstLean.Part162.gmom_nonneg 24
  obtain ⟨K, hK, hPhi⟩ := centrePhi_lip (by omega) D c hb
  set f := centreCoordinate D c
  set Γ := fun ξ => BstLean.Part151.gradSq f ξ
  have hΓ0 : ∀ ξ, 0 ≤ Γ ξ := fun ξ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have heΓ : (fun ξ => √(Γ ξ) ^ 24) = fun ξ => Γ ξ ^ 12 := by
    funext ξ
    rw [show (24 : ℕ) = 2 * 12 by norm_num, pow_mul, Real.sq_sqrt (hΓ0 ξ)]
  have hiΓ : Integrable (fun ξ => √(Γ ξ) ^ 24) (stdGauss (Fin n)) := by
    rw [heΓ]
    exact hM.2.1
  have hgrad : ∀ᵐ ξ ∂stdGauss (Fin n),
      ∑ i, (fderiv ℝ (fun ξ => centrePhi D c (sphPt (c.1.2 + D.tau0 c • ξ))) ξ
        (Pi.single i 1)) ^ 2 ≤ Γ ξ := by
    rw [centrePhi_eq]
    exact ae_of_all _ fun _ => le_rfl
  have hiInv := (BstLean.Part153.invMoment_le (p := 24) (n := n) (by omega) c.1.2 hτ).1
  have hne := BstLean.Part153.ae_normSq_ne (n := n) (by omega) c.1.2 hτ.ne'
  have hPC := BstLean.Part165.lemmaS_grad_p c.1.2 hτ hK hPhi (by norm_num : 1 ≤ (24 : ℕ))
    hΓ0 hiΓ hgrad hiInv hne
  rw [centrePhi_eq, heΓ] at hPC
  have hBound : ∀ ξ, |f ξ| ≤ |centrePhi D c 0| + K := by
    intro ξ
    have hl := hPhi (sphPt (c.1.2 + D.tau0 c • ξ)) 0
    simp only [Pi.zero_apply, sub_zero] at hl
    have hs : √(∑ j, sphPt (c.1.2 + D.tau0 c • ξ) j ^ 2) = 1 := by
      change √(normSq (sphPt (c.1.2 + D.tau0 c • ξ))) = 1
      rw [normSq_sphPt (by omega), Real.sqrt_one]
    rw [hs, mul_one] at hl
    have ha := abs_sub_abs_le_abs_sub
      (centrePhi D c (sphPt (c.1.2 + D.tau0 c • ξ))) (centrePhi D c 0)
    change |centrePhi D c (sphPt (c.1.2 + D.tau0 c • ξ))| ≤ _
    linarith
  have hi : Integrable (fun ξ => |f ξ - ∫ ζ, f ζ ∂stdGauss (Fin n)| ^ 24)
      (stdGauss (Fin n)) := by
    refine Integrable.of_bound
      ((((measurable_centreCoordinate D c).sub measurable_const).abs.pow_const 24).aestronglyMeasurable)
      ((|centrePhi D c 0| + K + |∫ ζ, f ζ ∂stdGauss (Fin n)|) ^ 24)
      (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add (hBound ξ) le_rfl)) 24
  refine ⟨hi, hPC.trans ?_⟩
  have hm := mul_le_mul_of_nonneg_left hM.2.2
    (by positivity : 0 ≤ (π / 2) ^ 24 * BstLean.Part162.gmom 24)
  simpa only [mul_assoc] using hm

lemma moment_tail {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (p : ℕ) {t B : ℝ} (ht : 0 < t)
    (hi : Integrable (fun x => |f x| ^ p) μ) (hm : ∫ x, |f x| ^ p ∂μ ≤ B) :
    μ.real {x | t ≤ |f x|} ≤ B / t ^ p := by
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (ae_of_all _ fun x => pow_nonneg (abs_nonneg (f x)) p) hi (t ^ p)
  have hsub : {x | t ≤ |f x|} ⊆ {x | t ^ p ≤ |f x| ^ p} :=
    fun x hx => pow_le_pow_left₀ ht.le hx p
  have hmono := measureReal_mono (μ := μ) hsub
  rw [le_div_iff₀ (pow_pos ht p)]
  have h := (mul_le_mul_of_nonneg_left hmono (pow_nonneg ht.le p)).trans (hM.trans hm)
  simpa only [mul_comm] using h

/-- The mass payment is for the complement of the good intersection. -/
theorem good_complement_mass {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (omega f : X → ℝ)
    (hω : ∀ x, 0 ≤ omega x) (hf : ∀ x, 0 ≤ f x) {u d q H C : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hd : d < (1 - u) ^ 2)
    (hgap : 0 < √((1 - u) ^ 2 - d) - q)
    (hmean : ∫ x, f x ∂μ ≤ q)
    (hEi : Integrable (fun x => |√(omega x) - 1| ^ 32) μ)
    (hE : ∫ x, |√(omega x) - 1| ^ 32 ∂μ ≤ H ^ 32)
    (hFi : Integrable (fun x => |f x - ∫ y, f y ∂μ| ^ 24) μ)
    (hF : ∫ x, |f x - ∫ y, f y ∂μ| ^ 24 ∂μ ≤ C) :
    μ.real {x | ¬ goodInput ((1 - u) ^ 2) d (omega x) (f x)} ≤
      (H / u) ^ 32 + C / (√((1 - u) ^ 2 - d) - q) ^ 24 := by
  have hsub : {x | ¬ goodInput ((1 - u) ^ 2) d (omega x) (f x)} ⊆
      {x | u ≤ |√(omega x) - 1|} ∪
        {x | √((1 - u) ^ 2 - d) - q ≤ |f x - ∫ y, f y ∂μ|} := by
    intro x hx
    by_cases h : u ≤ |√(omega x) - 1|
    · exact Or.inl h
    · right
      have hclose : |√(omega x) - 1| < u := not_le.mp h
      have hlow : 1 - u < √(omega x) := by linarith [(abs_lt.mp hclose).1]
      have hωgood : (1 - u) ^ 2 ≤ omega x := by
        nlinarith [Real.sq_sqrt (hω x), Real.sqrt_nonneg (omega x)]
      have hfbad : (1 - u) ^ 2 - d < f x ^ 2 := by
        by_contra hn
        exact hx ⟨hωgood, not_lt.mp hn⟩
      have hthreshold : √((1 - u) ^ 2 - d) < f x := by
        nlinarith [Real.sq_sqrt (by linarith : 0 ≤ (1 - u) ^ 2 - d), hf x,
          Real.sqrt_nonneg ((1 - u) ^ 2 - d)]
      change √((1 - u) ^ 2 - d) - q ≤ |f x - ∫ y, f y ∂μ|
      exact le_trans (by linarith) (le_abs_self (f x - ∫ y, f y ∂μ))
  have hm := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  have h1 := moment_tail μ (fun x => √(omega x) - 1) 32 hu hEi hE
  have h2 := moment_tail μ (fun x => f x - ∫ y, f y ∂μ) 24 hgap hFi hF
  rw [div_pow]
  exact hm.trans (add_le_add h1 h2)

lemma inputEnergy_nonneg (D : Design n) (c : Ret n) (ξ : Fin n → ℝ) :
    0 ≤ inputEnergy D c ξ := div_nonneg (normSq_nonneg _) (Nat.cast_nonneg _)

lemma centreCoordinate_nonneg (D : Design n) (c : Ret n)
    (hb : ∀ j, 0 ≤ D.bA c.1 c.2.1.1 j) (ξ : Fin n → ℝ) : 0 ≤ centreCoordinate D c ξ := by
  unfold centreCoordinate
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro j _
    have hh : 0 ≤ hStand D c ξ j := by
      change 0 ≤ max 0 _
      exact le_max_left _ _
    exact mul_nonneg hh (hb j)
  · exact mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg _)

/-- The three interfaces give the mass needed by corrected WF, at one retained value. -/
theorem network_WF_mass (hn : 50 ≤ n) (D : Design n) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hb : 0 < normSq (D.bA c.1 c.2.1.1))
    (hb0 : ∀ j, 0 ≤ D.bA c.1 c.2.1.1 j) {M H xi E u d : ℝ}
    (hI : WFInterfaces D c M H xi) (hE : centreEnergy D c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : d < (1 - u) ^ 2)
    (hgap : 0 < √((1 - u) ^ 2 - d) - (√E + √(xi / n))) :
    (n : ℝ) * (stdGauss (Fin n)).real
      {ξ | ¬ goodInput ((1 - u) ^ 2) d (inputEnergy D c ξ) (centreCoordinate D c ξ)} ≤
    (n : ℝ) * ((H / u) ^ 32 +
      ((π / 2) ^ 24 * BstLean.Part162.gmom 24 * (M / n) ^ 12) /
        (√((1 - u) ^ 2 - d) - (√E + √(xi / n))) ^ 24) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have he : (fun ξ => |√(inputEnergy D c ξ) - 1| ^ 32) =
      (fun ξ => (√(inputEnergy D c ξ) - 1) ^ 32) := by
    funext ξ
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hiE : Integrable (fun ξ => |√(inputEnergy D c ξ) - 1| ^ 32) (stdGauss (Fin n)) := by
    rw [he]
    exact hI.energy.2.1
  have hEm : (∫ ξ, |√(inputEnergy D c ξ) - 1| ^ 32 ∂stdGauss (Fin n)) ≤ H ^ 32 := by
    rw [he]
    exact hI.energy.2.2
  have hm : (∫ ξ, centreCoordinate D c ξ ∂stdGauss (Fin n)) ≤ √E + √(xi / n) := by
    have hp := (abs_le.mp hI.parallel.2).2
    have hs := Real.sqrt_le_sqrt hE
    linarith
  have hFm := centreCoordinate_moment24 hn D c hτ hb hI.direction
  exact mul_le_mul_of_nonneg_left
    (good_complement_mass (stdGauss (Fin n)) (inputEnergy D c) (centreCoordinate D c)
      (inputEnergy_nonneg D c) (centreCoordinate_nonneg D c hb0)
      hu hu1 hd hgap hm hiE hEm hFm.1 hFm.2) (Nat.cast_nonneg _)

/-- A payment for the good-set complement supplies the older residual-mass interface. -/
theorem MASS_at_of_good_complement (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    (hb : normSq (D.bA c.1 c.2.1.1) ≠ 0) {a d Beta : ℝ}
    (hmass : (n : ℝ) * (stdGauss (Fin n)).real
      {ξ | ¬ goodInput a d (inputEnergy D c ξ) (centreCoordinate D c ξ)} ≤ Beta) :
    MASS_at D c d Beta := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmA : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have hsub : {ξ | 2 / (mA n : ℝ) * normSq (res (D.bA c.1 c.2.1.1) (hStand D c ξ)) <
      2 / (n : ℝ) * d} ⊆
      {ξ | ¬ goodInput a d (inputEnergy D c ξ) (centreCoordinate D c ξ)} := by
    intro ξ hl
    change ¬ goodInput a d (inputEnergy D c ξ) (centreCoordinate D c ξ)
    intro hg
    have hr := mul_le_mul_of_nonneg_left (goodInput_residual hg) (Nat.cast_nonneg n)
    rw [← network_residual_energy hn D c hb ξ] at hr
    have hscaled := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2 / (n : ℝ) ^ 2)
    have he : 2 / (n : ℝ) ^ 2 * ((n : ℝ) * d) = 2 / (n : ℝ) * d := by field_simp
    rw [he] at hscaled
    change 2 / (mA n : ℝ) * normSq (res (D.bA c.1 c.2.1.1) (hStand D c ξ)) <
      2 / (n : ℝ) * d at hl
    rw [hmA] at hl
    linarith
  exact (mul_le_mul_of_nonneg_left (measureReal_mono (μ := stdGauss (Fin n)) hsub)
    (Nat.cast_nonneg n)).trans hmass

end BstLean.Part188
