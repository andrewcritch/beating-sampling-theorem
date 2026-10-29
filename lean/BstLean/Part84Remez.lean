import BstLean.Part84Defs
import BstLean.Part59RPlus
import BstLean.Part53Polar

/-!
# Part 84, the sphere step (`RemezStep`)

Remez on the radius of `W` (Lemma R+ of Part 59), polar independence (Part 53), then Markov and
Chebyshev.
-/

namespace BstLean.Part84

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part41 (varU)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part78 (zv)
open BstLean.Part81 (JJ WIdx pf)

variable {n d : ℕ}

/-! ## Scaling -/

lemma FW_smul (P : MvPolynomial (Fin n) ℝ) (lam t : ℝ) (W : WIdx n d → ℝ) (x : Fin n → ℝ) :
    FW P lam (t • W) x = FW P (lam * t) W x := by
  unfold FW
  congr 2
  funext i
  simp only [zv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

lemma FW_smul' (P : MvPolynomial (Fin n) ℝ) (lam t : ℝ) (W : WIdx n d → ℝ) :
    FW P lam (t • W) = FW P (lam * t) W := funext fun x => FW_smul P lam t W x

lemma BW_smul (P : MvPolynomial (Fin n) ℝ) (lam t : ℝ) (W : WIdx n d → ℝ) :
    BW P lam (t • W) = BW P (lam * t) W := by
  unfold BW; rw [FW_smul']

lemma VW_smul (P : MvPolynomial (Fin n) ℝ) (lam t : ℝ) (W : WIdx n d → ℝ) :
    VW P lam (t • W) = VW P (lam * t) W := by
  unfold VW; rw [FW_smul']

lemma errW_smul (P : MvPolynomial (Fin n) ℝ) (lam t : ℝ) (W : WIdx n d → ℝ) :
    errW P lam (t • W) = errW P (lam * t) W := by
  unfold errW; rw [BW_smul]

lemma VW_nonneg (P : MvPolynomial (Fin n) ℝ) (lam : ℝ) (W : WIdx n d → ℝ) : 0 ≤ VW P lam W := by
  unfold VW varU
  exact integral_nonneg fun x => sq_nonneg _

/-! ## Measurability -/

lemma FW_joint_cont (P : MvPolynomial (Fin n) ℝ) (lam : ℝ) :
    Continuous (fun p : (WIdx n d → ℝ) × (Fin n → ℝ) => FW P lam p.1 p.2) := by
  unfold FW
  apply (MvPolynomial.continuous_eval P).comp
  apply continuous_pi
  intro i
  apply continuous_const.mul
  unfold zv
  apply continuous_finsetSum
  intro q _
  exact ((continuous_apply (q, i)).comp continuous_fst).mul
    ((BstLean.Part81.cont_pf q).comp continuous_snd)

lemma BW_meas (k : ℕ) (hPoly : PolyRep n d) (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ k)
    (lam : ℝ) : Measurable (fun W : WIdx n d → ℝ => BW P lam W) := by
  obtain ⟨Q, -, hQ⟩ := (hPoly k P hP lam).2
  have : (fun W : WIdx n d → ℝ => BW P lam W) = fun W => MvPolynomial.eval W Q :=
    funext fun W => (hQ W).symm
  rw [this]
  exact (MvPolynomial.continuous_eval Q).measurable

lemma VW_meas (k : ℕ) (hn : 1 ≤ n) (hPoly : PolyRep n d) (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ k) (lam : ℝ) : Measurable (fun W : WIdx n d → ℝ => VW P lam W) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hm : Measurable (fun p : (WIdx n d → ℝ) × (Fin n → ℝ) =>
      (FW P lam p.1 p.2 - BW P lam p.1) ^ 2) :=
    (((FW_joint_cont P lam).measurable).sub ((BW_meas k hPoly P hP lam).comp measurable_fst)).pow_const 2
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := uniformSphere n)).measurable

/-! ## The polar transfer -/

private lemma ofReal_integral_le' {α : Type*} [MeasurableSpace α] {ν : Measure α} {g : α → ℝ}
    (hg : ∀ x, 0 ≤ g x) : ENNReal.ofReal (∫ x, g x ∂ν) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂ν := by
  by_cases hi : Integrable g ν
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hg)]
  · rw [integral_undef hi, ENNReal.ofReal_zero]; exact bot_le

lemma rad_smul_unit {ι : Type} [Fintype ι] (Z : ι → ℝ) : radF53 Z • unitF53 Z = Z := by
  unfold radF53 unitF53
  by_cases h : Real.sqrt (∑ i, Z i ^ 2) = 0
  · rw [h, zero_smul]
    have h0 : ∑ i, Z i ^ 2 = 0 :=
      (Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg (Z i))).mp h
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (Z i))).mp h0 i (Finset.mem_univ i)
    simpa using (pow_eq_zero_iff (two_ne_zero)).mp this |>.symm
  · rw [smul_smul, mul_one_div, div_self h, one_smul]

lemma polar_transfer {ι : Type} [Fintype ι] (G : (ι → ℝ) → ℝ) (hGm : Measurable G)
    (hG0 : ∀ W, 0 ≤ G W) (hGi : Integrable G (stdGauss ι)) (R s : ℝ) (hR : 0 ≤ R)
    (hrem : ∀ ω : ι → ℝ, G (s • ω) ≤ R * ∫ W', G (radF53 W' • ω) ∂stdGauss ι) :
    ∫⁻ W, ENNReal.ofReal (G (s • unitF53 W)) ∂stdGauss ι ≤
      ENNReal.ofReal (R * ∫ W, G W ∂stdGauss ι) := by
  obtain ⟨F, hF⟩ : ∃ F : (ι → ℝ) → ℝ → ℝ≥0∞,
      F = fun ω ρ => ENNReal.ofReal (R * G (ρ • ω)) := ⟨_, rfl⟩
  have hFm : Measurable (Function.uncurry F) := by
    rw [hF]
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.mul (hGm.comp (measurable_snd.smul measurable_fst)))
  calc ∫⁻ W, ENNReal.ofReal (G (s • unitF53 W)) ∂stdGauss ι
      ≤ ∫⁻ W, ∫⁻ W', F (unitF53 W) (radF53 W') ∂stdGauss ι ∂stdGauss ι := by
        apply lintegral_mono
        intro W
        refine (ENNReal.ofReal_le_ofReal (hrem (unitF53 W))).trans ?_
        rw [← integral_const_mul, hF]
        exact ofReal_integral_le' (fun W' => mul_nonneg hR (hG0 _))
    _ = ∫⁻ W, F (unitF53 W) (radF53 W) ∂stdGauss ι := (BstLean.Part53.gauss_polar_gen F hFm).symm
    _ = ∫⁻ W, ENNReal.ofReal (R * G W) ∂stdGauss ι := by
        rw [hF]; simp only [rad_smul_unit]
    _ = ENNReal.ofReal (∫ W, R * G W ∂stdGauss ι) :=
        (ofReal_integral_eq_lintegral_ofReal (hGi.const_mul R)
          (Filter.Eventually.of_forall fun W => mul_nonneg hR (hG0 W))).symm
    _ = ENNReal.ofReal (R * ∫ W, G W ∂stdGauss ι) := by rw [integral_const_mul]

/-! ## The sphere step -/

theorem remezStep (n d k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (c1 cV efl : ℝ) (hc1 : 0 ≤ c1)
    (hcV : 0 ≤ cV) (hcard : 1000 ≤ Fintype.card (WIdx n d))
    (hG : GaussModel n d k c1 cV efl) (hRad : RadPoly n d) (hPoly : PolyRep n d) :
    RemezStep n d k c1 cV efl := by
  classical
  intro P hP lam hlam ε κ hε hκ hefl
  obtain ⟨L, Vb, hL, hVb, hi1, hi2, hb1, hb2⟩ := hG P hP lam hlam
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hDpos : (0 : ℝ) < DW n d := by
    unfold DW; exact_mod_cast (show 0 < Fintype.card (WIdx n d) by omega)
  have hsD : Real.sqrt (DW n d) ≠ 0 := (Real.sqrt_pos.mpr hDpos).ne'
  set R1 : ℝ := 5 / 2 * ((k : ℝ) + 1) ^ 2 with hR1
  set R2 : ℝ := 5 / 2 * (2 * (k : ℝ) + 1) ^ 2 with hR2
  have hR10 : 0 ≤ R1 := by positivity
  have hR20 : 0 ≤ R2 := by positivity
  set G1 : (WIdx n d → ℝ) → ℝ := fun W => errW P lam W ^ 2 with hG1
  set G2 : (WIdx n d → ℝ) → ℝ := fun W => (VW P lam W - Vb) ^ 2 with hG2
  have hBm := BW_meas k hPoly P hP lam
  have hVm := VW_meas k hn hPoly P hP lam
  have hG1m : Measurable G1 := (hBm.sub_const _).pow_const 2
  have hG2m : Measurable G2 := (hVm.sub_const _).pow_const 2
  have hsm : Measurable (fun W : WIdx n d → ℝ => Real.sqrt (DW n d) • unitF53 W) :=
    (BstLean.Part53.measurable_unitF (ι := WIdx n d)).const_smul (Real.sqrt (DW n d))
  -- Remez, error
  have hrem1 : ∀ ω : WIdx n d → ℝ, G1 (Real.sqrt (DW n d) • ω) ≤
      R1 * ∫ W', G1 (radF53 W' • ω) ∂stdGauss (WIdx n d) := by
    intro ω
    obtain ⟨⟨qB, hBd, hBe⟩, -⟩ := hRad k P hP (Real.sqrt (DW n d) • ω)
    set Q : Polynomial ℝ :=
      (qB.comp (Polynomial.C lam * Polynomial.X) - Polynomial.C (g0P d P)) ^ 2 with hQ
    have hQe : ∀ t : ℝ, Q.eval t = G1 (t • Real.sqrt (DW n d) • ω) := by
      intro t
      simp only [hQ, hG1, errW, BW_smul P lam t, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, hBe]
    have hQd : Q.natDegree ≤ 2 * k := by
      refine (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left 2 ?_)
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ (by simp))
      refine (Polynomial.natDegree_comp_le).trans ?_
      have h1 : (Polynomial.C lam * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 :=
        (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
      calc qB.natDegree * _ ≤ k * 1 := Nat.mul_le_mul hBd h1
        _ = k := mul_one k
    have h := BstLean.Part59.lemmaRp59 k (WIdx n d) hcard Q hQd
      (fun x => by rw [hQe]; exact sq_nonneg _)
    rw [hQe 1, one_smul] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    apply integral_congr_ae
    filter_upwards with W'
    rw [hQe, smul_smul]
    show G1 ((radF53 W' / Real.sqrt (DW n d) * Real.sqrt (DW n d)) • ω) = _
    rw [div_mul_cancel₀ _ hsD]
  -- Remez, variance
  have hrem2 : ∀ ω : WIdx n d → ℝ, G2 (Real.sqrt (DW n d) • ω) ≤
      R2 * ∫ W', G2 (radF53 W' • ω) ∂stdGauss (WIdx n d) := by
    intro ω
    obtain ⟨-, ⟨qV, hVd, hVe⟩⟩ := hRad k P hP (Real.sqrt (DW n d) • ω)
    set Q : Polynomial ℝ :=
      (qV.comp (Polynomial.C lam * Polynomial.X) - Polynomial.C Vb) ^ 2 with hQ
    have hQe : ∀ t : ℝ, Q.eval t = G2 (t • Real.sqrt (DW n d) • ω) := by
      intro t
      simp only [hQ, hG2, VW_smul P lam t, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, hVe]
    have hQd : Q.natDegree ≤ 2 * (2 * k) := by
      refine (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left 2 ?_)
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ (by simp))
      refine (Polynomial.natDegree_comp_le).trans ?_
      have h1 : (Polynomial.C lam * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 :=
        (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
      calc qV.natDegree * _ ≤ 2 * k * 1 := Nat.mul_le_mul hVd h1
        _ = 2 * k := mul_one _
    have h := BstLean.Part59.lemmaRp59 (2 * k) (WIdx n d) hcard Q hQd
      (fun x => by rw [hQe]; exact sq_nonneg _)
    rw [hQe 1, one_smul] at h
    have hc : (5 : ℝ) / 2 * (((2 * k : ℕ) : ℝ) + 1) ^ 2 = R2 := by rw [hR2]; push_cast; ring
    rw [hc] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    apply integral_congr_ae
    filter_upwards with W'
    rw [hQe, smul_smul]
    show G2 ((radF53 W' / Real.sqrt (DW n d) * Real.sqrt (DW n d)) • ω) = _
    rw [div_mul_cancel₀ _ hsD]
  have hT1 := polar_transfer G1 hG1m (fun W => sq_nonneg _) hi1 R1 _ hR10 hrem1
  have hT2 := polar_transfer G2 hG2m (fun W => sq_nonneg _) hi2 R2 _ hR20 hrem2
  have hm1 : Measurable (fun W : WIdx n d → ℝ =>
      ENNReal.ofReal (G1 (Real.sqrt (DW n d) • unitF53 W))) :=
    ENNReal.measurable_ofReal.comp (hG1m.comp hsm)
  have hm2 : Measurable (fun W : WIdx n d → ℝ =>
      ENNReal.ofReal (G2 (Real.sqrt (DW n d) • unitF53 W))) :=
    ENNReal.measurable_ofReal.comp (hG2m.comp hsm)
  have hδ : 0 < 1 - efl - κ := by linarith
  have ht1 : 0 ≤ R1 * c1 / (n * (ε ^ 2 * κ)) := by positivity
  have ht2 : 0 ≤ R2 * cV / (n * (1 - efl - κ) ^ 2) := by positivity
  rcases hL.eq_or_lt with hL0 | hLpos
  · -- `L = 0`
    have hz : ∫⁻ W, ENNReal.ofReal (G1 (Real.sqrt (DW n d) • unitF53 W)) ∂stdGauss (WIdx n d) = 0 := by
      apply le_antisymm _ bot_le
      have : ∫ W, G1 W ∂stdGauss (WIdx n d) ≤ 0 := by
        refine hb1.trans (le_of_eq ?_); rw [← hL0, mul_zero]
      exact hT1.trans (le_of_eq (ENNReal.ofReal_eq_zero.mpr
        (mul_nonpos_of_nonneg_of_nonpos hR10 this)))
    have hae := (lintegral_eq_zero_iff hm1).mp hz
    refine le_trans (le_of_eq (measure_mono_null ?_ (ae_iff.mp hae))) bot_le
    intro W hW
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, ENNReal.ofReal_eq_zero, not_le, hG1] at hW ⊢
    have := VW_nonneg P lam (Real.sqrt (DW n d) • unitF53 W)
    have h2 : 0 ≤ ε ^ 2 * VW P lam (Real.sqrt (DW n d) • unitF53 W) := by positivity
    exact lt_of_le_of_lt h2 hW
  · -- `L > 0`
    have hθ1 : 0 < ε ^ 2 * κ * L := by positivity
    have hθ2 : 0 < ((1 - efl - κ) * L) ^ 2 := by positivity
    have hsub : {W : WIdx n d → ℝ | ε ^ 2 * VW P lam (Real.sqrt (DW n d) • unitF53 W) <
          errW P lam (Real.sqrt (DW n d) • unitF53 W) ^ 2} ⊆
        {W | ENNReal.ofReal (ε ^ 2 * κ * L) ≤
            ENNReal.ofReal (G1 (Real.sqrt (DW n d) • unitF53 W))} ∪
        {W | ENNReal.ofReal (((1 - efl - κ) * L) ^ 2) ≤
            ENNReal.ofReal (G2 (Real.sqrt (DW n d) • unitF53 W))} := by
      intro W hW
      simp only [Set.mem_ofPred_eq] at hW
      by_cases hV : VW P lam (Real.sqrt (DW n d) • unitF53 W) < κ * L
      · right
        apply ENNReal.ofReal_le_ofReal
        simp only [hG2]
        have h1 : (1 - efl - κ) * L ≤ Vb - VW P lam (Real.sqrt (DW n d) • unitF53 W) := by
          nlinarith
        have h0 : 0 ≤ (1 - efl - κ) * L := by positivity
        nlinarith
      · left
        apply ENNReal.ofReal_le_ofReal
        simp only [hG1]
        push Not at hV
        have : ε ^ 2 * (κ * L) ≤ ε ^ 2 * VW P lam (Real.sqrt (DW n d) • unitF53 W) :=
          mul_le_mul_of_nonneg_left hV (by positivity)
        nlinarith
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    have hM1 := (meas_ge_le_lintegral_div hm1.aemeasurable
      (by simpa using hθ1) ENNReal.ofReal_ne_top).trans (ENNReal.div_le_div_right hT1 _)
    have hM2 := (meas_ge_le_lintegral_div hm2.aemeasurable
      (by simpa using hθ2) ENNReal.ofReal_ne_top).trans (ENNReal.div_le_div_right hT2 _)
    rw [← ENNReal.ofReal_div_of_pos hθ1] at hM1
    rw [← ENNReal.ofReal_div_of_pos hθ2] at hM2
    rw [show 5 / 2 * ((k : ℝ) + 1) ^ 2 * c1 / (n * (ε ^ 2 * κ)) +
        5 / 2 * (2 * (k : ℝ) + 1) ^ 2 * cV / (n * (1 - efl - κ) ^ 2) =
        R1 * c1 / (n * (ε ^ 2 * κ)) + R2 * cV / (n * (1 - efl - κ) ^ 2) from rfl,
      ENNReal.ofReal_add ht1 ht2]
    refine add_le_add (hM1.trans (ENNReal.ofReal_le_ofReal ?_))
      (hM2.trans (ENNReal.ofReal_le_ofReal ?_))
    · rw [div_le_div_iff₀ hθ1 (by positivity)]
      have := mul_le_mul_of_nonneg_left hb1 hR10
      calc R1 * (∫ W, G1 W ∂stdGauss (WIdx n d)) * (n * (ε ^ 2 * κ))
          ≤ R1 * (c1 / n * L) * (n * (ε ^ 2 * κ)) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = R1 * c1 * (ε ^ 2 * κ * L) := by field_simp
    · rw [div_le_div_iff₀ hθ2 (by positivity)]
      have := mul_le_mul_of_nonneg_left hb2 hR20
      calc R2 * (∫ W, G2 W ∂stdGauss (WIdx n d)) * (n * (1 - efl - κ) ^ 2)
          ≤ R2 * (cV / n * L ^ 2) * (n * (1 - efl - κ) ^ 2) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = R2 * cV * ((1 - efl - κ) * L) ^ 2 := by field_simp

end BstLean.Part84
