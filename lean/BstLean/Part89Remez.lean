import BstLean.Part86Remez
import BstLean.Part89Defs

/-!
# Part 89, the sphere step with a Markov level `a` and a Chebyshev level `b`

`remez89P`: the per-polynomial version of `Part86.XRemez.remez86`, from `GMP M P lam c1 cV efl`.
`remez89`: the corollary `RemezStep86 M k gq (remezBound89 n k c1 cV efl a b)`.
-/

namespace BstLean.Part89

open MeasureTheory MvPolynomial
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part78 (zv)
open BstLean.Part84 (polar_transfer)
open BstLean.Part86 BstLean.Part86.XRemez

/-- The deterministic step with levels `a` (Markov) and `b` (Chebyshev). -/
lemma det89 (Lv Vb efl η a b E Vd V T R X Bv gDv gqv : ℝ) (hLv : 0 ≤ Lv)
    (hVb : (1 - efl) * Lv ≤ Vb) (hb0 : 0 ≤ b)
    (hab : 9 / 4 * a + 1 / 400 ≤ b * (1 - efl) / 4) (hE : E ≤ a * Lv) (hV : b * Vb ≤ Vd)
    (hR : R ≤ 2 * Lv) (hR0 : 0 ≤ R) (hT : 0 ≤ T) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 40)
    (hs : (gqv - gDv) ^ 2 ≤ η ^ 2 * (R + T)) (hVm : V = Vd + X) (hX : 1 / 2 * T - E ≤ X)
    (hJ : (Bv - gDv) ^ 2 ≤ E) : (Bv - gqv) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 * V := by
  have hη2 : η ^ 2 ≤ 1 / 1600 := by nlinarith
  have h1 : (gqv - gDv) ^ 2 ≤ (R + T) / 1600 := by
    refine hs.trans ?_
    have : 0 ≤ R + T := by linarith
    nlinarith
  have h2 : (Bv - gqv) ^ 2 ≤ 2 * (Bv - gDv) ^ 2 + 2 * (gqv - gDv) ^ 2 := by
    nlinarith [sq_nonneg ((Bv - gDv) + (gqv - gDv))]
  have h3 : b * ((1 - efl) * Lv) ≤ b * Vb := mul_le_mul_of_nonneg_left hVb hb0
  have h4 := mul_le_mul_of_nonneg_right hab hLv
  linarith

section main

variable {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S] [MeasurableSpace G]

theorem remez89P (M : Mod n I J S G) (d k : ℕ) (c1 cV efl η a b : ℝ)
    (gq : MvPolynomial (I ⊕ Fin n) ℝ → ℝ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hR : Reg M d) (hPF : PolyFacts M d)
    (P : MvPolynomial (I ⊕ Fin n) ℝ) (hP : P.totalDegree ≤ k) (lam : ℝ)
    (hG : GMP M P lam c1 cV efl)
    (hSu : SurrHyp M η gq) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 40)
    (hefl0 : 0 ≤ efl) (hefl : efl < 1) (ha : 0 < a) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hab : 9 / 4 * a + 1 / 400 ≤ b * (1 - efl) / 4)
    (hc1 : 0 ≤ c1) (hcV : 0 ≤ cV) (hcard : 1000 ≤ Fintype.card (J × Fin n)) :
    stdGauss (J × Fin n) (badSet86 M gq P lam) ≤
      ENNReal.ofReal (remezBound89 n k c1 cV efl a b) := by
  classical
  obtain ⟨Lv, Vb, hLv, hVb, hi1, hi2, hb1, hb2, hR1⟩ := hG
  have he1 : 0 < 1 - efl := by linarith
  have hbb : 0 < 1 - b := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hDpos : (0 : ℝ) < DWr n J := by
    unfold DWr; exact_mod_cast (show 0 < Fintype.card (J × Fin n) by omega)
  set sD : ℝ := Real.sqrt (DWr n J) with hsDdef
  have hsD : sD ≠ 0 := (Real.sqrt_pos.mpr hDpos).ne'
  have hsDc : Real.sqrt (Fintype.card (J × Fin n) : ℝ) = sD := rfl
  set Rc1 : ℝ := 5 / 2 * ((k : ℝ) + 1) ^ 2 with hRc1
  set Rc2 : ℝ := 5 / 2 * (2 * (k : ℝ) + 1) ^ 2 with hRc2
  have hRc10 : 0 ≤ Rc1 := by positivity
  have hRc20 : 0 ≤ Rc2 := by positivity
  set G1 : (J × Fin n → ℝ) → ℝ := fun W => Esl M P lam W with hG1
  set G2 : (J × Fin n → ℝ) → ℝ := fun W => (Vdn M P lam W - Vb) ^ 2 with hG2
  have hG1m : Measurable G1 := Esl_meas M d k P hR hPF hP lam
  have hG2m : Measurable G2 := ((Vdn_meas M d k P hR hPF hP lam).sub_const _).pow_const 2
  have hG10 : ∀ W, 0 ≤ G1 W := fun W => integral_nonneg fun p => sq_nonneg _
  have hsm : Measurable (fun W : J × Fin n → ℝ => sD • unitF53 W) :=
    (BstLean.Part53.measurable_unitF (ι := J × Fin n)).const_smul sD
  have hlin : (Polynomial.C lam * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
  -- Remez, error
  have hrem1 : ∀ ω : J × Fin n → ℝ, G1 (sD • ω) ≤
      Rc1 * ∫ W', G1 (radF53 W' • ω) ∂stdGauss (J × Fin n) := by
    intro ω
    obtain ⟨qE, hEd, hEe⟩ := Esl_poly M d k P hR hPF hP (sD • ω)
    set Q : Polynomial ℝ := qE.comp (Polynomial.C lam * Polynomial.X) with hQ
    have hQe : ∀ t : ℝ, Q.eval t = G1 (t • sD • ω) := by
      intro t
      simp only [hQ, hG1, Esl_smul M P lam t, Polynomial.eval_comp, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, hEe]
    have hQd : Q.natDegree ≤ 2 * k := by
      refine (Polynomial.natDegree_comp_le).trans ?_
      calc qE.natDegree * _ ≤ 2 * k * 1 := Nat.mul_le_mul hEd hlin
        _ = 2 * k := mul_one _
    have h := BstLean.Part59.lemmaRp59 k (J × Fin n) hcard Q hQd
      (fun x => by rw [hQe]; exact hG10 _)
    rw [hQe 1, one_smul, hsDc] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    apply integral_congr_ae
    filter_upwards with W'
    rw [hQe, smul_smul]
    show G1 ((radF53 W' / sD * sD) • ω) = _
    rw [div_mul_cancel₀ _ hsD]
  -- Remez, variance
  have hrem2 : ∀ ω : J × Fin n → ℝ, G2 (sD • ω) ≤
      Rc2 * ∫ W', G2 (radF53 W' • ω) ∂stdGauss (J × Fin n) := by
    intro ω
    obtain ⟨qV, hVd, hVe⟩ := (hPF k P hP).2.2.2.2.2.1 (sD • ω)
    set Q : Polynomial ℝ :=
      (qV.comp (Polynomial.C lam * Polynomial.X) - Polynomial.C Vb) ^ 2 with hQ
    have hQe : ∀ t : ℝ, Q.eval t = G2 (t • sD • ω) := by
      intro t
      simp only [hQ, hG2, Vdn_smul M P lam t, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, hVe]
    have hQd : Q.natDegree ≤ 2 * (2 * k) := by
      refine (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left 2 ?_)
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ (by simp))
      refine (Polynomial.natDegree_comp_le).trans ?_
      calc qV.natDegree * _ ≤ 2 * k * 1 := Nat.mul_le_mul hVd hlin
        _ = 2 * k := mul_one _
    have h := BstLean.Part59.lemmaRp59 (2 * k) (J × Fin n) hcard Q hQd
      (fun x => by rw [hQe]; exact sq_nonneg _)
    rw [hQe 1, one_smul, hsDc] at h
    have hc : (5 : ℝ) / 2 * (((2 * k : ℕ) : ℝ) + 1) ^ 2 = Rc2 := by rw [hRc2]; push_cast; ring
    rw [hc] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    apply integral_congr_ae
    filter_upwards with W'
    rw [hQe, smul_smul]
    show G2 ((radF53 W' / sD * sD) • ω) = _
    rw [div_mul_cancel₀ _ hsD]
  have hT1 := polar_transfer G1 hG1m hG10 hi1 Rc1 _ hRc10 hrem1
  have hT2 := polar_transfer G2 hG2m (fun W => sq_nonneg _) hi2 Rc2 _ hRc20 hrem2
  have hm1 : Measurable (fun W : J × Fin n → ℝ => ENNReal.ofReal (G1 (sD • unitF53 W))) :=
    ENNReal.measurable_ofReal.comp (hG1m.comp hsm)
  have hm2 : Measurable (fun W : J × Fin n → ℝ => ENNReal.ofReal (G2 (sD • unitF53 W))) :=
    ENNReal.measurable_ofReal.comp (hG2m.comp hsm)
  -- the deterministic step at a point
  have hdet : ∀ W : J × Fin n → ℝ, G1 W ≤ a * Lv → b * Vb ≤ Vdn M P lam W →
      (Bm M P lam W - gq P) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 * Vm M P lam W := by
    intro W hE hV
    obtain ⟨hJ, hX⟩ := slice_two M d k P hR hPF hP lam W
    exact det89 Lv Vb efl η a b (Esl M P lam W) (Vdn M P lam W) (Vm M P lam W) (Tm M P) (R1 M P)
      _ (Bm M P lam W) (gD M P) (gq P) hLv hVb hb0 hab hE hV hR1
      (integral_nonneg fun p => integral_nonneg fun g => sq_nonneg _)
      (integral_nonneg fun p => sq_nonneg _) hη0 hη (hSu P)
      (Vm_decomp M d k P hR hPF hP lam W) hX hJ
  have hbad : ∀ W, W ∈ badSet86 M gq P lam →
      ¬ (G1 (sD • unitF53 W) ≤ a * Lv ∧ b * Vb ≤ Vdn M P lam (sD • unitF53 W)) := by
    intro W hW h
    have := hdet _ h.1 h.2
    simp only [badSet86, Set.mem_ofPred_eq] at hW
    exact absurd hW (not_lt.mpr this)
  have ht1 : 0 ≤ Rc1 * c1 / (a * n) := by positivity
  have ht2 : 0 ≤ Rc2 * cV / ((1 - b) ^ 2 * (1 - efl) ^ 2 * n) := by positivity
  rcases hLv.eq_or_lt with hL0 | hLpos
  · -- `Lv = 0`
    have hVb0 : 0 ≤ Vb := by rw [← hL0, mul_zero] at hVb; exact hVb
    have hz1 : ∫⁻ W, ENNReal.ofReal (G1 (sD • unitF53 W)) ∂stdGauss (J × Fin n) = 0 := by
      apply le_antisymm _ bot_le
      have : ∫ W, G1 W ∂stdGauss (J × Fin n) ≤ 0 := by
        refine hb1.trans (le_of_eq ?_); rw [← hL0, mul_zero]
      exact hT1.trans (le_of_eq (ENNReal.ofReal_eq_zero.mpr
        (mul_nonpos_of_nonneg_of_nonpos hRc10 this)))
    have hz2 : ∫⁻ W, ENNReal.ofReal (G2 (sD • unitF53 W)) ∂stdGauss (J × Fin n) = 0 := by
      apply le_antisymm _ bot_le
      have : ∫ W, G2 W ∂stdGauss (J × Fin n) ≤ 0 := by
        refine hb2.trans (le_of_eq ?_); rw [← hL0]; simp
      exact hT2.trans (le_of_eq (ENNReal.ofReal_eq_zero.mpr
        (mul_nonpos_of_nonneg_of_nonpos hRc20 this)))
    have hae1 := (lintegral_eq_zero_iff hm1).mp hz1
    have hae2 := (lintegral_eq_zero_iff hm2).mp hz2
    have hnull : stdGauss (J × Fin n) (badSet86 M gq P lam) = 0 := by
      have hae : ∀ᵐ W ∂stdGauss (J × Fin n), W ∉ badSet86 M gq P lam := by
        filter_upwards [hae1, hae2] with W h1 h2 hW
        simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at h1 h2
        refine hbad W hW ⟨?_, ?_⟩
        · rw [← hL0]; simpa using h1
        · have h3 : (Vdn M P lam (sD • unitF53 W) - Vb) ^ 2 = 0 :=
            le_antisymm h2 (sq_nonneg _)
          have h4 : Vdn M P lam (sD • unitF53 W) = Vb := by
            have := pow_eq_zero_iff (two_ne_zero) |>.mp h3
            linarith
          rw [h4]; nlinarith
      simpa [ae_iff] using hae
    rw [hnull]; exact bot_le
  · -- `Lv > 0`
    have hVbL : 0 ≤ (1 - efl) * Lv := by positivity
    have hθ1 : 0 < a * Lv := by positivity
    have hθ2 : 0 < ((1 - b) * ((1 - efl) * Lv)) ^ 2 := by positivity
    have hsub : badSet86 M gq P lam ⊆
        {W | ENNReal.ofReal (a * Lv) ≤ ENNReal.ofReal (G1 (sD • unitF53 W))} ∪
        {W | ENNReal.ofReal (((1 - b) * ((1 - efl) * Lv)) ^ 2) ≤ ENNReal.ofReal (G2 (sD • unitF53 W))} := by
      intro W hW
      have hb := hbad W hW
      by_cases hE : G1 (sD • unitF53 W) ≤ a * Lv
      · right
        have hV : ¬ b * Vb ≤ Vdn M P lam (sD • unitF53 W) := fun h => hb ⟨hE, h⟩
        push Not at hV
        apply ENNReal.ofReal_le_ofReal
        simp only [hG2]
        have hq : (1 - b) * ((1 - efl) * Lv) ≤ (1 - b) * Vb :=
          mul_le_mul_of_nonneg_left hVb hbb.le
        have hq0 : 0 ≤ (1 - b) * ((1 - efl) * Lv) := by positivity
        have hq1 : (1 - b) * ((1 - efl) * Lv) ≤ Vb - Vdn M P lam (sD • unitF53 W) := by linarith
        have := pow_le_pow_left₀ hq0 hq1 2
        nlinarith
      · left
        push Not at hE
        exact ENNReal.ofReal_le_ofReal hE.le
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    have hM1 := (meas_ge_le_lintegral_div hm1.aemeasurable (ε := ENNReal.ofReal (a * Lv))
      (ENNReal.ofReal_pos.mpr hθ1).ne' ENNReal.ofReal_ne_top).trans (ENNReal.div_le_div_right hT1 _)
    have hM2 := (meas_ge_le_lintegral_div hm2.aemeasurable (ε := ENNReal.ofReal (((1 - b) * ((1 - efl) * Lv)) ^ 2))
      (ENNReal.ofReal_pos.mpr hθ2).ne' ENNReal.ofReal_ne_top).trans (ENNReal.div_le_div_right hT2 _)
    rw [← ENNReal.ofReal_div_of_pos hθ1] at hM1
    rw [← ENNReal.ofReal_div_of_pos hθ2] at hM2
    rw [show remezBound89 n k c1 cV efl a b = Rc1 * c1 / (a * n) +
        Rc2 * cV / ((1 - b) ^ 2 * (1 - efl) ^ 2 * n) from rfl,
      ENNReal.ofReal_add ht1 ht2]
    refine add_le_add (hM1.trans (ENNReal.ofReal_le_ofReal ?_))
      (hM2.trans (ENNReal.ofReal_le_ofReal ?_))
    · rw [div_le_div_iff₀ hθ1 (by positivity)]
      have := mul_le_mul_of_nonneg_left hb1 hRc10
      calc Rc1 * (∫ W, G1 W ∂stdGauss (J × Fin n)) * (a * n)
          ≤ Rc1 * (c1 / n * Lv) * (a * n) := mul_le_mul_of_nonneg_right this (by positivity)
        _ = Rc1 * c1 * (a * Lv) := by field_simp
    · rw [div_le_div_iff₀ hθ2 (by positivity)]
      have := mul_le_mul_of_nonneg_left hb2 hRc20
      calc Rc2 * (∫ W, G2 W ∂stdGauss (J × Fin n)) * ((1 - b) ^ 2 * (1 - efl) ^ 2 * n)
          ≤ Rc2 * (cV / n * Lv ^ 2) * ((1 - b) ^ 2 * (1 - efl) ^ 2 * n) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = Rc2 * cV * ((1 - b) * ((1 - efl) * Lv)) ^ 2 := by field_simp


theorem remez89 (M : Mod n I J S G) (d k : ℕ) (c1 cV efl η a b : ℝ)
    (gq : MvPolynomial (I ⊕ Fin n) ℝ → ℝ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hR : Reg M d) (hPF : PolyFacts M d) (hG : GaussModel86 M k c1 cV efl)
    (hSu : SurrHyp M η gq) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 40)
    (hefl0 : 0 ≤ efl) (hefl : efl < 1) (ha : 0 < a) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hab : 9 / 4 * a + 1 / 400 ≤ b * (1 - efl) / 4)
    (hc1 : 0 ≤ c1) (hcV : 0 ≤ cV) (hcard : 1000 ≤ Fintype.card (J × Fin n)) :
    RemezStep86 M k gq (remezBound89 n k c1 cV efl a b) := by
  intro P hP lam hlam
  exact remez89P M d k c1 cV efl η a b gq hn hk hR hPF P hP lam (hG P hP lam hlam) hSu hη0 hη
    hefl0 hefl ha hb0 hb1 hab hc1 hcV hcard

end main

end BstLean.Part89

#print axioms BstLean.Part89.remez89P
#print axioms BstLean.Part89.remez89
