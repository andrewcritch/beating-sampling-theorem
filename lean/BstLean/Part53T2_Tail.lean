import BstLean.Part53T2_Angular
import BstLean.Part53T2_Bounds

namespace BstLean.Part53.T2Aux

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD unitOfD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Tens TSymm uJ varU sdU)

variable {n d : ℕ}

lemma radialDefect_measurable (μ : Measure (Fin n → ℝ)) (hμ : SphLaw n μ)
    (hn : 1 ≤ n) (k : ℕ) (T : Tens n) :
    Measurable (fun Z : CoefIdxD n d → ℝ =>
      radialDefect μ k T (unitOfD Z) (radialScale n d Z)) := by
  unfold radialDefect sdU
  apply Finset.measurable_sum
  intro j _
  exact ((((radialScale_continuous n d).measurable.pow_const j).sub measurable_const).abs).mul
    (((varU_uJ_measurable μ hμ hn T j).comp measurable_unit).sqrt)

private lemma defect_square_le (μ : Measure (Fin n → ℝ)) (k : ℕ) (T : Tens n)
    (Z : CoefIdxD n d → ℝ) :
    radialDefect μ k T (unitOfD Z) (radialScale n d Z) ^ 2 ≤
      (k : ℝ) * ∑ j ∈ Finset.Icc 1 k,
        (radialScale n d Z ^ j - 1) ^ 2 * varU μ (uJ T j (unitOfD Z)) := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 k)
    (f := fun j => |radialScale n d Z ^ j - 1| * sdU μ (uJ T j (unitOfD Z)))
  have hc : (Finset.Icc 1 k).card = k := by simp
  rw [hc] at h
  unfold radialDefect
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow, sq_abs, sdU]
  have hv : 0 ≤ varU μ (uJ T j (unitOfD Z)) := integral_nonneg fun _ => sq_nonneg _
  rw [Real.sq_sqrt hv]

private lemma radial_variance_product (hP : GaussPolar53) (μ : Measure (Fin n → ℝ))
    (hμ : SphLaw n μ) (hn : 1 ≤ n) (T : Tens n) (j : ℕ)
    (hi : Integrable (fun Z : CoefIdxD n d → ℝ => (radialScale n d Z ^ j - 1) ^ 2)
      (stdGauss (CoefIdxD n d))) :
    (∫⁻ Z, ENNReal.ofReal ((radialScale n d Z ^ j - 1) ^ 2 *
        varU μ (uJ T j (unitOfD Z))) ∂stdGauss (CoefIdxD n d)) =
      ENNReal.ofReal (∫ Z, (radialScale n d Z ^ j - 1) ^ 2 ∂stdGauss (CoefIdxD n d)) *
        ∫⁻ Z, ENNReal.ofReal (varU μ (uJ T j (unitOfD Z))) ∂stdGauss (CoefIdxD n d) := by
  let a := fun r : ℝ => ENNReal.ofReal (((r / Real.sqrt (DD n d)) ^ j - 1) ^ 2)
  let b := fun W : CoefIdxD n d → ℝ => ENNReal.ofReal (varU μ (uJ T j W))
  have ha : Measurable a := by dsimp [a]; fun_prop
  have hb : Measurable b := (varU_uJ_measurable μ hμ hn T j).ennreal_ofReal
  have hp := polar_product hP a b ha hb
  change (∫⁻ Z, ENNReal.ofReal ((radialScale n d Z ^ j - 1) ^ 2) *
      ENNReal.ofReal (varU μ (uJ T j (unitOfD Z))) ∂stdGauss (CoefIdxD n d)) = _ at hp
  have hm (Z : CoefIdxD n d → ℝ) : ENNReal.ofReal ((radialScale n d Z ^ j - 1) ^ 2 *
      varU μ (uJ T j (unitOfD Z))) = ENNReal.ofReal ((radialScale n d Z ^ j - 1) ^ 2) *
      ENNReal.ofReal (varU μ (uJ T j (unitOfD Z))) :=
    ENNReal.ofReal_mul (sq_nonneg _)
  simp_rw [hm]
  rw [hp]
  change (∫⁻ Z, ENNReal.ofReal ((radialScale n d Z ^ j - 1) ^ 2) ∂stdGauss (CoefIdxD n d)) * _ = _
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun Z => sq_nonneg _)]

lemma radialDefect_second_moment (d k : ℕ) (hd : 1 ≤ d) (hkd : k ≤ 2 * d + 1)
    (hW : LemmaW53 k) (hTr : LemmaTr53) (hP : GaussPolar53) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      (∫⁻ Z, ENNReal.ofReal (radialDefect μ k T (unitOfD Z) (radialScale n d Z) ^ 2)
        ∂stdGauss (CoefIdxD n d)) ≤ ENNReal.ofReal (C / n * Ncirc n d k f0 T) := by
  obtain ⟨CR, hCR, hbR⟩ := radialScale_uniform_second_moment k
  obtain ⟨CA, hCA, hbA⟩ := angular_variance_bound d k hd hW hTr hP
  let C := (k : ℝ) ^ 2 * CR * CA * (d.factorial : ℝ)
  refine ⟨C, by dsimp [C]; positivity, fun n hn μ hμ f0 T hT => ?_⟩
  have hD := BstLean.Part36.DD_pos (d := d) hn
  have hN : 0 ≤ Ncirc n d k f0 T := by
    unfold Ncirc
    exact Finset.sum_nonneg fun _ _ => div_nonneg
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  let Q := CR / DD n d * (CA * (n : ℝ) ^ (k / 2) * Ncirc n d k f0 T)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let F := fun (j : ℕ) (Z : CoefIdxD n d → ℝ) =>
    (radialScale n d Z ^ j - 1) ^ 2 * varU μ (uJ T j (unitOfD Z))
  have hF0 (j : ℕ) (Z : CoefIdxD n d → ℝ) : 0 ≤ F j Z :=
    mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  have hFm (j : ℕ) : Measurable (fun Z => ENNReal.ofReal (F j Z)) :=
    (((((radialScale_continuous n d).measurable.pow_const j).sub measurable_const).pow_const 2).mul
      ((varU_uJ_measurable μ hμ hn T j).comp measurable_unit)).ennreal_ofReal
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc 1 k) :
      (∫⁻ Z, ENNReal.ofReal (F j Z) ∂stdGauss (CoefIdxD n d)) ≤ ENNReal.ofReal Q := by
    obtain ⟨hi, hb⟩ := hbR n d hn j (Finset.mem_Icc.mp hj).2
    rw [radial_variance_product hP μ hμ hn T j hi]
    have h1 := ENNReal.ofReal_le_ofReal hb
    have h2 := hbA n hn μ hμ f0 T hT j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
    calc
      _ ≤ ENNReal.ofReal (CR / DD n d) *
          ENNReal.ofReal (CA * (n : ℝ) ^ (k / 2) * Ncirc n d k f0 T) := by gcongr
      _ = _ := (ENNReal.ofReal_mul (div_nonneg hCR hD.le)).symm
  have hcs : (∫⁻ Z, ENNReal.ofReal (radialDefect μ k T (unitOfD Z) (radialScale n d Z) ^ 2)
      ∂stdGauss (CoefIdxD n d)) ≤ ENNReal.ofReal ((k : ℝ) ^ 2 * Q) := by
    calc
      _ ≤ ∫⁻ Z, ENNReal.ofReal ((k : ℝ) * ∑ j ∈ Finset.Icc 1 k, F j Z)
          ∂stdGauss (CoefIdxD n d) :=
        lintegral_mono fun Z => ENNReal.ofReal_le_ofReal (defect_square_le μ k T Z)
      _ = ENNReal.ofReal (k : ℝ) * ∑ j ∈ Finset.Icc 1 k,
          ∫⁻ Z, ENNReal.ofReal (F j Z) ∂stdGauss (CoefIdxD n d) := by
        simp_rw [ENNReal.ofReal_mul (Nat.cast_nonneg k),
          ENNReal.ofReal_sum_of_nonneg (fun j _ => hF0 j _)]
        rw [lintegral_const_mul _ (Finset.measurable_sum _ (fun j _ => hFm j)),
          lintegral_finsetSum _ (fun j _ => hFm j)]
      _ ≤ ENNReal.ofReal (k : ℝ) * ∑ _j ∈ Finset.Icc 1 k, ENNReal.ofReal Q := by
        gcongr
        exact hterm _ ‹_›
      _ = ENNReal.ofReal ((k : ℝ) ^ 2 * Q) := by
        have hc : (Finset.Icc 1 k).card = k := by simp
        simp only [Finset.sum_const, hc, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast]
        rw [← ENNReal.ofReal_mul (Nat.cast_nonneg k),
          ← ENNReal.ofReal_mul (Nat.cast_nonneg k)]
        congr 1
        ring
  apply hcs.trans
  apply ENNReal.ofReal_le_ofReal
  have hratio := dimension_ratio n d k hn hkd
  calc
    (k : ℝ) ^ 2 * Q = ((k : ℝ) ^ 2 * CR * CA) *
        ((n : ℝ) ^ (k / 2) / DD n d) * Ncirc n d k f0 T := by dsimp [Q]; ring
    _ ≤ ((k : ℝ) ^ 2 * CR * CA) * ((d.factorial : ℝ) / n) * Ncirc n d k f0 T :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (by positivity)) hN
    _ = _ := by dsimp [C]; ring

/-- Markov gives the tail estimate in the sphere-floor proof. -/
lemma radialDefect_tail (d k : ℕ) (hd : 1 ≤ d) (hkd : k ≤ 2 * d + 1)
    (hW : LemmaW53 k) (hTr : LemmaTr53) (hP : GaussPolar53) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      0 < Ncirc n d k f0 T → ∀ s : ℝ, 0 < s →
      stdGauss (CoefIdxD n d) {Z | Real.sqrt (s * Ncirc n d k f0 T) ≤
        radialDefect μ k T (unitOfD Z) (radialScale n d Z)} ≤ ENNReal.ofReal (C / (n * s)) := by
  obtain ⟨C, hC, hb⟩ := radialDefect_second_moment d k hd hkd hW hTr hP
  refine ⟨C, hC, fun n hn μ hμ f0 T hT hN s hs => ?_⟩
  let N := Ncirc n d k f0 T
  have hsN : 0 < s * N := mul_pos hs hN
  have hfm := ((radialDefect_measurable (d := d) μ hμ hn k T).pow_const 2).ennreal_ofReal
  have hsub : {Z : CoefIdxD n d → ℝ | Real.sqrt (s * N) ≤
        radialDefect μ k T (unitOfD Z) (radialScale n d Z)} ⊆
      {Z | ENNReal.ofReal (s * N) ≤
        ENNReal.ofReal (radialDefect μ k T (unitOfD Z) (radialScale n d Z) ^ 2)} := by
    intro Z hZ
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans hZ)).mpr hZ
    rw [Real.sq_sqrt hsN.le] at hsq
    exact ENNReal.ofReal_le_ofReal hsq
  apply le_trans (measure_mono hsub)
    ((meas_ge_le_lintegral_div hfm.aemeasurable
      (by simpa using hsN) ENNReal.ofReal_ne_top).trans ?_)
  apply le_trans (ENNReal.div_le_div_right (hb n hn μ hμ f0 T hT) _)
  rw [← ENNReal.ofReal_div_of_pos hsN]
  apply ENNReal.ofReal_le_ofReal
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact le_of_eq (by dsimp [N]; field_simp)

end BstLean.Part53.T2Aux
