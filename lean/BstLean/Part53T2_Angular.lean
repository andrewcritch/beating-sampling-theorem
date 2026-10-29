import BstLean.Part53T2_WickMoment
import BstLean.Part53T2_Polar
import BstLean.Part43Floor

namespace BstLean.Part53.T2Aux

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD mapMD unitOfD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Tens TSymm frob uJ varU phiM phiSq Mono colM)

variable {n d : ℕ}

private lemma map_linear (M : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    mapMD M x = linZ M (fun p => phiM x p) := by
  classical
  funext a
  unfold mapMD linZ BstLean.Part36.coefD
  rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range (fun i => ∑ β : Sym (Fin n) i,
    (if h : i < d + 1 then M ⟨⟨i, h⟩, (β, a)⟩ else 0) * BstLean.Part36.monoVal x β.1)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro β _
  simp [colM, phiM, i.2]

lemma normalized_gaussian_variance_bound (d k : ℕ) (hd : 1 ≤ d)
    (hW : LemmaW53 k) (hTr : LemmaTr53) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      ∀ j : ℕ, 1 ≤ j → j ≤ k →
      (sg n d) ^ (2 * j) *
          (∫ Z, varU μ (uJ T j Z) ∂stdGauss (CoefIdxD n d)) ≤
        C * (n : ℝ) ^ (k / 2) * Ncirc n d k f0 T := by
  obtain ⟨CW, hCW, hbW⟩ := raw_gaussian_moment k hW hTr (d + 1) (by positivity)
  obtain ⟨CT, hCT, hbT⟩ := raw_tensor_bound d k hTr
  refine ⟨CW * CT, mul_nonneg hCW hCT, ?_⟩
  intro n hn μ hμ f0 T hT j hj hjk
  let := hμ.prob
  have hv := expected_var_le_raw (d := d) μ hμ hn T j
  have hi := raw_second_expectation_integrable (d := d) μ hμ hn T j
  have hraw : (∫ x, ∫ Z : CoefIdxD n d → ℝ, uJ T j Z x ^ 2
      ∂stdGauss (CoefIdxD n d) ∂μ) ≤ CW * (n : ℝ) ^ (j / 2) * frob (T j) := by
    have hb := integral_mono_ae hi (integrable_const (CW * (n : ℝ) ^ (j / 2) * frob (T j)))
      (show (fun x => ∫ Z : CoefIdxD n d → ℝ, uJ T j Z x ^ 2 ∂stdGauss (CoefIdxD n d)) ≤ᵐ[μ]
        fun _ => CW * (n : ℝ) ^ (j / 2) * frob (T j) by
        filter_upwards [hμ.sphere] with x hx
        have hphi : nsq (fun p : Mono n d => phiM x p) ≤ (d : ℝ) + 1 :=
          (BstLean.Part43.phiSq_bounds hd x hx).2
        have h := (hbW n d j hn hjk (T j) (hT j hj hjk) _ hphi).2
        simpa only [uJ, map_linear] using h)
    simpa using hb
  have hTraw := hbT n hn f0 T j hj hjk
  have hN : 0 ≤ Ncirc n d k f0 T := by
    unfold Ncirc
    exact Finset.sum_nonneg fun _ _ => div_nonneg
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hsg : 0 ≤ sg n d := by unfold sg; positivity
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : j / 2 + (k - j) / 2 ≤ k / 2 := by omega
  calc
    _ ≤ (sg n d) ^ (2 * j) * (CW * (n : ℝ) ^ (j / 2) * frob (T j)) :=
      mul_le_mul_of_nonneg_left (hv.trans hraw) (pow_nonneg hsg _)
    _ = CW * (n : ℝ) ^ (j / 2) * (frob (T j) / DD n d ^ j) := by
      rw [sg_pow_even n d j hn]
      ring
    _ ≤ CW * (n : ℝ) ^ (j / 2) *
        (CT * (n : ℝ) ^ ((k - j) / 2) * Ncirc n d k f0 T) :=
      mul_le_mul_of_nonneg_left hTraw (by positivity)
    _ = (CW * CT) * (n : ℝ) ^ (j / 2 + (k - j) / 2) * Ncirc n d k f0 T := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hnR hexp) (mul_nonneg hCW hCT)) hN

lemma angular_variance_bound (d k : ℕ) (hd : 1 ≤ d)
    (hW : LemmaW53 k) (hTr : LemmaTr53) (hP : GaussPolar53) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      ∀ j : ℕ, 1 ≤ j → j ≤ k →
      (∫⁻ Z, ENNReal.ofReal (varU μ (uJ T j (unitOfD Z))) ∂stdGauss (CoefIdxD n d)) ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (k / 2) * Ncirc n d k f0 T) := by
  obtain ⟨C, hC, hb⟩ := normalized_gaussian_variance_bound d k hd hW hTr
  refine ⟨C, hC, fun n hn μ hμ f0 T hT j hj hjk => ?_⟩
  exact (angular_variance_le_gaussian hP μ hμ hn T j).trans
    (ENNReal.ofReal_le_ofReal (hb n hn μ hμ f0 T hT j hj hjk))

end BstLean.Part53.T2Aux
