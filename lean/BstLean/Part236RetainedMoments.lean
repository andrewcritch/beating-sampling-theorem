import BstLean.Part236Frame

/-! RF error moments transfer to every retained design without normalization. -/
namespace BstLean.Part236
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part134 BstLean.Part136 BstLean.Part157 BstLean.Part159
open BstLean.Part227

theorem retained_marginal {n : ℕ} (D : Centres n) {f : WHid n → ℝ} {B : ℝ}
    (hi : Integrable f (hidGauss (2 * n) (mW n))) (hf : ∀ θ, 0 ≤ f θ)
    (hb : ∫ θ, f θ ∂hidGauss (2 * n) (mW n) ≤ B) (E : Set (Ret n)) :
    IntegrableOn (fun x : Ret n => f x.1.1) E (retDist D) ∧
      ∫ x in E, f x.1.1 ∂retDist D ≤ B := by
  have hmap := retDist_hid D
  have hi' : Integrable f ((retDist D).map (fun x : Ret n => x.1.1)) := by
    rw [hmap]; exact hi
  have hic := (integrable_map_measure hi'.aestronglyMeasurable
    measurable_hidOf.aemeasurable).1 hi'
  have he := integral_map (μ := retDist D) measurable_hidOf.aemeasurable
    hi'.aestronglyMeasurable
  rw [hmap] at he
  refine ⟨hic.integrableOn, ?_⟩
  have hs := setIntegral_mono_set hic.integrableOn
    (Filter.Eventually.of_forall fun x => hf x.1.1)
    (Filter.Eventually.of_forall (show E ⊆ univ from subset_univ E))
  rw [setIntegral_univ] at hs
  simp only [Function.comp_apply] at hs
  rw [← he] at hs
  exact hs.trans hb

theorem retained_error_moments {n : ℕ} (hn : 4096 ≤ n) (D : Centres n)
    {sp p₂ Xc dT eB e : ℝ} (c : FrameCertificate n sp p₂ Xc dT eB)
    (he : 0 < e) (E : Set (Ret n)) :
    IntegrableOn (fun x : Ret n => (coeffK c e * √(yK x.1.1)) ^ 2) E (retDist D) ∧
    IntegrableOn (fun x : Ret n => coeffD c e * yD x.1.1) E (retDist D) ∧
    (∫ x in E, (coeffK c e * √(yK x.1.1)) ^ 2 ∂retDist D) ≤
      372 / 1000 * coeffK c e ^ 2 ∧
    (∫ x in E, coeffD c e * yD x.1.1 ∂retDist D) ≤ 448 / 1000 * coeffD c e := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hD : 0 ≤ coeffD c e := coeffD_nonneg c he
  obtain ⟨iK, iD, hK, hDmean⟩ := normalized_moments hn
  have hkEq : (fun θ : WHid n => (coeffK c e * √(yK θ)) ^ 2) =
      fun θ => coeffK c e ^ 2 * yK θ := by
    funext θ
    rw [mul_pow, Real.sq_sqrt (yK_nonneg θ)]
  have hkI : Integrable (fun θ : WHid n => (coeffK c e * √(yK θ)) ^ 2)
      (hidGauss (2 * n) (mW n)) := by rw [hkEq]; exact iK.const_mul _
  have hkB : (∫ θ : WHid n, (coeffK c e * √(yK θ)) ^ 2 ∂hidGauss (2 * n) (mW n)) ≤
      372 / 1000 * coeffK c e ^ 2 := by
    rw [hkEq, integral_const_mul]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hK (sq_nonneg (coeffK c e))
  have hdB : (∫ θ : WHid n, coeffD c e * yD θ ∂hidGauss (2 * n) (mW n)) ≤
      448 / 1000 * coeffD c e := by
    rw [integral_const_mul]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hDmean hD
  have hk := retained_marginal D hkI (fun _ => sq_nonneg _) hkB E
  have hd := retained_marginal D (iD.const_mul _) (fun θ => mul_nonneg hD (yD_nonneg θ)) hdB E
  exact ⟨hk.1, hd.1, hk.2, hd.2⟩

theorem frame_error_max {n : ℕ} (hn : 4096 ≤ n) {Xc dT eB e : ℝ}
    (c : FrameCertificate n (4 / 100) (4 / 10000) Xc dT eB) (he : 0 < e)
    {θ : WHid n} (hθ : θ ∈ hidden n (4 / 100) (4 / 10000) Xc dT eB) :
    frameError c e θ ≤ 25 * coeffK c e + 2500 * coeffD c e := by
  obtain ⟨hk, hd⟩ := base_error_bounds hn hθ.1.1.1.1.1
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hK : 0 ≤ coeffK c e := coeffK_nonneg c he
  have hD : 0 ≤ coeffD c e := coeffD_nonneg c he
  have hs : √(yK θ) ≤ 25 := by
    exact (Real.sqrt_le_sqrt hk.le).trans (by norm_num)
  have h1 := mul_le_mul_of_nonneg_left hs hK
  have h2 := mul_le_mul_of_nonneg_left hd.le hD
  unfold frameError
  nlinarith only [h1, h2]
end BstLean.Part236
