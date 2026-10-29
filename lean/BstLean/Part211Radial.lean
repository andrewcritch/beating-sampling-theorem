import BstLean.Part206First
import BstLean.Part198Radial

/-! Gaussian radial moments and their dependence on a fixed projection. -/
namespace BstLean.Part211
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part131 (projMat projMat_mulVec projMat_dot stdGauss_decomp)

lemma normSq_square_integrable (n : ℕ) :
    Integrable (fun g : Fin n → ℝ => normSq g ^ 2) (stdGauss (Fin n)) := by
  have he : ∀ g : Fin n → ℝ, normSq g ^ 2 = ∑ i, ∑ j, g i * g i * g j * g j := by
    intro g
    unfold normSq
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [he]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    BstLean.Part107.int4 i i j j

noncomputable def radialRoot {n : ℕ} (g : Fin n → ℝ) : ℝ := √(normSq g / n)

lemma radialRoot_sq {n : ℕ} (g : Fin n → ℝ) : radialRoot g ^ 2 = normSq g / n := by
  exact sq_sqrt (div_nonneg (normSq_nonneg g) (Nat.cast_nonneg n))

lemma radial_fluctuation {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun g : Fin n → ℝ => (normSq g / n - 1) ^ 2) (stdGauss (Fin n)) ∧
    (∫ g : Fin n → ℝ, (normSq g / n - 1) ^ 2 ∂stdGauss (Fin n)) = 2 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h1 := (BstLean.Part149.stdGauss_normSq n).1
  have h2 := normSq_square_integrable n
  have he : (fun g : Fin n → ℝ => (normSq g / n - 1) ^ 2) =
      fun g => normSq g ^ 2 / (n : ℝ) ^ 2 - (2 / n) * normSq g + 1 := by
    funext g
    ring
  rw [he]
  refine ⟨((h2.div_const _).sub (h1.const_mul _)).add (integrable_const _), ?_⟩
  rw [integral_add (f := fun g => normSq g ^ 2 / (n : ℝ) ^ 2 - (2 / n) * normSq g)
      (g := fun _ => (1 : ℝ)) ((h2.div_const _).sub (h1.const_mul _)) (integrable_const _),
    integral_sub (f := fun g => normSq g ^ 2 / (n : ℝ) ^ 2)
      (g := fun g => (2 / n) * normSq g) (h2.div_const _) (h1.const_mul _),
    integral_div, integral_const_mul,
    (BstLean.Part149.stdGauss_normSq n).2, integral_const]
  simp only [probReal_univ, one_smul]
  have hmean : (∫ g : Fin n → ℝ, normSq g ^ 2 ∂stdGauss (Fin n)) =
      (n : ℝ) * (n + 2) := by
    simpa only [normSq, Fintype.card_fin] using
      (BstLean.Part107.normSq_mom2 (ι := Fin n))
  rw [hmean]
  field_simp
  ring

lemma radialRoot_error {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun g : Fin n → ℝ => (radialRoot g - 1) ^ 2) (stdGauss (Fin n)) ∧
    (∫ g : Fin n → ℝ, (radialRoot g - 1) ^ 2 ∂stdGauss (Fin n)) ≤ 2 / (n : ℝ) := by
  have hpt : ∀ g : Fin n → ℝ,
      (radialRoot g - 1) ^ 2 ≤ (normSq g / n - 1) ^ 2 := by
    intro g
    rw [← radialRoot_sq g]
    have h0 : 0 ≤ radialRoot g := sqrt_nonneg _
    nlinarith [mul_nonneg (sq_nonneg (radialRoot g - 1))
      (show 0 ≤ radialRoot g ^ 2 + 2 * radialRoot g by positivity)]
  have hi : Integrable (fun g : Fin n → ℝ => (radialRoot g - 1) ^ 2)
      (stdGauss (Fin n)) := by
    apply (radial_fluctuation hn).1.mono'
    · apply Continuous.aestronglyMeasurable
      unfold radialRoot
      exact ((continuous_normSq.div_const _).sqrt.sub continuous_const).pow 2
    · exact ae_of_all _ fun g => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hpt g
  refine ⟨hi, ?_⟩
  exact (integral_mono hi (radial_fluctuation hn).1 hpt).trans_eq (radial_fluctuation hn).2

lemma unit_decomposition_norm {n : ℕ} {u : Fin n → ℝ} (hu : normSq u = 1)
    (z : ℝ) (g : Fin n → ℝ) :
    normSq (z • u + projMat u *ᵥ g) = z ^ 2 + normSq g - (g ⬝ᵥ u) ^ 2 := by
  have he : z • u + projMat u *ᵥ g = g - (g ⬝ᵥ u - z) • u := by
    rw [projMat_mulVec, dotProduct_comm u g]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, BstLean.Part153.normSq_sub_smul, hu]
  ring

lemma bounded_mul_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f w : Ω → ℝ} {C : ℝ} (hf : Integrable f μ) (hw : Measurable w)
    (hb : ∀ x, |w x| ≤ C) : Integrable (fun x => w x * f x) μ := by
  apply (hf.norm.const_mul C).mono' (hw.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  exact ae_of_all _ fun x => by
    dsimp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs (w x)]
    exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

/-- A bounded projection weight retains the exact radial dependence. -/
theorem weighted_radial_identity {n : ℕ} {u : Fin n → ℝ} (hu : normSq u = 1)
    {w : ℝ → ℝ} {C : ℝ} (hw : Measurable w) (hb : ∀ z, |w z| ≤ C) :
    (∫ g, w (g ⬝ᵥ u) * (normSq g - n) ∂stdGauss (Fin n)) =
      ∫ z, w z * (z ^ 2 - 1) ∂gaussianReal 0 1 := by
  have hud : u ⬝ᵥ u = 1 := by simpa only [normSq, dotProduct, ← sq] using hu
  let F : (Fin n → ℝ) → ℝ := fun g => w (g ⬝ᵥ u) * (normSq g - n)
  let P : ℝ × (Fin n → ℝ) → (Fin n → ℝ) := fun p => p.1 • u + projMat u *ᵥ p.2
  have hP : Measurable P := by dsimp [P]; fun_prop
  have hF : Measurable F := by
    apply Measurable.mul (hw.comp (by unfold dotProduct; fun_prop))
      (continuous_normSq.measurable.sub_const _)
  have hi : Integrable F (stdGauss (Fin n)) :=
    bounded_mul_integrable ((BstLean.Part149.stdGauss_normSq n).1.sub (integrable_const _))
      (hw.comp (by unfold dotProduct; fun_prop)) (fun g => hb (g ⬝ᵥ u))
  have hmap : ((gaussianReal 0 1).prod (stdGauss (Fin n))).map P = stdGauss (Fin n) :=
    stdGauss_decomp hud
  have hcomp : ∀ p, F (P p) = w p.1 * (p.1 ^ 2 + normSq p.2 - (p.2 ⬝ᵥ u) ^ 2 - n) := by
    intro p
    dsimp [F, P]
    rw [add_dotProduct, smul_dotProduct, hud, projMat_dot hud, smul_eq_mul, mul_one, add_zero,
      unit_decomposition_norm hu]
  have hip : Integrable (fun p => F (P p))
      ((gaussianReal 0 1).prod (stdGauss (Fin n))) := by
    apply (integrable_map_measure hF.aestronglyMeasurable hP.aemeasurable).mp
    rwa [hmap]
  change (∫ g, F g ∂stdGauss (Fin n)) = _
  rw [← hmap, integral_map hP.aemeasurable hF.aestronglyMeasurable, integral_prod _ hip]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    simp_rw [hcomp]
    rw [integral_const_mul,
      integral_sub (f := fun g => z ^ 2 + normSq g - (g ⬝ᵥ u) ^ 2) (g := fun _ => (n : ℝ))
        (((integrable_const _).add (BstLean.Part149.stdGauss_normSq n).1).sub
        (BstLean.Part160.MFB.lin_moments u).2.2.1) (integrable_const _),
      integral_sub (f := fun g => z ^ 2 + normSq g) (g := fun g => (g ⬝ᵥ u) ^ 2)
        ((integrable_const _).add (BstLean.Part149.stdGauss_normSq n).1)
        (BstLean.Part160.MFB.lin_moments u).2.2.1,
      integral_add (f := fun _ => z ^ 2) (g := fun g => normSq g)
        (integrable_const _) (BstLean.Part149.stdGauss_normSq n).1,
      (BstLean.Part149.stdGauss_normSq n).2, (BstLean.Part160.MFB.lin_moments u).2.2.2.1, hu]
    simp only [integral_const, probReal_univ, one_smul]
    ring

theorem weighted_radial_bounds {n : ℕ} (hn : 1 ≤ n)
    {u : Fin n → ℝ} (hu : normSq u = 1) {w : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hw : Measurable w) (hb : ∀ z, 0 ≤ w z ∧ w z ≤ C) :
    -(C / n) ≤ (∫ g, w (g ⬝ᵥ u) * (normSq g / n - 1) ∂stdGauss (Fin n)) ∧
    (∫ g, w (g ⬝ᵥ u) * (normSq g / n - 1) ∂stdGauss (Fin n)) ≤ C / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hab : ∀ z, |w z| ≤ C := fun z => by rw [abs_of_nonneg (hb z).1]; exact (hb z).2
  have hi : Integrable (fun z => w z * (z ^ 2 - 1)) (gaussianReal 0 1) :=
    bounded_mul_integrable ((integrable_pow_gauss 2).sub (integrable_const _)) hw hab
  have hl : -C ≤ ∫ z, w z * (z ^ 2 - 1) ∂gaussianReal 0 1 := by
    calc -C = ∫ _ : ℝ, -C ∂gaussianReal 0 1 := by simp
      _ ≤ _ := integral_mono (integrable_const _) hi fun z => by
        nlinarith [mul_nonneg (hb z).1 (sq_nonneg z), (hb z).2]
  have hh : (∫ z, w z * (z ^ 2 - 1) ∂gaussianReal 0 1) ≤ C := by
    calc _ ≤ ∫ z, C * z ^ 2 ∂gaussianReal 0 1 := by
          apply integral_mono hi ((integrable_pow_gauss 2).const_mul _)
          intro z
          nlinarith [mul_le_mul_of_nonneg_right (hb z).2 (sq_nonneg z), (hb z).1]
      _ = C := by rw [integral_const_mul, BstLean.Part29.gaussMom_eq]; norm_num [BstLean.Part29.gaussMom]
  have he : (∫ g, w (g ⬝ᵥ u) * (normSq g / n - 1) ∂stdGauss (Fin n)) =
      (∫ z, w z * (z ^ 2 - 1) ∂gaussianReal 0 1) / n := by
    have hpt : (fun g : Fin n → ℝ => w (g ⬝ᵥ u) * (normSq g / n - 1)) =
        fun g => (w (g ⬝ᵥ u) * (normSq g - n)) / n := by
      funext g
      field_simp
    rw [hpt, integral_div, weighted_radial_identity hu hw hab]
  rw [he]
  exact ⟨by simpa only [neg_div] using div_le_div_of_nonneg_right hl hnR.le,
    div_le_div_of_nonneg_right hh hnR.le⟩

lemma radialRoot_sub_integrable (n : ℕ) :
    Integrable (fun g : Fin n → ℝ => radialRoot g - 1) (stdGauss (Fin n)) := by
  have hi : Integrable (fun g : Fin n → ℝ => radialRoot g) (stdGauss (Fin n)) := by
    apply (((BstLean.Part149.stdGauss_normSq n).1.div_const n).add
      (integrable_const (1 : ℝ))).mono'
    · exact ((continuous_normSq.div_const _).sqrt).aestronglyMeasurable
    · exact ae_of_all _ fun g => by
        rw [Real.norm_of_nonneg (show 0 ≤ radialRoot g from sqrt_nonneg _)]
        change radialRoot g ≤ normSq g / n + 1
        rw [← radialRoot_sq]
        nlinarith [sq_nonneg (radialRoot g - 1)]
  exact hi.sub (integrable_const _)

/-- The projection weight and the radial fluctuation are not independent. -/
theorem weighted_root_bounds {n : ℕ} (hn : 1 ≤ n)
    {u : Fin n → ℝ} (hu : normSq u = 1) {w : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hw : Measurable w) (hb : ∀ z, 0 ≤ w z ∧ w z ≤ C) :
    -(3 * C / (2 * n)) ≤
      (∫ g, w (g ⬝ᵥ u) * (radialRoot g - 1) ∂stdGauss (Fin n)) ∧
    (∫ g, w (g ⬝ᵥ u) * (radialRoot g - 1) ∂stdGauss (Fin n)) ≤ C / (2 * n) := by
  have hab : ∀ z, |w z| ≤ C := fun z => by rw [abs_of_nonneg (hb z).1]; exact (hb z).2
  have hwm : Measurable (fun g : Fin n → ℝ => w (g ⬝ᵥ u)) :=
    hw.comp (by unfold dotProduct; fun_prop)
  have hiU := bounded_mul_integrable
    (((BstLean.Part149.stdGauss_normSq n).1.div_const n).sub (integrable_const 1))
    hwm (fun g => hab (g ⬝ᵥ u))
  have hiR := bounded_mul_integrable (radialRoot_error hn).1 hwm (fun g => hab (g ⬝ᵥ u))
  have hR : 0 ≤ ∫ g, w (g ⬝ᵥ u) * (radialRoot g - 1) ^ 2 ∂stdGauss (Fin n) :=
    integral_nonneg fun g => mul_nonneg (hb _).1 (sq_nonneg _)
  have hRup : (∫ g, w (g ⬝ᵥ u) * (radialRoot g - 1) ^ 2 ∂stdGauss (Fin n)) ≤
      C * (2 / n) := by
    calc _ ≤ ∫ g, C * (radialRoot g - 1) ^ 2 ∂stdGauss (Fin n) :=
          integral_mono hiR ((radialRoot_error hn).1.const_mul _) fun g =>
            mul_le_mul_of_nonneg_right (hb _).2 (sq_nonneg _)
      _ = C * (∫ g, (radialRoot g - 1) ^ 2 ∂stdGauss (Fin n)) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (radialRoot_error hn).2 hC
  have hEq : 2 * (∫ g, w (g ⬝ᵥ u) * (radialRoot g - 1) ∂stdGauss (Fin n)) =
      (∫ g, w (g ⬝ᵥ u) * (normSq g / n - 1) ∂stdGauss (Fin n)) -
      (∫ g, w (g ⬝ᵥ u) * (radialRoot g - 1) ^ 2 ∂stdGauss (Fin n)) := by
    rw [← integral_const_mul, ← integral_sub
      (f := fun g => w (g ⬝ᵥ u) * (normSq g / n - 1))
      (g := fun g => w (g ⬝ᵥ u) * (radialRoot g - 1) ^ 2) hiU hiR]
    apply integral_congr_ae
    exact ae_of_all _ fun g => by dsimp only; rw [← radialRoot_sq]; ring
  obtain ⟨hl, hh⟩ := weighted_radial_bounds hn hu hC hw hb
  have e1 : 3 * C / (2 * (n : ℝ)) = 3 * (C / n) / 2 := by ring
  have e2 : C / (2 * (n : ℝ)) = (C / n) / 2 := by ring
  have e3 : C * (2 / (n : ℝ)) = 2 * (C / n) := by ring
  rw [e1, e2]
  rw [e3] at hRup
  constructor <;> linarith

end BstLean.Part211
