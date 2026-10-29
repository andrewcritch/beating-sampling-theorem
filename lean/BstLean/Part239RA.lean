import BstLean.Part239Correction
import BstLean.Part213Sharp

/-! The exact location correction stays inside the square root. -/
namespace BstLean.Part239
open MeasureTheory ProbabilityTheory Real
open BstLean.Part213
open BstLean.Part223 (MomentBound)

noncomputable def iidAverage {X : Type*} (m : ℕ) (f : X → ℝ) (y : Fin m → X) : ℝ :=
  (m : ℝ)⁻¹ * ∑ j, f (y j)

lemma momentBound_of_norm {X : Type*} [MeasurableSpace X] {ρ : Measure X}
    {k : ℕ} (hk : k ≠ 0) {f : X → ℝ} {B : ℝ} (hf : Measurable f) (hB : 0 ≤ B)
    (hN : eLpNorm f k ρ ≤ ENNReal.ofReal B) : MomentBound ρ k f B := by
  refine ⟨hf, hB, ?_⟩
  have h := pow_le_pow_left' hN k
  rwa [BstLean.Part153.eLpNorm_nat_pow hk hf.aestronglyMeasurable,
    ← ENNReal.ofReal_pow hB] at h

/-- The energy RA price is the mean plus the exact finite-width correction. -/
theorem energy_RA_exact {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) [IsProbabilityMeasure ρ] {m p : ℕ} (hm : 1 ≤ m) (hp : 1 ≤ p)
    {f : X → ℝ} {B : ℝ} (h0 : ∀ x, 0 ≤ f x) (hf : Integrable f ρ)
    (hi : ∀ k, k ≤ 2 * p → Integrable (fun x => f x ^ k) ρ)
    (hc : ∀ k, k ≤ 2 * p → Integrable (fun x => (f x - ∫ y, f y ∂ρ) ^ k) ρ)
    (hM : MomentBound ρ (2 * p) f B) :
    MomentBound (Measure.pi fun _ : Fin m => ρ) (2 * p) (iidAverage m f)
      ((∫ x, f x ∂ρ) + exactCorrection (2 * p) m * B) := by
  let u := ∫ x, f x ∂ρ
  have hu : 0 ≤ u := integral_nonneg h0
  have hr := mul_nonneg (exactCorrection_nonneg (2 * p) m) hM.nonneg
  have hp0 : 2 * p ≠ 0 := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hz : Measurable (iidAverage m f) :=
    (Finset.measurable_sum _ fun j _ => hM.measurable.comp (measurable_pi_apply j)).const_mul _
  have hC := iid_rows_exact (m := m) ρ hp h0 hf hi hc hM
  have hU : eLpNorm (fun _y : Fin m → X => u) (2 * p : ℕ)
      (Measure.pi fun _ : Fin m => ρ) ≤ ENNReal.ofReal u := by
    apply moment_norm_bound measurable_const hp0 hu
    simp [abs_of_nonneg hu]
  apply momentBound_of_norm hp0 hz (add_nonneg hu hr)
  have he : iidAverage m f = (fun _y : Fin m → X => u) +
      (fun y : Fin m → X => (m : ℝ)⁻¹ * ∑ j, (f (y j) - u)) := by
    funext y
    simp only [iidAverage, Pi.add_apply, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hm0]
    ring
  rw [he]
  calc
    _ ≤ eLpNorm (fun _y : Fin m → X => u) (2 * p : ℕ) (Measure.pi fun _ => ρ) +
        eLpNorm (fun y : Fin m → X => (m : ℝ)⁻¹ * ∑ j, (f (y j) - u))
          (2 * p : ℕ) (Measure.pi fun _ => ρ) :=
      eLpNorm_add_le (by exact_mod_cast (by omega : 1 ≤ 2 * p))
    _ ≤ ENNReal.ofReal u + ENNReal.ofReal (exactCorrection (2 * p) m * B) :=
      add_le_add hU hC
    _ = _ := (ENNReal.ofReal_add hu hr).symm

/-- The location RA price is the root of the mean square plus the exact correction. -/
theorem location_RA_exact {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) [IsProbabilityMeasure ρ] {m p : ℕ} (hm : 1 ≤ m) (hp : 1 ≤ p)
    {β : X → ℝ} {B : ℝ} (hf : Integrable (fun x => β x ^ 2) ρ)
    (hi : ∀ k, k ≤ 2 * p → Integrable (fun x => (β x ^ 2) ^ k) ρ)
    (hc : ∀ k, k ≤ 2 * p → Integrable
      (fun x => (β x ^ 2 - ∫ y, β y ^ 2 ∂ρ) ^ k) ρ)
    (hM : MomentBound ρ (4 * p) β B) :
    MomentBound (Measure.pi fun _ : Fin m => ρ) (4 * p)
      (fun y => sqrt (iidAverage m (fun x => β x ^ 2) y))
      (sqrt ((∫ x, β x ^ 2 ∂ρ) + exactCorrection (2 * p) m * B ^ 2)) := by
  have hsq : MomentBound ρ (2 * p) (fun x => β x ^ 2) (B ^ 2) := by
    rw [show 4 * p = (2 * p) * 2 by omega] at hM
    exact hM.power
  have hA := energy_RA_exact ρ hm hp (fun x => sq_nonneg (β x)) hf hi hc hsq
  have hnonneg : ∀ y, 0 ≤ iidAverage m (fun x => β x ^ 2) y := by
    intro y
    unfold iidAverage
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m))
      (Finset.sum_nonneg fun j _ => sq_nonneg _)
  simpa only [show 2 * (2 * p) = 4 * p by omega] using hA.sqrt hnonneg

#print axioms energy_RA_exact
#print axioms location_RA_exact

/-- A finite highest source moment supplies every integrability premise. -/
theorem source_integrability {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) [IsProbabilityMeasure ρ] {p : ℕ} (hp : 1 ≤ p)
    {f : X → ℝ} {B : ℝ} (h0 : ∀ x, 0 ≤ f x)
    (hM : MomentBound ρ (2 * p) f B) :
    Integrable f ρ ∧
    (∀ k, k ≤ 2 * p → Integrable (fun x => f x ^ k) ρ) ∧
    (∀ k, k ≤ 2 * p → Integrable (fun x => (f x - ∫ y, f y ∂ρ) ^ k) ρ) := by
  have hfinite := hM.moment.trans_lt ENNReal.ofReal_lt_top
  have ia : Integrable (fun x => |f x| ^ (2 * p)) ρ :=
    (lintegral_ofReal_ne_top_iff_integrable (hM.measurable.abs.pow_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => pow_nonneg (abs_nonneg _) _)).mp (ne_of_lt hfinite)
  have ifun : Integrable f ρ := by
    simpa only [pow_one] using lower_power_integrable hM.measurable (by omega : 1 ≤ 2 * p) ia
  have ip : Integrable (fun x => f x ^ (2 * p)) ρ := by
    simpa only [abs_of_nonneg (h0 _)] using ia
  have hreal : ∫ x, f x ^ (2 * p) ∂ρ ≤ B ^ (2 * p) := by
    have hm := hM.moment
    simp only [abs_of_nonneg (h0 _)] at hm
    rw [← ofReal_integral_eq_lintegral_ofReal ip
      (Filter.Eventually.of_forall fun x => pow_nonneg (h0 x) _)] at hm
    exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg hM.nonneg _)).mp hm
  have hcen := nonnegative_centring hM.measurable h0 (by omega : 1 ≤ 2 * p)
    ip hM.nonneg hreal
  have mc : Measurable (fun x => f x - ∫ y, f y ∂ρ) := hM.measurable.sub_const _
  have ic : Integrable (fun x => |f x - ∫ y, f y ∂ρ| ^ (2 * p)) ρ :=
    (lintegral_ofReal_ne_top_iff_integrable (mc.abs.pow_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => pow_nonneg (abs_nonneg _) _)).mp
      (ne_of_lt (hcen.trans_lt ENNReal.ofReal_lt_top))
  exact ⟨ifun, fun k hk => lower_power_integrable hM.measurable hk ia,
    fun k hk => lower_power_integrable mc hk ic⟩

theorem iid_rows_exact_from_top {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) [IsProbabilityMeasure ρ] {m p : ℕ} (hp : 1 ≤ p)
    {f : X → ℝ} {B : ℝ} (h0 : ∀ x, 0 ≤ f x) (hM : MomentBound ρ (2 * p) f B) :
    eLpNorm (fun y : Fin m → X => (m : ℝ)⁻¹ * ∑ j, (f (y j) - ∫ x, f x ∂ρ))
      (2 * p : ℕ) (Measure.pi fun _ : Fin m => ρ) ≤
      ENNReal.ofReal (exactCorrection (2 * p) m * B) := by
  obtain ⟨hf, hi, hc⟩ := source_integrability ρ hp h0 hM
  exact iid_rows_exact ρ hp h0 hf hi hc hM

theorem energy_RA_from_top {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) [IsProbabilityMeasure ρ] {m p : ℕ} (hm : 1 ≤ m) (hp : 1 ≤ p)
    {f : X → ℝ} {B : ℝ} (h0 : ∀ x, 0 ≤ f x) (hM : MomentBound ρ (2 * p) f B) :
    MomentBound (Measure.pi fun _ : Fin m => ρ) (2 * p) (iidAverage m f)
      ((∫ x, f x ∂ρ) + exactCorrection (2 * p) m * B) := by
  obtain ⟨hf, hi, hc⟩ := source_integrability ρ hp h0 hM
  exact energy_RA_exact ρ hm hp h0 hf hi hc hM

theorem location_RA_from_top {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) [IsProbabilityMeasure ρ] {m p : ℕ} (hm : 1 ≤ m) (hp : 1 ≤ p)
    {β : X → ℝ} {B : ℝ} (hM : MomentBound ρ (4 * p) β B) :
    MomentBound (Measure.pi fun _ : Fin m => ρ) (4 * p)
      (fun y => sqrt (iidAverage m (fun x => β x ^ 2) y))
      (sqrt ((∫ x, β x ^ 2 ∂ρ) + exactCorrection (2 * p) m * B ^ 2)) := by
  have hs : MomentBound ρ (2 * p) (fun x => β x ^ 2) (B ^ 2) := by
    rw [show 4 * p = (2 * p) * 2 by omega] at hM
    exact hM.power
  obtain ⟨hf, hi, hc⟩ := source_integrability ρ hp (fun x => sq_nonneg _) hs
  exact location_RA_exact ρ hm hp hf hi hc hM

#print axioms source_integrability
#print axioms iid_rows_exact_from_top
#print axioms energy_RA_from_top
#print axioms location_RA_from_top
end BstLean.Part239
