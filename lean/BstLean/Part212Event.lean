import BstLean.Part166End

/-! A fresh joint latitude event with one conditional Markov payment. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part130 BstLean.Part134 BstLean.Part157
open BstLean.Part166 (certI fK sK)

/-- The residual field in Part166 carries an extra factor `sqrt (2/n)`. -/
noncomputable def latitudeCertZ (n : ℕ) (k : BstLean.Part160.AgFam n) : ℝ≥0∞ :=
  ENNReal.ofReal ((n : ℝ) / 2) ^ (12 : ℕ) * certI sK k

theorem measurable_latitudeCertZ (n : ℕ) : Measurable (latitudeCertZ n) :=
  (BstLean.Part166.measurable_certI BstLean.Part166.measurable_psiK_s).const_mul _

/-- The order-160 power of the order-24 square-root field norm. -/
noncomputable def latitudeScore (n : ℕ) (k : BstLean.Part160.AgFam n) : ℝ≥0∞ :=
  certI fK k ^ ((20 : ℝ) / 3) + latitudeCertZ n k ^ ((20 : ℝ) / 3)

/-- This event uses its own threshold and does not refer to an older event. -/
def latitudeEvent (n : ℕ) (C : ℝ≥0∞) : Set (BstLean.Part160.AgFam n) :=
  {k | latitudeScore n k ≤ C ^ (80 : ℕ)}

theorem measurable_latitudeScore (n : ℕ) : Measurable (latitudeScore n) := by
  exact ((BstLean.Part166.measurable_certI BstLean.Part166.measurable_psiK_f).pow_const _).add
    ((measurable_latitudeCertZ n).pow_const _)

theorem measurableSet_latitudeEvent (n : ℕ) (C : ℝ≥0∞) :
    MeasurableSet (latitudeEvent n C) :=
  measurableSet_le (measurable_latitudeScore n) measurable_const

theorem latitudeEvent_fields {n : ℕ} {C : ℝ≥0∞}
    {k : BstLean.Part160.AgFam n} (hk : k ∈ latitudeEvent n C) :
    certI fK k ≤ C ^ (12 : ℕ) ∧ latitudeCertZ n k ≤ C ^ (12 : ℕ) := by
  have hh : latitudeScore n k ≤ C ^ (80 : ℕ) := hk
  have one (a : ℝ≥0∞) (ha : a ^ ((20 : ℝ) / 3) ≤ C ^ (80 : ℕ)) :
      a ≤ C ^ (12 : ℕ) := by
    have h := ENNReal.rpow_le_rpow ha (by norm_num : (0 : ℝ) ≤ 3 / 20)
    rw [← ENNReal.rpow_mul, show (20 : ℝ) / 3 * (3 / 20) = 1 by norm_num,
      ENNReal.rpow_one, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at h
    norm_num at h
    exact h
  exact ⟨one _ ((le_add_right le_rfl).trans hh),
    one _ ((le_add_left le_rfl).trans hh)⟩

/-- Both fields share one Markov payment. The mixed moment estimate is explicit. -/
theorem latitudeEvent_charge {n : ℕ} (c : Fin n → ℝ) (τ : ℝ)
    {C δ : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hM : ∫⁻ θ, latitudeScore n ((c, τ), θ) ∂BstLean.Part153.nuA n ≤
      δ * C ^ (80 : ℕ)) :
    BstLean.Part153.nuA n {θ | ((c, τ), θ) ∉ latitudeEvent n C} ≤ δ := by
  have hm : Measurable (fun θ => latitudeScore n ((c, τ), θ)) :=
    (measurable_latitudeScore n).comp (measurable_const.prodMk measurable_id)
  have h0 : C ^ (80 : ℕ) ≠ 0 := pow_ne_zero _ hC
  have ht : C ^ (80 : ℕ) ≠ ∞ := ENNReal.pow_ne_top hCt
  have hs : {θ | ((c, τ), θ) ∉ latitudeEvent n C} ⊆
      {θ | C ^ (80 : ℕ) ≤ latitudeScore n ((c, τ), θ)} := by
    intro θ hθ
    change ¬ latitudeScore n ((c, τ), θ) ≤ C ^ (80 : ℕ) at hθ
    exact (lt_of_not_ge hθ).le
  refine (measure_mono hs).trans ((meas_ge_le_lintegral_div hm.aemeasurable h0 ht).trans ?_)
  calc (∫⁻ θ, latitudeScore n ((c, τ), θ) ∂BstLean.Part153.nuA n) / C ^ (80 : ℕ)
      ≤ (δ * C ^ (80 : ℕ)) / C ^ (80 : ℕ) := by gcongr
    _ = δ := ENNReal.mul_div_cancel_right h0 ht

/-- The paper's squared-gradient envelope at order 160. -/
noncomputable def latitudeConstant (K Θ δ : ℝ) : ℝ :=
  (2 / δ) ^ ((1 : ℝ) / 80) * K ^ 2 * Θ

theorem latitudeConstant_pow {K Θ δ : ℝ} (hK : 0 ≤ K) (hΘ : 0 ≤ Θ) (hδ : 0 < δ) :
    latitudeConstant K Θ δ ^ 80 = (2 / δ) * (K ^ 2 * Θ) ^ 80 := by
  unfold latitudeConstant
  rw [mul_pow, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 / δ)]
  norm_num
  ring

/-- Two separate mixed moment supplies give the one joint supply. -/
theorem latitudeScore_moment {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) {B : ℝ≥0∞}
    (hf : ∫⁻ θ, certI fK ((c, τ), θ) ^ ((20 : ℝ) / 3)
      ∂BstLean.Part153.nuA n ≤ B ^ (80 : ℕ))
    (hz : ∫⁻ θ, latitudeCertZ n ((c, τ), θ) ^ ((20 : ℝ) / 3)
      ∂BstLean.Part153.nuA n ≤ B ^ (80 : ℕ)) :
    ∫⁻ θ, latitudeScore n ((c, τ), θ) ∂BstLean.Part153.nuA n ≤
      2 * B ^ (80 : ℕ) := by
  unfold latitudeScore
  rw [lintegral_add_left]
  · simpa only [two_mul] using add_le_add hf hz
  · exact ((BstLean.Part166.measurable_certI BstLean.Part166.measurable_psiK_f).comp
      (measurable_const.prodMk measurable_id)).pow_const _

/-- The fresh event uses the paper threshold and one payment at `delta`. -/
theorem latitudeEvent_from_mixed {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ)
    {K Θ δ : ℝ} (hK : 0 < K) (hΘ : 0 < Θ) (hδ : 0 < δ)
    (hf : ∫⁻ θ, certI fK ((c, τ), θ) ^ ((20 : ℝ) / 3)
      ∂BstLean.Part153.nuA n ≤ ENNReal.ofReal ((K ^ 2 * Θ / n) ^ 80))
    (hz : ∫⁻ θ, latitudeCertZ n ((c, τ), θ) ^ ((20 : ℝ) / 3)
      ∂BstLean.Part153.nuA n ≤ ENNReal.ofReal ((K ^ 2 * Θ / n) ^ 80)) :
    (BstLean.Part153.nuA n).real
      {θ | ((c, τ), θ) ∉ latitudeEvent n (ENNReal.ofReal (latitudeConstant K Θ δ / n))}
      ≤ δ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hC0 : 0 < latitudeConstant K Θ δ / n := by
    unfold latitudeConstant
    positivity
  have hB0 : 0 ≤ K ^ 2 * Θ / n := by positivity
  have hM := latitudeScore_moment c τ
    (B := ENNReal.ofReal (K ^ 2 * Θ / n))
    (by simpa only [ENNReal.ofReal_pow hB0] using hf)
    (by simpa only [ENNReal.ofReal_pow hB0] using hz)
  have he : (δ * (latitudeConstant K Θ δ / n) ^ 80) =
      2 * (K ^ 2 * Θ / n) ^ 80 := by
    rw [div_pow, latitudeConstant_pow hK.le hΘ.le hδ, div_pow]
    field_simp
  have hM' : ∫⁻ θ, latitudeScore n ((c, τ), θ) ∂BstLean.Part153.nuA n ≤
      ENNReal.ofReal δ * ENNReal.ofReal (latitudeConstant K Θ δ / n) ^ (80 : ℕ) := by
    rw [← ENNReal.ofReal_pow hC0.le, ← ENNReal.ofReal_mul hδ.le, he]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num only [ENNReal.ofReal_ofNat]
    simpa only [ENNReal.ofReal_pow hB0] using hM
  have hc := latitudeEvent_charge c τ (C := ENNReal.ofReal (latitudeConstant K Θ δ / n))
    (δ := ENNReal.ofReal δ) (by simp only [ne_eq, ENNReal.ofReal_eq_zero]; exact not_le.mpr hC0)
    ENNReal.ofReal_ne_top hM'
  exact ENNReal.toReal_le_of_le_ofReal hδ.le hc

theorem latitudeEvent_charge_oneTenThousand {n : ℕ} (hn : 1 ≤ n)
    (c : Fin n → ℝ) (τ : ℝ) {K Θ : ℝ} (hK : 0 < K) (hΘ : 0 < Θ)
    (hf : ∫⁻ θ, certI fK ((c, τ), θ) ^ ((20 : ℝ) / 3)
      ∂BstLean.Part153.nuA n ≤ ENNReal.ofReal ((K ^ 2 * Θ / n) ^ 80))
    (hz : ∫⁻ θ, latitudeCertZ n ((c, τ), θ) ^ ((20 : ℝ) / 3)
      ∂BstLean.Part153.nuA n ≤ ENNReal.ofReal ((K ^ 2 * Θ / n) ^ 80)) :
    (BstLean.Part153.nuA n).real {θ | ((c, τ), θ) ∉
      latitudeEvent n (ENNReal.ofReal (latitudeConstant K Θ (1 / 10000) / n))}
      ≤ 1 / 10000 :=
  latitudeEvent_from_mixed hn c τ hK hΘ (by norm_num) hf hz
end BstLean.Part212
