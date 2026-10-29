import BstLean.Part242Integral
import BstLean.Part242Scale
import BstLean.Part241Partition

/-! The SY regular price and the exceptional price share one kept measure. -/
namespace BstLean.Part242
open MeasureTheory Real Set
open BstLean.Part161 (hellG2)
open scoped ENNReal

noncomputable def syPrice (n : ℕ) (χ ε af Γ BS mex : ℝ) : ℝ :=
  (χ * Γ / (2 * (2 - ε)) * af ^ 2 + BS ^ 2 / (8 * (1 - ε))) / n + 2 * mex

theorem SY_price {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {K : Set X} (hK : MeasurableSet K) (hmass : μ univ ≤ 1)
    (n : ℕ) (hn : 0 < n) {Sb St lb lt : X → ℝ}
    (mSb : Measurable Sb) (mSt : Measurable St)
    {γ e χ cA2 ε af Γ BS mex : ℝ}
    (hγ : 0 < γ) (he : 0 < e) (hχ : 0 ≤ χ) (hc0 : 0 ≤ cA2)
    (hc : cA2 ≤ γ * e * n * χ) (hε : ε < 1)
    (hSb : ∀ x ∈ K, 0 < Sb x) (hSt : ∀ x ∈ K, 0 < St x)
    (hF : LBound (μ.restrict K) 8
      (fun x => (n : ℝ) * (sqrt e * (lb x - lt x))) af)
    (hR : LBound (μ.restrict K) 4 (fun x => 1 / (Sb x / γ)) Γ)
    (hS : LBound (μ.restrict K) 2 (fun x => (n : ℝ) * (St x / Sb x - 1)) BS)
    (hmex : μ.real (K ∩ {x | ε < |St x / Sb x - 1|}) ≤ mex) :
    ∫ x in K, hellG2 n ((lb x - lt x) ^ 2 * cA2) (Sb x) (St x) ∂μ ≤
      syPrice n χ ε af Γ BS mex := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h1e : 0 < 1 - ε := by linarith
  have h2e : 0 < 2 - ε := by linarith
  let df : X → ℝ := fun x => (n : ℝ) * (sqrt e * (lb x - lt x))
  let ds : X → ℝ := fun x => (n : ℝ) * (St x / Sb x - 1)
  let Xbad : Set X := {x | ε < |St x / Sb x - 1|}
  have mX : MeasurableSet Xbad :=
    measurableSet_lt measurable_const (((mSt.div mSb).sub_const 1).abs)
  have hμK : (μ.restrict K) univ ≤ 1 := (Measure.restrict_le_self univ).trans hmass
  have hY : ∀ᵐ x ∂μ.restrict K, 0 < Sb x / γ :=
    (ae_restrict_iff' hK).mpr (Filter.Eventually.of_forall fun x hx => div_pos (hSb x hx) hγ)
  obtain ⟨iF, bF⟩ := SY_location_integral hμK hF hR hY
  obtain ⟨iS, bS⟩ := hS.squareIntegral
  let reg : X → ℝ := fun x =>
    χ / (2 * (2 - ε) * n) * (df x ^ 2 / (Sb x / γ)) +
      1 / (8 * (1 - ε) * n) * ds x ^ 2
  have ireg : IntegrableOn reg K μ :=
    (iF.const_mul _).add (iS.const_mul _)
  have iex : IntegrableOn (Xbad.indicator (fun _ => (2 : ℝ))) K μ :=
    (integrable_const (2 : ℝ)).indicator mX |>.integrableOn
  have hpt : ∀ x ∈ K, hellG2 n ((lb x - lt x) ^ 2 * cA2) (Sb x) (St x) ≤
      reg x + Xbad.indicator (fun _ => 2) x := by
    intro x hx
    have hSbp : 0 < Sb x := hSb x hx
    have hreg : 0 ≤ reg x := by
      dsimp [reg]; have hy := hSb x hx; positivity
    by_cases hb : x ∈ Xbad
    · rw [indicator_of_mem hb]
      linarith [BstLean.Part161.hellG2_le_two n ((lb x - lt x) ^ 2 * cA2) (Sb x) (St x)]
    · rw [indicator_of_notMem hb, add_zero]
      have hp := BstLean.Part169.hell_price_pt n (hSb x hx) (hSt x hx)
        (mul_nonneg (sq_nonneg (lb x - lt x)) hc0) (le_of_not_gt hb) hε
      have hl : (lb x - lt x) ^ 2 * cA2 / (2 * Sb x * (2 - ε)) ≤
          χ / (2 * (2 - ε) * n) * (df x ^ 2 / (Sb x / γ)) := by
        calc
          _ ≤ (lb x - lt x) ^ 2 * (γ * e * n * χ) / (2 * Sb x * (2 - ε)) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hc (sq_nonneg _)) (by positivity)
          _ = _ := by
            dsimp [df]
            rw [mul_pow, mul_pow, sq_sqrt he.le]
            field_simp <;> ring
      have hscale : (n : ℝ) * (St x / Sb x - 1) ^ 2 / (8 * (1 - ε)) =
          1 / (8 * (1 - ε) * n) * ds x ^ 2 := by dsimp [ds]; field_simp <;> ring
      dsimp [reg]
      rw [hscale] at hp
      linarith
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x =>
      BstLean.Part161.hellG2_nonneg n (mul_nonneg (sq_nonneg _) hc0) _ _)
    (ireg.add iex)
    ((ae_restrict_iff' hK).mpr (Filter.Eventually.of_forall hpt))
  have hInt : ∫ x in K, reg x ∂μ ≤
      (χ * Γ / (2 * (2 - ε)) * af ^ 2 + BS ^ 2 / (8 * (1 - ε))) / n := by
    dsimp [reg]
    rw [integral_add (iF.const_mul _) (iS.const_mul _), integral_const_mul, integral_const_mul]
    have hF' := mul_le_mul_of_nonneg_left bF
      (show 0 ≤ χ / (2 * (2 - ε) * n) by positivity)
    have hS' := mul_le_mul_of_nonneg_left bS
      (show 0 ≤ 1 / (8 * (1 - ε) * n) by positivity)
    refine (add_le_add hF' hS').trans_eq ?_
    field_simp <;> ring
  have hEx : ∫ x in K, Xbad.indicator (fun _ => (2 : ℝ)) x ∂μ ≤ 2 * mex := by
    rw [integral_indicator mX, integral_const, smul_eq_mul,
      Measure.restrict_restrict mX, inter_comm, measureReal_restrict_apply_univ]
    exact (mul_le_mul_of_nonneg_right hmex (by norm_num)).trans_eq (by ring)
  simp only [Pi.add_apply] at hmono
  rw [integral_add ireg iex] at hmono
  exact hmono.trans (add_le_add hInt hEx)

end BstLean.Part242
